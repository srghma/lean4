// Lean compiler output
// Module: Lean.Elab.Tactic.Omega.OmegaM
// Imports: Lean.Meta.AppBuilder Lean.Meta.Canonicalizer Init.Omega
use crate::r#gen::Init::Data::Int::Basic::{
    l_Int_add___boxed, l_Int_mul___boxed, l_Int_pow, l_Int_sub___boxed, l_Int_toNat,
};
use crate::r#gen::Init::Data::Int::DivMod::Basic::l_Int_ediv___boxed;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Nat_add___boxed, l_Nat_div___boxed, l_Nat_mul___boxed, l_Nat_pow___boxed,
    l_Nat_sub___boxed,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_getAppFnArgs,
    l_Lean_Expr_hash, l_Lean_Expr_int_x3f, l_Lean_Expr_nat_x3f, l_Lean_mkApp3, l_Lean_mkApp4,
    l_Lean_mkApp5, l_Lean_mkAppB, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofList, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkDecideProof, l_Lean_Meta_mkEq,
    l_Lean_Meta_mkEqRefl, l_Lean_Meta_mkExpectedPropHint, l_Lean_Meta_mkListLit,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Canonicalizer::{
    initialize_Lean_Meta_Canonicalizer, l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg,
    l_Lean_Meta_Canonicalizer_canon, runtime_initialize_Lean_Meta_Canonicalizer,
};
use crate::r#gen::Lean::ToExpr::l_Lean_instToExprInt_mkNat;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_le, lean_int_neg, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_string_dec_eq,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [73, 110, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value:
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
    m_data: [79, 109, 101, 103, 97, 0],
};
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2_value:
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
    m_data: [67, 111, 101, 102, 102, 115, 0],
};
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3_value:
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
    m_data: [111, 102, 76, 105, 115, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        17910073349994400881 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        10725639862586182856 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        11430621368878064144 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [99, 97, 115, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0_value:
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
    m_data: [72, 65, 100, 100, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1_value:
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
    m_data: [72, 77, 117, 108, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2_value:
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
    m_data: [72, 83, 117, 98, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3_value:
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
    m_data: [72, 68, 105, 118, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4_value:
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
    m_data: [72, 80, 111, 119, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5_value:
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
    m_data: [104, 80, 111, 119, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6_value:
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
    m_fun: l_Nat_pow___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7_value:
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
    m_data: [104, 68, 105, 118, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8_value:
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
    m_fun: l_Nat_div___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9_value:
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
    m_data: [104, 83, 117, 98, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10_value:
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
    m_fun: l_Nat_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11_value:
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
    m_data: [104, 77, 117, 108, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12_value:
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
    m_fun: l_Nat_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13_value:
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
    m_data: [104, 65, 100, 100, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14_value:
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
    m_fun: l_Nat_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0_value:
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
    m_fun: l_Int_ediv___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1_value:
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
    m_fun: l_Int_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2_value:
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
    m_fun: l_Int_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3_value:
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
    m_fun: l_Int_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0_value:
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
    m_data: [72, 77, 111, 100, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [77, 105, 110, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [77, 97, 120, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [109, 97, 120, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [108, 101, 95, 109, 97, 120, 95, 108, 101, 102, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        8528684718952576202 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [108, 101, 95, 109, 97, 120, 95, 114, 105, 103, 104, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        4653461862122275003 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [109, 105, 110, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [109, 105, 110, 95, 108, 101, 95, 108, 101, 102, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        15037249822398505490 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [109, 105, 110, 95, 108, 101, 95, 114, 105, 103, 104, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14_value)
            as *mut crate::leanh::LeanObject,
        970802058389122393 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17_value:
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
    m_data: [104, 77, 111, 100, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        101, 109, 111, 100, 95, 111, 102, 78, 97, 116, 95, 110, 111, 110, 110, 101, 103, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        17910073349994400881 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        488667332567600511 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18_value)
            as *mut crate::leanh::LeanObject,
        10638584452205461697 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [76, 84, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [108, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value)
            as *mut crate::leanh::LeanObject,
        17878876274162330439 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value)
            as *mut crate::leanh::LeanObject,
        11833570877100518198 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25_value:
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
    m_data: [105, 110, 115, 116, 76, 84, 78, 97, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25_value)
            as *mut crate::leanh::LeanObject,
        14651840373392481165 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28_value:
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
    m_data: [112, 111, 119, 95, 112, 111, 115, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28_value)
            as *mut crate::leanh::LeanObject,
        14111604343637326856 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value:
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
        111, 102, 78, 97, 116, 95, 112, 111, 115, 95, 111, 102, 95, 112, 111, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        17910073349994400881 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        488667332567600511 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value)
            as *mut crate::leanh::LeanObject,
        13216564244333251368 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [101, 109, 111, 100, 95, 110, 111, 110, 110, 101, 103, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value)
            as *mut crate::leanh::LeanObject,
        17157738005422892093 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value:
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
    m_data: [110, 101, 95, 111, 102, 95, 103, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value)
            as *mut crate::leanh::LeanObject,
        11675868500096275836 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        101, 109, 111, 100, 95, 108, 116, 95, 111, 102, 95, 112, 111, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value)
            as *mut crate::leanh::LeanObject,
        15154550989551304115 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39: u8 = 0;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 101, 103, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 101, 103, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value)
            as *mut crate::leanh::LeanObject,
        9626815015619986526 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value)
            as *mut crate::leanh::LeanObject,
        17185717442815859305 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43_value:
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
    m_data: [105, 110, 115, 116, 78, 101, 103, 73, 110, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43_value)
            as *mut crate::leanh::LeanObject,
        6362876895233142233 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value:
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
    m_data: [105, 110, 115, 116, 76, 84, 73, 110, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value)
            as *mut crate::leanh::LeanObject,
        9121383836933346478 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        112, 111, 115, 95, 112, 111, 119, 95, 111, 102, 95, 112, 111, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        17910073349994400881 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        488667332567600511 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_value)
            as *mut crate::leanh::LeanObject,
        8404793396275648913 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [78, 101, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value)
            as *mut crate::leanh::LeanObject,
        6695605208187598753 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value:
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
        109, 117, 108, 95, 101, 100, 105, 118, 95, 115, 101, 108, 102, 95, 108, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value)
            as *mut crate::leanh::LeanObject,
        15464796390623215100 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 116, 95, 109, 117, 108, 95, 101, 100, 105, 118, 95, 115, 101, 108, 102, 95, 97, 100,
        100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value)
            as *mut crate::leanh::LeanObject,
        17601256755593845854 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value:
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
        110, 101, 103, 95, 108, 101, 95, 110, 97, 116, 65, 98, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        17910073349994400881 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        488667332567600511 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value)
            as *mut crate::leanh::LeanObject,
        13309385938308562393 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        110, 97, 116, 67, 97, 115, 116, 95, 110, 111, 110, 110, 101, 103, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value)
            as *mut crate::leanh::LeanObject,
        17750334692303158606 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value:
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
    m_data: [66, 105, 116, 86, 101, 99, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value:
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
    m_data: [105, 115, 76, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value)
            as *mut crate::leanh::LeanObject,
        5394957827732845164 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value)
            as *mut crate::leanh::LeanObject,
        8436147975023434436 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [70, 105, 110, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82_value)
            as *mut crate::leanh::LeanObject,
        15815496672699636542 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value)
            as *mut crate::leanh::LeanObject,
        4938441192065111774 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value:
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
    m_data: [108, 101, 95, 110, 97, 116, 65, 98, 115, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value)
            as *mut crate::leanh::LeanObject,
        6348096724845679194 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86_value:
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
    m_data: [116, 111, 78, 97, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [118, 97, 108, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88_value:
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
    m_data: [110, 97, 116, 65, 98, 115, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        111, 102, 78, 97, 116, 95, 115, 117, 98, 95, 100, 105, 99, 104, 111, 116, 111, 109, 121, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        17910073349994400881 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        488667332567600511 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89_value)
            as *mut crate::leanh::LeanObject,
        4345411359602094212 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 116, 101, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92_value:
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
        105, 116, 101, 95, 100, 105, 115, 106, 117, 110, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        17910073349994400881 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92_value)
            as *mut crate::leanh::LeanObject,
        7682406714577881933 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0:
    f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [111, 109, 101, 103, 97, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11366375744198450027 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__2_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__2_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__5_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [78, 101, 119, 32, 102, 97, 99, 116, 115, 58, 32, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__7_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [78, 101, 119, 32, 97, 116, 111, 109, 58, 32, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(
    mut v___x_2347_: *mut crate::leanh::LeanObject,
    mut v___x_2348_: *mut crate::leanh::LeanObject,
    mut v_m_2349_: *mut crate::leanh::LeanObject,
    mut v_cfg_2350_: *mut crate::leanh::LeanObject,
    mut v___y_2351_: u8,
    mut v___y_2352_: *mut crate::leanh::LeanObject,
    mut v___y_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
    mut v___y_2356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2365_: u8 = 0;
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2358_ = lean_st_mk_ref(v___x_2347_);
                v___x_2359_ = lean_st_mk_ref(v___x_2348_);
                v___x_2360_ = crate::leanh::lean_box((v___y_2351_) as usize);
                crate::leanh::lean_inc(v___y_2356_);
                crate::leanh::lean_inc_ref(v___y_2355_);
                crate::leanh::lean_inc(v___y_2354_);
                crate::leanh::lean_inc_ref(v___y_2353_);
                crate::leanh::lean_inc(v___y_2352_);
                crate::leanh::lean_inc(v___x_2358_);
                crate::leanh::lean_inc(v___x_2359_);
                v___x_2361_ = crate::leanh::lean_apply_10(
                    v_m_2349_,
                    v___x_2359_,
                    v___x_2358_,
                    v_cfg_2350_,
                    v___x_2360_,
                    v___y_2352_,
                    v___y_2353_,
                    v___y_2354_,
                    v___y_2355_,
                    v___y_2356_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2361_) == 0 {
                    v_a_2362_ = crate::leanh::lean_ctor_get(v___x_2361_, 0);
                    v_isSharedCheck_2371_ = (!crate::leanh::lean_is_exclusive(v___x_2361_)) as u8;
                    if v_isSharedCheck_2371_ == 0 {
                        v___x_2364_ = v___x_2361_;
                        v_isShared_2365_ = v_isSharedCheck_2371_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2362_);
                        crate::leanh::lean_dec(v___x_2361_);
                        v___x_2364_ = crate::leanh::lean_box(0);
                        v_isShared_2365_ = v_isSharedCheck_2371_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2359_);
                    crate::leanh::lean_dec(v___x_2358_);
                    return v___x_2361_;
                }
            }
            1 => {
                v___x_2366_ = lean_st_ref_get(v___x_2359_);
                crate::leanh::lean_dec(v___x_2359_);
                crate::leanh::lean_dec(v___x_2366_);
                v___x_2367_ = lean_st_ref_get(v___x_2358_);
                crate::leanh::lean_dec(v___x_2358_);
                crate::leanh::lean_dec(v___x_2367_);
                if v_isShared_2365_ == 0 {
                    v___x_2369_ = v___x_2364_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2370_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2362_);
                    v___x_2369_ = v_reuseFailAlloc_2370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed(
    mut v___x_2372_: *mut crate::leanh::LeanObject,
    mut v___x_2373_: *mut crate::leanh::LeanObject,
    mut v_m_2374_: *mut crate::leanh::LeanObject,
    mut v_cfg_2375_: *mut crate::leanh::LeanObject,
    mut v___y_2376_: *mut crate::leanh::LeanObject,
    mut v___y_2377_: *mut crate::leanh::LeanObject,
    mut v___y_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4823__boxed_2383_: u8 = 0;
    let mut v_res_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_4823__boxed_2383_ = (crate::leanh::lean_unbox(v___y_2376_) as u8);
    v_res_2384_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(
        v___x_2372_,
        v___x_2373_,
        v_m_2374_,
        v_cfg_2375_,
        v___y_4823__boxed_2383_,
        v___y_2377_,
        v___y_2378_,
        v___y_2379_,
        v___y_2380_,
        v___y_2381_,
    );
    crate::leanh::lean_dec(v___y_2381_);
    crate::leanh::lean_dec_ref(v___y_2380_);
    crate::leanh::lean_dec(v___y_2379_);
    crate::leanh::lean_dec_ref(v___y_2378_);
    crate::leanh::lean_dec(v___y_2377_);
    return v_res_2384_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2385_ = crate::leanh::lean_box(0);
    v___x_2386_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2387_ = lean_mk_array(v___x_2386_, v___x_2385_);
    return v___x_2387_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2388_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0_once),
        _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0,
    );
    v___x_2389_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2390_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2390_, 0, v___x_2389_);
    crate::leanh::lean_ctor_set(v___x_2390_, 1, v___x_2388_);
    return v___x_2390_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2391_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once),
        _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1,
    );
    v___x_2392_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2392_, 0, v___x_2391_);
    crate::leanh::lean_ctor_set(v___x_2392_, 1, v___x_2391_);
    return v___x_2392_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(
    mut v_m_2393_: *mut crate::leanh::LeanObject,
    mut v_cfg_2394_: *mut crate::leanh::LeanObject,
    mut v_a_2395_: *mut crate::leanh::LeanObject,
    mut v_a_2396_: *mut crate::leanh::LeanObject,
    mut v_a_2397_: *mut crate::leanh::LeanObject,
    mut v_a_2398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: u8 = 0;
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2400_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once),
        _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1,
    );
    v___f_2401_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed as *mut core::ffi::c_void,
        11,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2401_, 0, v___x_2400_);
    crate::leanh::lean_closure_set(v___f_2401_, 1, v___x_2400_);
    crate::leanh::lean_closure_set(v___f_2401_, 2, v_m_2393_);
    crate::leanh::lean_closure_set(v___f_2401_, 3, v_cfg_2394_);
    v___x_2402_ = 3;
    v___x_2403_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2_once),
        _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2,
    );
    v___x_2404_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(
        v___f_2401_,
        v___x_2402_,
        v___x_2403_,
        v_a_2395_,
        v_a_2396_,
        v_a_2397_,
        v_a_2398_,
    );
    return v___x_2404_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___boxed(
    mut v_m_2405_: *mut crate::leanh::LeanObject,
    mut v_cfg_2406_: *mut crate::leanh::LeanObject,
    mut v_a_2407_: *mut crate::leanh::LeanObject,
    mut v_a_2408_: *mut crate::leanh::LeanObject,
    mut v_a_2409_: *mut crate::leanh::LeanObject,
    mut v_a_2410_: *mut crate::leanh::LeanObject,
    mut v_a_2411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2412_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(
        v_m_2405_,
        v_cfg_2406_,
        v_a_2407_,
        v_a_2408_,
        v_a_2409_,
        v_a_2410_,
    );
    crate::leanh::lean_dec(v_a_2410_);
    crate::leanh::lean_dec_ref(v_a_2409_);
    crate::leanh::lean_dec(v_a_2408_);
    crate::leanh::lean_dec_ref(v_a_2407_);
    return v_res_2412_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run(
    mut v_00_u03b1_2413_: *mut crate::leanh::LeanObject,
    mut v_m_2414_: *mut crate::leanh::LeanObject,
    mut v_cfg_2415_: *mut crate::leanh::LeanObject,
    mut v_a_2416_: *mut crate::leanh::LeanObject,
    mut v_a_2417_: *mut crate::leanh::LeanObject,
    mut v_a_2418_: *mut crate::leanh::LeanObject,
    mut v_a_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2421_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(
        v_m_2414_,
        v_cfg_2415_,
        v_a_2416_,
        v_a_2417_,
        v_a_2418_,
        v_a_2419_,
    );
    return v___x_2421_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run___boxed(
    mut v_00_u03b1_2422_: *mut crate::leanh::LeanObject,
    mut v_m_2423_: *mut crate::leanh::LeanObject,
    mut v_cfg_2424_: *mut crate::leanh::LeanObject,
    mut v_a_2425_: *mut crate::leanh::LeanObject,
    mut v_a_2426_: *mut crate::leanh::LeanObject,
    mut v_a_2427_: *mut crate::leanh::LeanObject,
    mut v_a_2428_: *mut crate::leanh::LeanObject,
    mut v_a_2429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2430_ = l_Lean_Elab_Tactic_Omega_OmegaM_run(
        v_00_u03b1_2422_,
        v_m_2423_,
        v_cfg_2424_,
        v_a_2425_,
        v_a_2426_,
        v_a_2427_,
        v_a_2428_,
    );
    crate::leanh::lean_dec(v_a_2428_);
    crate::leanh::lean_dec_ref(v_a_2427_);
    crate::leanh::lean_dec(v_a_2426_);
    crate::leanh::lean_dec_ref(v_a_2425_);
    return v_res_2430_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_cfg___redArg(
    mut v_a_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_2431_);
    v___x_2433_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2433_, 0, v_a_2431_);
    return v___x_2433_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_cfg___redArg___boxed(
    mut v_a_2434_: *mut crate::leanh::LeanObject,
    mut v_a_2435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2436_ = l_Lean_Elab_Tactic_Omega_cfg___redArg(v_a_2434_);
    crate::leanh::lean_dec_ref(v_a_2434_);
    return v_res_2436_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_cfg(
    mut v_a_2437_: *mut crate::leanh::LeanObject,
    mut v_a_2438_: *mut crate::leanh::LeanObject,
    mut v_a_2439_: *mut crate::leanh::LeanObject,
    mut v_a_2440_: u8,
    mut v_a_2441_: *mut crate::leanh::LeanObject,
    mut v_a_2442_: *mut crate::leanh::LeanObject,
    mut v_a_2443_: *mut crate::leanh::LeanObject,
    mut v_a_2444_: *mut crate::leanh::LeanObject,
    mut v_a_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_2439_);
    v___x_2447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2447_, 0, v_a_2439_);
    return v___x_2447_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_cfg___boxed(
    mut v_a_2448_: *mut crate::leanh::LeanObject,
    mut v_a_2449_: *mut crate::leanh::LeanObject,
    mut v_a_2450_: *mut crate::leanh::LeanObject,
    mut v_a_2451_: *mut crate::leanh::LeanObject,
    mut v_a_2452_: *mut crate::leanh::LeanObject,
    mut v_a_2453_: *mut crate::leanh::LeanObject,
    mut v_a_2454_: *mut crate::leanh::LeanObject,
    mut v_a_2455_: *mut crate::leanh::LeanObject,
    mut v_a_2456_: *mut crate::leanh::LeanObject,
    mut v_a_2457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2458_: u8 = 0;
    let mut v_res_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2458_ = (crate::leanh::lean_unbox(v_a_2451_) as u8);
    v_res_2459_ = l_Lean_Elab_Tactic_Omega_cfg(
        v_a_2448_,
        v_a_2449_,
        v_a_2450_,
        v_a_boxed_2458_,
        v_a_2452_,
        v_a_2453_,
        v_a_2454_,
        v_a_2455_,
        v_a_2456_,
    );
    crate::leanh::lean_dec(v_a_2456_);
    crate::leanh::lean_dec_ref(v_a_2455_);
    crate::leanh::lean_dec(v_a_2454_);
    crate::leanh::lean_dec_ref(v_a_2453_);
    crate::leanh::lean_dec(v_a_2452_);
    crate::leanh::lean_dec_ref(v_a_2450_);
    crate::leanh::lean_dec(v_a_2449_);
    crate::leanh::lean_dec(v_a_2448_);
    return v_res_2459_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(
    mut v_hi_2460_: *mut crate::leanh::LeanObject,
    mut v_pivot_2461_: *mut crate::leanh::LeanObject,
    mut v_as_2462_: *mut crate::leanh::LeanObject,
    mut v_i_2463_: *mut crate::leanh::LeanObject,
    mut v_k_2464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2465_: u8 = 0;
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: u8 = 0;
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2465_ = lean_nat_dec_lt(v_k_2464_, v_hi_2460_);
                if v___x_2465_ == 0 {
                    crate::leanh::lean_dec(v_k_2464_);
                    v___x_2466_ = lean_array_fswap(v_as_2462_, v_i_2463_, v_hi_2460_);
                    v___x_2467_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2467_, 0, v_i_2463_);
                    crate::leanh::lean_ctor_set(v___x_2467_, 1, v___x_2466_);
                    return v___x_2467_;
                } else {
                    v___x_2468_ = lean_array_fget_borrowed(v_as_2462_, v_k_2464_);
                    v_snd_2469_ = crate::leanh::lean_ctor_get(v___x_2468_, 1);
                    v_snd_2470_ = crate::leanh::lean_ctor_get(v_pivot_2461_, 1);
                    v___x_2471_ = lean_nat_dec_lt(v_snd_2469_, v_snd_2470_);
                    if v___x_2471_ == 0 {
                        v___x_2472_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2473_ = lean_nat_add(v_k_2464_, v___x_2472_);
                        crate::leanh::lean_dec(v_k_2464_);
                        v_k_2464_ = v___x_2473_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2475_ = lean_array_fswap(v_as_2462_, v_i_2463_, v_k_2464_);
                        v___x_2476_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2477_ = lean_nat_add(v_i_2463_, v___x_2476_);
                        crate::leanh::lean_dec(v_i_2463_);
                        v___x_2478_ = lean_nat_add(v_k_2464_, v___x_2476_);
                        crate::leanh::lean_dec(v_k_2464_);
                        v_as_2462_ = v___x_2475_;
                        v_i_2463_ = v___x_2477_;
                        v_k_2464_ = v___x_2478_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg___boxed(
    mut v_hi_2480_: *mut crate::leanh::LeanObject,
    mut v_pivot_2481_: *mut crate::leanh::LeanObject,
    mut v_as_2482_: *mut crate::leanh::LeanObject,
    mut v_i_2483_: *mut crate::leanh::LeanObject,
    mut v_k_2484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2485_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_2480_, v_pivot_2481_, v_as_2482_, v_i_2483_, v_k_2484_);
    crate::leanh::lean_dec_ref(v_pivot_2481_);
    crate::leanh::lean_dec(v_hi_2480_);
    return v_res_2485_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(
    mut v_x1_2486_: *mut crate::leanh::LeanObject,
    mut v_x2_2487_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_snd_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: u8 = 0;
    v_snd_2488_ = crate::leanh::lean_ctor_get(v_x1_2486_, 1);
    v_snd_2489_ = crate::leanh::lean_ctor_get(v_x2_2487_, 1);
    v___x_2490_ = lean_nat_dec_lt(v_snd_2488_, v_snd_2489_);
    return v___x_2490_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed(
    mut v_x1_2491_: *mut crate::leanh::LeanObject,
    mut v_x2_2492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2493_: u8 = 0;
    let mut v_r_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2493_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v_x1_2491_, v_x2_2492_);
    crate::leanh::lean_dec_ref(v_x2_2492_);
    crate::leanh::lean_dec_ref(v_x1_2491_);
    v_r_2494_ = crate::leanh::lean_box((v_res_2493_) as usize);
    return v_r_2494_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(
    mut v_n_2495_: *mut crate::leanh::LeanObject,
    mut v_as_2496_: *mut crate::leanh::LeanObject,
    mut v_lo_2497_: *mut crate::leanh::LeanObject,
    mut v_hi_2498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: u8 = 0;
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: u8 = 0;
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: u8 = 0;
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: u8 = 0;
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: u8 = 0;
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2510_ = lean_nat_dec_lt(v_lo_2497_, v_hi_2498_);
                if v___x_2510_ == 0 {
                    crate::leanh::lean_dec(v_lo_2497_);
                    return v_as_2496_;
                } else {
                    v___x_2511_ = lean_nat_add(v_lo_2497_, v_hi_2498_);
                    v___x_2512_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_2513_ = lean_nat_shiftr(v___x_2511_, v___x_2512_);
                    crate::leanh::lean_dec(v___x_2511_);
                    v___x_2526_ = lean_array_fget_borrowed(v_as_2496_, v_mid_2513_);
                    v___x_2527_ = lean_array_fget_borrowed(v_as_2496_, v_lo_2497_);
                    v___x_2528_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v___x_2526_, v___x_2527_);
                    if v___x_2528_ == 0 {
                        v___y_2521_ = v_as_2496_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2529_ = lean_array_fswap(v_as_2496_, v_lo_2497_, v_mid_2513_);
                        v___y_2521_ = v___x_2529_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2501_ = lean_array_fget(v___y_2500_, v_hi_2498_);
                crate::leanh::lean_inc_n(v_lo_2497_, 2);
                v___x_2502_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_2498_, v_pivot_2501_, v___y_2500_, v_lo_2497_, v_lo_2497_);
                crate::leanh::lean_dec(v_pivot_2501_);
                v_fst_2503_ = crate::leanh::lean_ctor_get(v___x_2502_, 0);
                crate::leanh::lean_inc(v_fst_2503_);
                v_snd_2504_ = crate::leanh::lean_ctor_get(v___x_2502_, 1);
                crate::leanh::lean_inc(v_snd_2504_);
                crate::leanh::lean_dec_ref(v___x_2502_);
                v___x_2505_ = lean_nat_dec_le(v_hi_2498_, v_fst_2503_);
                if v___x_2505_ == 0 {
                    v___x_2506_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_2495_, v_snd_2504_, v_lo_2497_, v_fst_2503_);
                    v___x_2507_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2508_ = lean_nat_add(v_fst_2503_, v___x_2507_);
                    crate::leanh::lean_dec(v_fst_2503_);
                    v_as_2496_ = v___x_2506_;
                    v_lo_2497_ = v___x_2508_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_2503_);
                    crate::leanh::lean_dec(v_lo_2497_);
                    return v_snd_2504_;
                }
            }
            2 => {
                v___x_2516_ = lean_array_fget_borrowed(v___y_2515_, v_mid_2513_);
                v___x_2517_ = lean_array_fget_borrowed(v___y_2515_, v_hi_2498_);
                v___x_2518_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v___x_2516_, v___x_2517_);
                if v___x_2518_ == 0 {
                    crate::leanh::lean_dec(v_mid_2513_);
                    v___y_2500_ = v___y_2515_;
                    state = 1;
                    continue;
                } else {
                    v___x_2519_ = lean_array_fswap(v___y_2515_, v_mid_2513_, v_hi_2498_);
                    crate::leanh::lean_dec(v_mid_2513_);
                    v___y_2500_ = v___x_2519_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2522_ = lean_array_fget_borrowed(v___y_2521_, v_hi_2498_);
                v___x_2523_ = lean_array_fget_borrowed(v___y_2521_, v_lo_2497_);
                v___x_2524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v___x_2522_, v___x_2523_);
                if v___x_2524_ == 0 {
                    v___y_2515_ = v___y_2521_;
                    state = 2;
                    continue;
                } else {
                    v___x_2525_ = lean_array_fswap(v___y_2521_, v_lo_2497_, v_hi_2498_);
                    v___y_2515_ = v___x_2525_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___boxed(
    mut v_n_2530_: *mut crate::leanh::LeanObject,
    mut v_as_2531_: *mut crate::leanh::LeanObject,
    mut v_lo_2532_: *mut crate::leanh::LeanObject,
    mut v_hi_2533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_2530_, v_as_2531_, v_lo_2532_, v_hi_2533_);
    crate::leanh::lean_dec(v_hi_2533_);
    crate::leanh::lean_dec(v_n_2530_);
    return v_res_2534_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(
    mut v_x_2535_: *mut crate::leanh::LeanObject,
    mut v_x_2536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2536_) == 0 {
                    return v_x_2535_;
                } else {
                    v_key_2537_ = crate::leanh::lean_ctor_get(v_x_2536_, 0);
                    v_value_2538_ = crate::leanh::lean_ctor_get(v_x_2536_, 1);
                    v_tail_2539_ = crate::leanh::lean_ctor_get(v_x_2536_, 2);
                    crate::leanh::lean_inc(v_value_2538_);
                    crate::leanh::lean_inc(v_key_2537_);
                    v___x_2540_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2540_, 0, v_key_2537_);
                    crate::leanh::lean_ctor_set(v___x_2540_, 1, v_value_2538_);
                    v___x_2541_ = lean_array_push(v_x_2535_, v___x_2540_);
                    v_x_2535_ = v___x_2541_;
                    v_x_2536_ = v_tail_2539_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___boxed(
    mut v_x_2543_: *mut crate::leanh::LeanObject,
    mut v_x_2544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2545_ =
        l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(
            v_x_2543_, v_x_2544_,
        );
    crate::leanh::lean_dec(v_x_2544_);
    return v_res_2545_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(
    mut v_as_2546_: *mut crate::leanh::LeanObject,
    mut v_i_2547_: usize,
    mut v_stop_2548_: usize,
    mut v_b_2549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2550_: u8 = 0;
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: usize = 0;
    let mut v___x_2554_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2550_ = lean_usize_dec_eq(v_i_2547_, v_stop_2548_);
                if v___x_2550_ == 0 {
                    v___x_2551_ = lean_array_uget_borrowed(v_as_2546_, v_i_2547_);
                    v___x_2552_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(v_b_2549_, v___x_2551_);
                    v___x_2553_ = 1usize;
                    v___x_2554_ = lean_usize_add(v_i_2547_, v___x_2553_);
                    v_i_2547_ = v___x_2554_;
                    v_b_2549_ = v___x_2552_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2549_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3___boxed(
    mut v_as_2556_: *mut crate::leanh::LeanObject,
    mut v_i_2557_: *mut crate::leanh::LeanObject,
    mut v_stop_2558_: *mut crate::leanh::LeanObject,
    mut v_b_2559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2560_: usize = 0;
    let mut v_stop_boxed_2561_: usize = 0;
    let mut v_res_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2560_ = crate::leanh::lean_unbox_usize(v_i_2557_);
    crate::leanh::lean_dec(v_i_2557_);
    v_stop_boxed_2561_ = crate::leanh::lean_unbox_usize(v_stop_2558_);
    crate::leanh::lean_dec(v_stop_2558_);
    v_res_2562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_as_2556_, v_i_boxed_2560_, v_stop_boxed_2561_, v_b_2559_);
    crate::leanh::lean_dec_ref(v_as_2556_);
    return v_res_2562_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(
    mut v_sz_2563_: usize,
    mut v_i_2564_: usize,
    mut v_bs_2565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2566_: u8 = 0;
    let mut v_v_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: usize = 0;
    let mut v___x_2572_: usize = 0;
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2566_ = lean_usize_dec_lt(v_i_2564_, v_sz_2563_);
                if v___x_2566_ == 0 {
                    return v_bs_2565_;
                } else {
                    v_v_2567_ = lean_array_uget_borrowed(v_bs_2565_, v_i_2564_);
                    v_fst_2568_ = crate::leanh::lean_ctor_get(v_v_2567_, 0);
                    crate::leanh::lean_inc(v_fst_2568_);
                    v___x_2569_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2570_ = lean_array_uset(v_bs_2565_, v_i_2564_, v___x_2569_);
                    v___x_2571_ = 1usize;
                    v___x_2572_ = lean_usize_add(v_i_2564_, v___x_2571_);
                    v___x_2573_ = lean_array_uset(v_bs_x27_2570_, v_i_2564_, v_fst_2568_);
                    v_i_2564_ = v___x_2572_;
                    v_bs_2565_ = v___x_2573_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0___boxed(
    mut v_sz_2575_: *mut crate::leanh::LeanObject,
    mut v_i_2576_: *mut crate::leanh::LeanObject,
    mut v_bs_2577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2578_: usize = 0;
    let mut v_i_boxed_2579_: usize = 0;
    let mut v_res_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2578_ = crate::leanh::lean_unbox_usize(v_sz_2575_);
    crate::leanh::lean_dec(v_sz_2575_);
    v_i_boxed_2579_ = crate::leanh::lean_unbox_usize(v_i_2576_);
    crate::leanh::lean_dec(v_i_2576_);
    v_res_2580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(v_sz_boxed_2578_, v_i_boxed_2579_, v_bs_2577_);
    return v_res_2580_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atoms___redArg(
    mut v_a_2581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2586_: usize = 0;
    let mut v___x_2587_: usize = 0;
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: u8 = 0;
    let mut v___y_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: u8 = 0;
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: u8 = 0;
    let mut v_size_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u8 = 0;
    let mut v___x_2616_: u8 = 0;
    let mut v___x_2617_: usize = 0;
    let mut v___x_2618_: usize = 0;
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: usize = 0;
    let mut v___x_2621_: usize = 0;
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2583_ = lean_st_ref_get(v_a_2581_);
                v_size_2610_ = crate::leanh::lean_ctor_get(v___x_2583_, 0);
                crate::leanh::lean_inc(v_size_2610_);
                v_buckets_2611_ = crate::leanh::lean_ctor_get(v___x_2583_, 1);
                crate::leanh::lean_inc_ref(v_buckets_2611_);
                crate::leanh::lean_dec(v___x_2583_);
                v___x_2612_ = lean_mk_empty_array_with_capacity(v_size_2610_);
                crate::leanh::lean_dec(v_size_2610_);
                v___x_2613_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2614_ = lean_array_get_size(v_buckets_2611_);
                v___x_2615_ = lean_nat_dec_lt(v___x_2613_, v___x_2614_);
                if v___x_2615_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_2611_);
                    v___y_2603_ = v___x_2612_;
                    state = 4;
                    continue;
                } else {
                    v___x_2616_ = lean_nat_dec_le(v___x_2614_, v___x_2614_);
                    if v___x_2616_ == 0 {
                        if v___x_2615_ == 0 {
                            crate::leanh::lean_dec_ref(v_buckets_2611_);
                            v___y_2603_ = v___x_2612_;
                            state = 4;
                            continue;
                        } else {
                            v___x_2617_ = 0usize;
                            v___x_2618_ = lean_usize_of_nat(v___x_2614_);
                            v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_buckets_2611_, v___x_2617_, v___x_2618_, v___x_2612_);
                            crate::leanh::lean_dec_ref(v_buckets_2611_);
                            v___y_2603_ = v___x_2619_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_2620_ = 0usize;
                        v___x_2621_ = lean_usize_of_nat(v___x_2614_);
                        v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_buckets_2611_, v___x_2620_, v___x_2621_, v___x_2612_);
                        crate::leanh::lean_dec_ref(v_buckets_2611_);
                        v___y_2603_ = v___x_2622_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_2586_ = lean_array_size(v___y_2585_);
                v___x_2587_ = 0usize;
                v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(v_sz_2586_, v___x_2587_, v___y_2585_);
                v___x_2589_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2589_, 0, v___x_2588_);
                return v___x_2589_;
            }
            2 => {
                v___x_2595_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v___y_2593_, v___y_2591_, v___y_2592_, v___y_2594_);
                crate::leanh::lean_dec(v___y_2594_);
                crate::leanh::lean_dec(v___y_2593_);
                v___y_2585_ = v___x_2595_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2601_ = lean_nat_dec_le(v___y_2600_, v___y_2598_);
                if v___x_2601_ == 0 {
                    crate::leanh::lean_dec(v___y_2598_);
                    crate::leanh::lean_inc(v___y_2600_);
                    v___y_2591_ = v___y_2597_;
                    v___y_2592_ = v___y_2600_;
                    v___y_2593_ = v___y_2599_;
                    v___y_2594_ = v___y_2600_;
                    state = 2;
                    continue;
                } else {
                    v___y_2591_ = v___y_2597_;
                    v___y_2592_ = v___y_2600_;
                    v___y_2593_ = v___y_2599_;
                    v___y_2594_ = v___y_2598_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_2604_ = lean_array_get_size(v___y_2603_);
                v___x_2605_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2606_ = lean_nat_dec_eq(v___x_2604_, v___x_2605_);
                if v___x_2606_ == 0 {
                    v___x_2607_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2608_ = lean_nat_sub(v___x_2604_, v___x_2607_);
                    v___x_2609_ = lean_nat_dec_le(v___x_2605_, v___x_2608_);
                    if v___x_2609_ == 0 {
                        crate::leanh::lean_inc(v___x_2608_);
                        v___y_2597_ = v___y_2603_;
                        v___y_2598_ = v___x_2608_;
                        v___y_2599_ = v___x_2604_;
                        v___y_2600_ = v___x_2608_;
                        state = 3;
                        continue;
                    } else {
                        v___y_2597_ = v___y_2603_;
                        v___y_2598_ = v___x_2608_;
                        v___y_2599_ = v___x_2604_;
                        v___y_2600_ = v___x_2605_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_2585_ = v___y_2603_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atoms___redArg___boxed(
    mut v_a_2623_: *mut crate::leanh::LeanObject,
    mut v_a_2624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2625_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_2623_);
    crate::leanh::lean_dec(v_a_2623_);
    return v_res_2625_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atoms(
    mut v_a_2626_: *mut crate::leanh::LeanObject,
    mut v_a_2627_: *mut crate::leanh::LeanObject,
    mut v_a_2628_: *mut crate::leanh::LeanObject,
    mut v_a_2629_: u8,
    mut v_a_2630_: *mut crate::leanh::LeanObject,
    mut v_a_2631_: *mut crate::leanh::LeanObject,
    mut v_a_2632_: *mut crate::leanh::LeanObject,
    mut v_a_2633_: *mut crate::leanh::LeanObject,
    mut v_a_2634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2636_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_2627_);
    return v___x_2636_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atoms___boxed(
    mut v_a_2637_: *mut crate::leanh::LeanObject,
    mut v_a_2638_: *mut crate::leanh::LeanObject,
    mut v_a_2639_: *mut crate::leanh::LeanObject,
    mut v_a_2640_: *mut crate::leanh::LeanObject,
    mut v_a_2641_: *mut crate::leanh::LeanObject,
    mut v_a_2642_: *mut crate::leanh::LeanObject,
    mut v_a_2643_: *mut crate::leanh::LeanObject,
    mut v_a_2644_: *mut crate::leanh::LeanObject,
    mut v_a_2645_: *mut crate::leanh::LeanObject,
    mut v_a_2646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2647_: u8 = 0;
    let mut v_res_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2647_ = (crate::leanh::lean_unbox(v_a_2640_) as u8);
    v_res_2648_ = l_Lean_Elab_Tactic_Omega_atoms(
        v_a_2637_,
        v_a_2638_,
        v_a_2639_,
        v_a_boxed_2647_,
        v_a_2641_,
        v_a_2642_,
        v_a_2643_,
        v_a_2644_,
        v_a_2645_,
    );
    crate::leanh::lean_dec(v_a_2645_);
    crate::leanh::lean_dec_ref(v_a_2644_);
    crate::leanh::lean_dec(v_a_2643_);
    crate::leanh::lean_dec_ref(v_a_2642_);
    crate::leanh::lean_dec(v_a_2641_);
    crate::leanh::lean_dec_ref(v_a_2639_);
    crate::leanh::lean_dec(v_a_2638_);
    crate::leanh::lean_dec(v_a_2637_);
    return v_res_2648_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(
    mut v_n_2649_: *mut crate::leanh::LeanObject,
    mut v_as_2650_: *mut crate::leanh::LeanObject,
    mut v_lo_2651_: *mut crate::leanh::LeanObject,
    mut v_hi_2652_: *mut crate::leanh::LeanObject,
    mut v_w_2653_: *mut crate::leanh::LeanObject,
    mut v_hlo_2654_: *mut crate::leanh::LeanObject,
    mut v_hhi_2655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2656_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_2649_, v_as_2650_, v_lo_2651_, v_hi_2652_);
    return v___x_2656_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(
    mut v_n_2657_: *mut crate::leanh::LeanObject,
    mut v_as_2658_: *mut crate::leanh::LeanObject,
    mut v_lo_2659_: *mut crate::leanh::LeanObject,
    mut v_hi_2660_: *mut crate::leanh::LeanObject,
    mut v_w_2661_: *mut crate::leanh::LeanObject,
    mut v_hlo_2662_: *mut crate::leanh::LeanObject,
    mut v_hhi_2663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2664_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(v_n_2657_, v_as_2658_, v_lo_2659_, v_hi_2660_, v_w_2661_, v_hlo_2662_, v_hhi_2663_);
    crate::leanh::lean_dec(v_hi_2660_);
    crate::leanh::lean_dec(v_n_2657_);
    return v_res_2664_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(
    mut v_n_2665_: *mut crate::leanh::LeanObject,
    mut v_lo_2666_: *mut crate::leanh::LeanObject,
    mut v_hi_2667_: *mut crate::leanh::LeanObject,
    mut v_hhi_2668_: *mut crate::leanh::LeanObject,
    mut v_pivot_2669_: *mut crate::leanh::LeanObject,
    mut v_as_2670_: *mut crate::leanh::LeanObject,
    mut v_i_2671_: *mut crate::leanh::LeanObject,
    mut v_k_2672_: *mut crate::leanh::LeanObject,
    mut v_ilo_2673_: *mut crate::leanh::LeanObject,
    mut v_ik_2674_: *mut crate::leanh::LeanObject,
    mut v_w_2675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2676_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_2667_, v_pivot_2669_, v_as_2670_, v_i_2671_, v_k_2672_);
    return v___x_2676_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___boxed(
    mut v_n_2677_: *mut crate::leanh::LeanObject,
    mut v_lo_2678_: *mut crate::leanh::LeanObject,
    mut v_hi_2679_: *mut crate::leanh::LeanObject,
    mut v_hhi_2680_: *mut crate::leanh::LeanObject,
    mut v_pivot_2681_: *mut crate::leanh::LeanObject,
    mut v_as_2682_: *mut crate::leanh::LeanObject,
    mut v_i_2683_: *mut crate::leanh::LeanObject,
    mut v_k_2684_: *mut crate::leanh::LeanObject,
    mut v_ilo_2685_: *mut crate::leanh::LeanObject,
    mut v_ik_2686_: *mut crate::leanh::LeanObject,
    mut v_w_2687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2688_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(v_n_2677_, v_lo_2678_, v_hi_2679_, v_hhi_2680_, v_pivot_2681_, v_as_2682_, v_i_2683_, v_k_2684_, v_ilo_2685_, v_ik_2686_, v_w_2687_);
    crate::leanh::lean_dec_ref(v_pivot_2681_);
    crate::leanh::lean_dec(v_hi_2679_);
    crate::leanh::lean_dec(v_lo_2678_);
    crate::leanh::lean_dec(v_n_2677_);
    return v_res_2688_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2692_ = crate::leanh::lean_box(0);
    v___x_2693_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1;
    v___x_2694_ = l_Lean_Expr_const___override(v___x_2693_, v___x_2692_);
    return v___x_2694_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsList___redArg(
    mut v_a_2695_: *mut crate::leanh::LeanObject,
    mut v_a_2696_: *mut crate::leanh::LeanObject,
    mut v_a_2697_: *mut crate::leanh::LeanObject,
    mut v_a_2698_: *mut crate::leanh::LeanObject,
    mut v_a_2699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2701_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_2695_);
    v_a_2702_ = crate::leanh::lean_ctor_get(v___x_2701_, 0);
    crate::leanh::lean_inc(v_a_2702_);
    crate::leanh::lean_dec_ref(v___x_2701_);
    v___x_2703_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once),
        _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2,
    );
    v___x_2704_ = lean_array_to_list(v_a_2702_);
    v___x_2705_ = l_Lean_Meta_mkListLit(
        v___x_2703_,
        v___x_2704_,
        v_a_2696_,
        v_a_2697_,
        v_a_2698_,
        v_a_2699_,
    );
    return v___x_2705_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsList___redArg___boxed(
    mut v_a_2706_: *mut crate::leanh::LeanObject,
    mut v_a_2707_: *mut crate::leanh::LeanObject,
    mut v_a_2708_: *mut crate::leanh::LeanObject,
    mut v_a_2709_: *mut crate::leanh::LeanObject,
    mut v_a_2710_: *mut crate::leanh::LeanObject,
    mut v_a_2711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2712_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(
        v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_,
    );
    crate::leanh::lean_dec(v_a_2710_);
    crate::leanh::lean_dec_ref(v_a_2709_);
    crate::leanh::lean_dec(v_a_2708_);
    crate::leanh::lean_dec_ref(v_a_2707_);
    crate::leanh::lean_dec(v_a_2706_);
    return v_res_2712_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsList(
    mut v_a_2713_: *mut crate::leanh::LeanObject,
    mut v_a_2714_: *mut crate::leanh::LeanObject,
    mut v_a_2715_: *mut crate::leanh::LeanObject,
    mut v_a_2716_: u8,
    mut v_a_2717_: *mut crate::leanh::LeanObject,
    mut v_a_2718_: *mut crate::leanh::LeanObject,
    mut v_a_2719_: *mut crate::leanh::LeanObject,
    mut v_a_2720_: *mut crate::leanh::LeanObject,
    mut v_a_2721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2723_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(
        v_a_2714_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_,
    );
    return v___x_2723_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsList___boxed(
    mut v_a_2724_: *mut crate::leanh::LeanObject,
    mut v_a_2725_: *mut crate::leanh::LeanObject,
    mut v_a_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
    mut v_a_2728_: *mut crate::leanh::LeanObject,
    mut v_a_2729_: *mut crate::leanh::LeanObject,
    mut v_a_2730_: *mut crate::leanh::LeanObject,
    mut v_a_2731_: *mut crate::leanh::LeanObject,
    mut v_a_2732_: *mut crate::leanh::LeanObject,
    mut v_a_2733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2734_: u8 = 0;
    let mut v_res_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2734_ = (crate::leanh::lean_unbox(v_a_2727_) as u8);
    v_res_2735_ = l_Lean_Elab_Tactic_Omega_atomsList(
        v_a_2724_,
        v_a_2725_,
        v_a_2726_,
        v_a_boxed_2734_,
        v_a_2728_,
        v_a_2729_,
        v_a_2730_,
        v_a_2731_,
        v_a_2732_,
    );
    crate::leanh::lean_dec(v_a_2732_);
    crate::leanh::lean_dec_ref(v_a_2731_);
    crate::leanh::lean_dec(v_a_2730_);
    crate::leanh::lean_dec_ref(v_a_2729_);
    crate::leanh::lean_dec(v_a_2728_);
    crate::leanh::lean_dec_ref(v_a_2726_);
    crate::leanh::lean_dec(v_a_2725_);
    crate::leanh::lean_dec(v_a_2724_);
    return v_res_2735_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2745_ = crate::leanh::lean_box(0);
    v___x_2746_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4;
    v___x_2747_ = l_Lean_Expr_const___override(v___x_2746_, v___x_2745_);
    return v___x_2747_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(
    mut v_a_2748_: *mut crate::leanh::LeanObject,
    mut v_a_2749_: *mut crate::leanh::LeanObject,
    mut v_a_2750_: *mut crate::leanh::LeanObject,
    mut v_a_2751_: *mut crate::leanh::LeanObject,
    mut v_a_2752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2764_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2754_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(
                    v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_,
                );
                if crate::leanh::lean_obj_tag(v___x_2754_) == 0 {
                    v_a_2755_ = crate::leanh::lean_ctor_get(v___x_2754_, 0);
                    v_isSharedCheck_2764_ = (!crate::leanh::lean_is_exclusive(v___x_2754_)) as u8;
                    if v_isSharedCheck_2764_ == 0 {
                        v___x_2757_ = v___x_2754_;
                        v_isShared_2758_ = v_isSharedCheck_2764_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2755_);
                        crate::leanh::lean_dec(v___x_2754_);
                        v___x_2757_ = crate::leanh::lean_box(0);
                        v_isShared_2758_ = v_isSharedCheck_2764_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2754_;
                }
            }
            1 => {
                v___x_2759_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5,
                );
                v___x_2760_ = l_Lean_Expr_app___override(v___x_2759_, v_a_2755_);
                if v_isShared_2758_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2757_, 0, v___x_2760_);
                    v___x_2762_ = v___x_2757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2763_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
                    v___x_2762_ = v_reuseFailAlloc_2763_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2762_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___boxed(
    mut v_a_2765_: *mut crate::leanh::LeanObject,
    mut v_a_2766_: *mut crate::leanh::LeanObject,
    mut v_a_2767_: *mut crate::leanh::LeanObject,
    mut v_a_2768_: *mut crate::leanh::LeanObject,
    mut v_a_2769_: *mut crate::leanh::LeanObject,
    mut v_a_2770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2771_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(
        v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_,
    );
    crate::leanh::lean_dec(v_a_2769_);
    crate::leanh::lean_dec_ref(v_a_2768_);
    crate::leanh::lean_dec(v_a_2767_);
    crate::leanh::lean_dec_ref(v_a_2766_);
    crate::leanh::lean_dec(v_a_2765_);
    return v_res_2771_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsCoeffs(
    mut v_a_2772_: *mut crate::leanh::LeanObject,
    mut v_a_2773_: *mut crate::leanh::LeanObject,
    mut v_a_2774_: *mut crate::leanh::LeanObject,
    mut v_a_2775_: u8,
    mut v_a_2776_: *mut crate::leanh::LeanObject,
    mut v_a_2777_: *mut crate::leanh::LeanObject,
    mut v_a_2778_: *mut crate::leanh::LeanObject,
    mut v_a_2779_: *mut crate::leanh::LeanObject,
    mut v_a_2780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2782_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(
        v_a_2773_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_,
    );
    return v___x_2782_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(
    mut v_a_2783_: *mut crate::leanh::LeanObject,
    mut v_a_2784_: *mut crate::leanh::LeanObject,
    mut v_a_2785_: *mut crate::leanh::LeanObject,
    mut v_a_2786_: *mut crate::leanh::LeanObject,
    mut v_a_2787_: *mut crate::leanh::LeanObject,
    mut v_a_2788_: *mut crate::leanh::LeanObject,
    mut v_a_2789_: *mut crate::leanh::LeanObject,
    mut v_a_2790_: *mut crate::leanh::LeanObject,
    mut v_a_2791_: *mut crate::leanh::LeanObject,
    mut v_a_2792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2793_: u8 = 0;
    let mut v_res_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2793_ = (crate::leanh::lean_unbox(v_a_2786_) as u8);
    v_res_2794_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs(
        v_a_2783_,
        v_a_2784_,
        v_a_2785_,
        v_a_boxed_2793_,
        v_a_2787_,
        v_a_2788_,
        v_a_2789_,
        v_a_2790_,
        v_a_2791_,
    );
    crate::leanh::lean_dec(v_a_2791_);
    crate::leanh::lean_dec_ref(v_a_2790_);
    crate::leanh::lean_dec(v_a_2789_);
    crate::leanh::lean_dec_ref(v_a_2788_);
    crate::leanh::lean_dec(v_a_2787_);
    crate::leanh::lean_dec_ref(v_a_2785_);
    crate::leanh::lean_dec(v_a_2784_);
    crate::leanh::lean_dec(v_a_2783_);
    return v_res_2794_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_commitWhen___redArg(
    mut v_t_2795_: *mut crate::leanh::LeanObject,
    mut v_a_2796_: *mut crate::leanh::LeanObject,
    mut v_a_2797_: *mut crate::leanh::LeanObject,
    mut v_a_2798_: *mut crate::leanh::LeanObject,
    mut v_a_2799_: u8,
    mut v_a_2800_: *mut crate::leanh::LeanObject,
    mut v_a_2801_: *mut crate::leanh::LeanObject,
    mut v_a_2802_: *mut crate::leanh::LeanObject,
    mut v_a_2803_: *mut crate::leanh::LeanObject,
    mut v_a_2804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v_snd_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    let mut v_fst_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2828_: u8 = 0;
    let mut v_a_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2832_: u8 = 0;
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2806_ = lean_st_ref_get(v_a_2797_);
                v___x_2807_ = lean_st_ref_get(v_a_2796_);
                v___x_2808_ = crate::leanh::lean_box((v_a_2799_) as usize);
                crate::leanh::lean_inc(v_a_2804_);
                crate::leanh::lean_inc_ref(v_a_2803_);
                crate::leanh::lean_inc(v_a_2802_);
                crate::leanh::lean_inc_ref(v_a_2801_);
                crate::leanh::lean_inc(v_a_2800_);
                crate::leanh::lean_inc_ref(v_a_2798_);
                crate::leanh::lean_inc(v_a_2797_);
                crate::leanh::lean_inc(v_a_2796_);
                v___x_2809_ = crate::leanh::lean_apply_10(
                    v_t_2795_,
                    v_a_2796_,
                    v_a_2797_,
                    v_a_2798_,
                    v___x_2808_,
                    v_a_2800_,
                    v_a_2801_,
                    v_a_2802_,
                    v_a_2803_,
                    v_a_2804_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2809_) == 0 {
                    v_a_2810_ = crate::leanh::lean_ctor_get(v___x_2809_, 0);
                    v_isSharedCheck_2828_ = (!crate::leanh::lean_is_exclusive(v___x_2809_)) as u8;
                    if v_isSharedCheck_2828_ == 0 {
                        v___x_2812_ = v___x_2809_;
                        v_isShared_2813_ = v_isSharedCheck_2828_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2810_);
                        crate::leanh::lean_dec(v___x_2809_);
                        v___x_2812_ = crate::leanh::lean_box(0);
                        v_isShared_2813_ = v_isSharedCheck_2828_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2807_);
                    crate::leanh::lean_dec(v___x_2806_);
                    v_a_2829_ = crate::leanh::lean_ctor_get(v___x_2809_, 0);
                    v_isSharedCheck_2836_ = (!crate::leanh::lean_is_exclusive(v___x_2809_)) as u8;
                    if v_isSharedCheck_2836_ == 0 {
                        v___x_2831_ = v___x_2809_;
                        v_isShared_2832_ = v_isSharedCheck_2836_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2829_);
                        crate::leanh::lean_dec(v___x_2809_);
                        v___x_2831_ = crate::leanh::lean_box(0);
                        v_isShared_2832_ = v_isSharedCheck_2836_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2814_ = crate::leanh::lean_ctor_get(v_a_2810_, 1);
                v___x_2815_ = (crate::leanh::lean_unbox(v_snd_2814_) as u8);
                if v___x_2815_ == 0 {
                    v_fst_2816_ = crate::leanh::lean_ctor_get(v_a_2810_, 0);
                    crate::leanh::lean_inc(v_fst_2816_);
                    crate::leanh::lean_dec(v_a_2810_);
                    v___x_2817_ = lean_st_ref_take(v_a_2797_);
                    crate::leanh::lean_dec(v___x_2817_);
                    v___x_2818_ = lean_st_ref_set(v_a_2797_, v___x_2806_);
                    v___x_2819_ = lean_st_ref_take(v_a_2796_);
                    crate::leanh::lean_dec(v___x_2819_);
                    v___x_2820_ = lean_st_ref_set(v_a_2796_, v___x_2807_);
                    if v_isShared_2813_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2812_, 0, v_fst_2816_);
                        v___x_2822_ = v___x_2812_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2823_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_fst_2816_);
                        v___x_2822_ = v_reuseFailAlloc_2823_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2807_);
                    crate::leanh::lean_dec(v___x_2806_);
                    v_fst_2824_ = crate::leanh::lean_ctor_get(v_a_2810_, 0);
                    crate::leanh::lean_inc(v_fst_2824_);
                    crate::leanh::lean_dec(v_a_2810_);
                    if v_isShared_2813_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2812_, 0, v_fst_2824_);
                        v___x_2826_ = v___x_2812_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2827_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_fst_2824_);
                        v___x_2826_ = v_reuseFailAlloc_2827_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2822_;
            }
            3 => {
                return v___x_2826_;
            }
            4 => {
                if v_isShared_2832_ == 0 {
                    v___x_2834_ = v___x_2831_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2835_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
                    v___x_2834_ = v_reuseFailAlloc_2835_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_commitWhen___redArg___boxed(
    mut v_t_2837_: *mut crate::leanh::LeanObject,
    mut v_a_2838_: *mut crate::leanh::LeanObject,
    mut v_a_2839_: *mut crate::leanh::LeanObject,
    mut v_a_2840_: *mut crate::leanh::LeanObject,
    mut v_a_2841_: *mut crate::leanh::LeanObject,
    mut v_a_2842_: *mut crate::leanh::LeanObject,
    mut v_a_2843_: *mut crate::leanh::LeanObject,
    mut v_a_2844_: *mut crate::leanh::LeanObject,
    mut v_a_2845_: *mut crate::leanh::LeanObject,
    mut v_a_2846_: *mut crate::leanh::LeanObject,
    mut v_a_2847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2848_: u8 = 0;
    let mut v_res_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2848_ = (crate::leanh::lean_unbox(v_a_2841_) as u8);
    v_res_2849_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(
        v_t_2837_,
        v_a_2838_,
        v_a_2839_,
        v_a_2840_,
        v_a_boxed_2848_,
        v_a_2842_,
        v_a_2843_,
        v_a_2844_,
        v_a_2845_,
        v_a_2846_,
    );
    crate::leanh::lean_dec(v_a_2846_);
    crate::leanh::lean_dec_ref(v_a_2845_);
    crate::leanh::lean_dec(v_a_2844_);
    crate::leanh::lean_dec_ref(v_a_2843_);
    crate::leanh::lean_dec(v_a_2842_);
    crate::leanh::lean_dec_ref(v_a_2840_);
    crate::leanh::lean_dec(v_a_2839_);
    crate::leanh::lean_dec(v_a_2838_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_commitWhen(
    mut v_00_u03b1_2850_: *mut crate::leanh::LeanObject,
    mut v_t_2851_: *mut crate::leanh::LeanObject,
    mut v_a_2852_: *mut crate::leanh::LeanObject,
    mut v_a_2853_: *mut crate::leanh::LeanObject,
    mut v_a_2854_: *mut crate::leanh::LeanObject,
    mut v_a_2855_: u8,
    mut v_a_2856_: *mut crate::leanh::LeanObject,
    mut v_a_2857_: *mut crate::leanh::LeanObject,
    mut v_a_2858_: *mut crate::leanh::LeanObject,
    mut v_a_2859_: *mut crate::leanh::LeanObject,
    mut v_a_2860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2862_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(
        v_t_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_,
        v_a_2859_, v_a_2860_,
    );
    return v___x_2862_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_commitWhen___boxed(
    mut v_00_u03b1_2863_: *mut crate::leanh::LeanObject,
    mut v_t_2864_: *mut crate::leanh::LeanObject,
    mut v_a_2865_: *mut crate::leanh::LeanObject,
    mut v_a_2866_: *mut crate::leanh::LeanObject,
    mut v_a_2867_: *mut crate::leanh::LeanObject,
    mut v_a_2868_: *mut crate::leanh::LeanObject,
    mut v_a_2869_: *mut crate::leanh::LeanObject,
    mut v_a_2870_: *mut crate::leanh::LeanObject,
    mut v_a_2871_: *mut crate::leanh::LeanObject,
    mut v_a_2872_: *mut crate::leanh::LeanObject,
    mut v_a_2873_: *mut crate::leanh::LeanObject,
    mut v_a_2874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2875_: u8 = 0;
    let mut v_res_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2875_ = (crate::leanh::lean_unbox(v_a_2868_) as u8);
    v_res_2876_ = l_Lean_Elab_Tactic_Omega_commitWhen(
        v_00_u03b1_2863_,
        v_t_2864_,
        v_a_2865_,
        v_a_2866_,
        v_a_2867_,
        v_a_boxed_2875_,
        v_a_2869_,
        v_a_2870_,
        v_a_2871_,
        v_a_2872_,
        v_a_2873_,
    );
    crate::leanh::lean_dec(v_a_2873_);
    crate::leanh::lean_dec_ref(v_a_2872_);
    crate::leanh::lean_dec(v_a_2871_);
    crate::leanh::lean_dec_ref(v_a_2870_);
    crate::leanh::lean_dec(v_a_2869_);
    crate::leanh::lean_dec_ref(v_a_2867_);
    crate::leanh::lean_dec(v_a_2866_);
    crate::leanh::lean_dec(v_a_2865_);
    return v_res_2876_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(
    mut v_t_2877_: *mut crate::leanh::LeanObject,
    mut v___y_2878_: *mut crate::leanh::LeanObject,
    mut v___y_2879_: *mut crate::leanh::LeanObject,
    mut v___y_2880_: *mut crate::leanh::LeanObject,
    mut v___y_2881_: u8,
    mut v___y_2882_: *mut crate::leanh::LeanObject,
    mut v___y_2883_: *mut crate::leanh::LeanObject,
    mut v___y_2884_: *mut crate::leanh::LeanObject,
    mut v___y_2885_: *mut crate::leanh::LeanObject,
    mut v___y_2886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2893_: u8 = 0;
    let mut v___x_2894_: u8 = 0;
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2900_: u8 = 0;
    let mut v_a_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2904_: u8 = 0;
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2888_ = crate::leanh::lean_box((v___y_2881_) as usize);
                crate::leanh::lean_inc(v___y_2886_);
                crate::leanh::lean_inc_ref(v___y_2885_);
                crate::leanh::lean_inc(v___y_2884_);
                crate::leanh::lean_inc_ref(v___y_2883_);
                crate::leanh::lean_inc(v___y_2882_);
                crate::leanh::lean_inc_ref(v___y_2880_);
                crate::leanh::lean_inc(v___y_2879_);
                crate::leanh::lean_inc(v___y_2878_);
                v___x_2889_ = crate::leanh::lean_apply_10(
                    v_t_2877_,
                    v___y_2878_,
                    v___y_2879_,
                    v___y_2880_,
                    v___x_2888_,
                    v___y_2882_,
                    v___y_2883_,
                    v___y_2884_,
                    v___y_2885_,
                    v___y_2886_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2889_) == 0 {
                    v_a_2890_ = crate::leanh::lean_ctor_get(v___x_2889_, 0);
                    v_isSharedCheck_2900_ = (!crate::leanh::lean_is_exclusive(v___x_2889_)) as u8;
                    if v_isSharedCheck_2900_ == 0 {
                        v___x_2892_ = v___x_2889_;
                        v_isShared_2893_ = v_isSharedCheck_2900_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2890_);
                        crate::leanh::lean_dec(v___x_2889_);
                        v___x_2892_ = crate::leanh::lean_box(0);
                        v_isShared_2893_ = v_isSharedCheck_2900_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2901_ = crate::leanh::lean_ctor_get(v___x_2889_, 0);
                    v_isSharedCheck_2908_ = (!crate::leanh::lean_is_exclusive(v___x_2889_)) as u8;
                    if v_isSharedCheck_2908_ == 0 {
                        v___x_2903_ = v___x_2889_;
                        v_isShared_2904_ = v_isSharedCheck_2908_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2901_);
                        crate::leanh::lean_dec(v___x_2889_);
                        v___x_2903_ = crate::leanh::lean_box(0);
                        v_isShared_2904_ = v_isSharedCheck_2908_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2894_ = 0;
                v___x_2895_ = crate::leanh::lean_box((v___x_2894_) as usize);
                v___x_2896_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2896_, 0, v_a_2890_);
                crate::leanh::lean_ctor_set(v___x_2896_, 1, v___x_2895_);
                if v_isShared_2893_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2892_, 0, v___x_2896_);
                    v___x_2898_ = v___x_2892_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2899_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
                    v___x_2898_ = v_reuseFailAlloc_2899_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2898_;
            }
            3 => {
                if v_isShared_2904_ == 0 {
                    v___x_2906_ = v___x_2903_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2907_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
                    v___x_2906_ = v_reuseFailAlloc_2907_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed(
    mut v_t_2909_: *mut crate::leanh::LeanObject,
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
    let mut v___y_657__boxed_2920_: u8 = 0;
    let mut v_res_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_657__boxed_2920_ = (crate::leanh::lean_unbox(v___y_2913_) as u8);
    v_res_2921_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(
        v_t_2909_,
        v___y_2910_,
        v___y_2911_,
        v___y_2912_,
        v___y_657__boxed_2920_,
        v___y_2914_,
        v___y_2915_,
        v___y_2916_,
        v___y_2917_,
        v___y_2918_,
    );
    crate::leanh::lean_dec(v___y_2918_);
    crate::leanh::lean_dec_ref(v___y_2917_);
    crate::leanh::lean_dec(v___y_2916_);
    crate::leanh::lean_dec_ref(v___y_2915_);
    crate::leanh::lean_dec(v___y_2914_);
    crate::leanh::lean_dec_ref(v___y_2912_);
    crate::leanh::lean_dec(v___y_2911_);
    crate::leanh::lean_dec(v___y_2910_);
    return v_res_2921_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(
    mut v_t_2922_: *mut crate::leanh::LeanObject,
    mut v_a_2923_: *mut crate::leanh::LeanObject,
    mut v_a_2924_: *mut crate::leanh::LeanObject,
    mut v_a_2925_: *mut crate::leanh::LeanObject,
    mut v_a_2926_: u8,
    mut v_a_2927_: *mut crate::leanh::LeanObject,
    mut v_a_2928_: *mut crate::leanh::LeanObject,
    mut v_a_2929_: *mut crate::leanh::LeanObject,
    mut v_a_2930_: *mut crate::leanh::LeanObject,
    mut v_a_2931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2933_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        11,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2933_, 0, v_t_2922_);
    v___x_2934_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(
        v___f_2933_,
        v_a_2923_,
        v_a_2924_,
        v_a_2925_,
        v_a_2926_,
        v_a_2927_,
        v_a_2928_,
        v_a_2929_,
        v_a_2930_,
        v_a_2931_,
    );
    return v___x_2934_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___boxed(
    mut v_t_2935_: *mut crate::leanh::LeanObject,
    mut v_a_2936_: *mut crate::leanh::LeanObject,
    mut v_a_2937_: *mut crate::leanh::LeanObject,
    mut v_a_2938_: *mut crate::leanh::LeanObject,
    mut v_a_2939_: *mut crate::leanh::LeanObject,
    mut v_a_2940_: *mut crate::leanh::LeanObject,
    mut v_a_2941_: *mut crate::leanh::LeanObject,
    mut v_a_2942_: *mut crate::leanh::LeanObject,
    mut v_a_2943_: *mut crate::leanh::LeanObject,
    mut v_a_2944_: *mut crate::leanh::LeanObject,
    mut v_a_2945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2946_: u8 = 0;
    let mut v_res_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2946_ = (crate::leanh::lean_unbox(v_a_2939_) as u8);
    v_res_2947_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(
        v_t_2935_,
        v_a_2936_,
        v_a_2937_,
        v_a_2938_,
        v_a_boxed_2946_,
        v_a_2940_,
        v_a_2941_,
        v_a_2942_,
        v_a_2943_,
        v_a_2944_,
    );
    crate::leanh::lean_dec(v_a_2944_);
    crate::leanh::lean_dec_ref(v_a_2943_);
    crate::leanh::lean_dec(v_a_2942_);
    crate::leanh::lean_dec_ref(v_a_2941_);
    crate::leanh::lean_dec(v_a_2940_);
    crate::leanh::lean_dec_ref(v_a_2938_);
    crate::leanh::lean_dec(v_a_2937_);
    crate::leanh::lean_dec(v_a_2936_);
    return v_res_2947_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState(
    mut v_00_u03b1_2948_: *mut crate::leanh::LeanObject,
    mut v_t_2949_: *mut crate::leanh::LeanObject,
    mut v_a_2950_: *mut crate::leanh::LeanObject,
    mut v_a_2951_: *mut crate::leanh::LeanObject,
    mut v_a_2952_: *mut crate::leanh::LeanObject,
    mut v_a_2953_: u8,
    mut v_a_2954_: *mut crate::leanh::LeanObject,
    mut v_a_2955_: *mut crate::leanh::LeanObject,
    mut v_a_2956_: *mut crate::leanh::LeanObject,
    mut v_a_2957_: *mut crate::leanh::LeanObject,
    mut v_a_2958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2960_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(
        v_t_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_,
        v_a_2957_, v_a_2958_,
    );
    return v___x_2960_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState___boxed(
    mut v_00_u03b1_2961_: *mut crate::leanh::LeanObject,
    mut v_t_2962_: *mut crate::leanh::LeanObject,
    mut v_a_2963_: *mut crate::leanh::LeanObject,
    mut v_a_2964_: *mut crate::leanh::LeanObject,
    mut v_a_2965_: *mut crate::leanh::LeanObject,
    mut v_a_2966_: *mut crate::leanh::LeanObject,
    mut v_a_2967_: *mut crate::leanh::LeanObject,
    mut v_a_2968_: *mut crate::leanh::LeanObject,
    mut v_a_2969_: *mut crate::leanh::LeanObject,
    mut v_a_2970_: *mut crate::leanh::LeanObject,
    mut v_a_2971_: *mut crate::leanh::LeanObject,
    mut v_a_2972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2973_: u8 = 0;
    let mut v_res_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2973_ = (crate::leanh::lean_unbox(v_a_2966_) as u8);
    v_res_2974_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState(
        v_00_u03b1_2961_,
        v_t_2962_,
        v_a_2963_,
        v_a_2964_,
        v_a_2965_,
        v_a_boxed_2973_,
        v_a_2967_,
        v_a_2968_,
        v_a_2969_,
        v_a_2970_,
        v_a_2971_,
    );
    crate::leanh::lean_dec(v_a_2971_);
    crate::leanh::lean_dec_ref(v_a_2970_);
    crate::leanh::lean_dec(v_a_2969_);
    crate::leanh::lean_dec_ref(v_a_2968_);
    crate::leanh::lean_dec(v_a_2967_);
    crate::leanh::lean_dec_ref(v_a_2965_);
    crate::leanh::lean_dec(v_a_2964_);
    crate::leanh::lean_dec(v_a_2963_);
    return v_res_2974_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_natCast_x3f(
    mut v_n_2977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_n_2977_);
    v___x_2978_ = l_Lean_Expr_getAppFnArgs(v_n_2977_);
    v_fst_2979_ = crate::leanh::lean_ctor_get(v___x_2978_, 0);
    crate::leanh::lean_inc(v_fst_2979_);
    if crate::leanh::lean_obj_tag(v_fst_2979_) == 1 {
        let mut v_pre_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_2980_ = crate::leanh::lean_ctor_get(v_fst_2979_, 0);
        crate::leanh::lean_inc(v_pre_2980_);
        if crate::leanh::lean_obj_tag(v_pre_2980_) == 1 {
            let mut v_pre_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_pre_2981_ = crate::leanh::lean_ctor_get(v_pre_2980_, 0);
            if crate::leanh::lean_obj_tag(v_pre_2981_) == 0 {
                let mut v_snd_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2986_: u8 = 0;
                v_snd_2982_ = crate::leanh::lean_ctor_get(v___x_2978_, 1);
                crate::leanh::lean_inc(v_snd_2982_);
                crate::leanh::lean_dec_ref(v___x_2978_);
                v_str_2983_ = crate::leanh::lean_ctor_get(v_fst_2979_, 1);
                crate::leanh::lean_inc_ref(v_str_2983_);
                crate::leanh::lean_dec_ref_known(v_fst_2979_, 2);
                v_str_2984_ = crate::leanh::lean_ctor_get(v_pre_2980_, 1);
                crate::leanh::lean_inc_ref(v_str_2984_);
                crate::leanh::lean_dec_ref_known(v_pre_2980_, 2);
                v___x_2985_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
                v___x_2986_ = lean_string_dec_eq(v_str_2984_, v___x_2985_);
                crate::leanh::lean_dec_ref(v_str_2984_);
                if v___x_2986_ == 0 {
                    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v_str_2983_);
                    crate::leanh::lean_dec(v_snd_2982_);
                    v___x_2987_ = l_Lean_Expr_nat_x3f(v_n_2977_);
                    return v___x_2987_;
                } else {
                    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2989_: u8 = 0;
                    v___x_2988_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                    v___x_2989_ = lean_string_dec_eq(v_str_2983_, v___x_2988_);
                    crate::leanh::lean_dec_ref(v_str_2983_);
                    if v___x_2989_ == 0 {
                        let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_snd_2982_);
                        v___x_2990_ = l_Lean_Expr_nat_x3f(v_n_2977_);
                        return v___x_2990_;
                    } else {
                        let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2993_: u8 = 0;
                        v___x_2991_ = lean_array_get_size(v_snd_2982_);
                        v___x_2992_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_2993_ = lean_nat_dec_eq(v___x_2991_, v___x_2992_);
                        if v___x_2993_ == 0 {
                            let mut v___x_2994_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_snd_2982_);
                            v___x_2994_ = l_Lean_Expr_nat_x3f(v_n_2977_);
                            return v___x_2994_;
                        } else {
                            let mut v___x_2995_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2996_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2997_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec_ref(v_n_2977_);
                            v___x_2995_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_2996_ = lean_array_fget(v_snd_2982_, v___x_2995_);
                            crate::leanh::lean_dec(v_snd_2982_);
                            v___x_2997_ = l_Lean_Expr_nat_x3f(v___x_2996_);
                            return v___x_2997_;
                        }
                    }
                }
            } else {
                let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v_pre_2980_, 2);
                crate::leanh::lean_dec_ref_known(v_fst_2979_, 2);
                crate::leanh::lean_dec_ref(v___x_2978_);
                v___x_2998_ = l_Lean_Expr_nat_x3f(v_n_2977_);
                return v___x_2998_;
            }
        } else {
            let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_pre_2980_);
            crate::leanh::lean_dec_ref_known(v_fst_2979_, 2);
            crate::leanh::lean_dec_ref(v___x_2978_);
            v___x_2999_ = l_Lean_Expr_nat_x3f(v_n_2977_);
            return v___x_2999_;
        }
    } else {
        let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_fst_2979_);
        crate::leanh::lean_dec_ref(v___x_2978_);
        v___x_3000_ = l_Lean_Expr_nat_x3f(v_n_2977_);
        return v___x_3000_;
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Elab_Tactic_Omega_intCast_x3f_spec__0(
    mut v_a_3001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3002_ = lean_nat_to_int(v_a_3001_);
    return v___x_3002_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_intCast_x3f(
    mut v_n_3003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u8 = 0;
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: u8 = 0;
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: u8 = 0;
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3028_: u8 = 0;
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3033_: u8 = 0;
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_n_3003_);
                v___x_3004_ = l_Lean_Expr_getAppFnArgs(v_n_3003_);
                v_fst_3005_ = crate::leanh::lean_ctor_get(v___x_3004_, 0);
                crate::leanh::lean_inc(v_fst_3005_);
                if crate::leanh::lean_obj_tag(v_fst_3005_) == 1 {
                    v_pre_3006_ = crate::leanh::lean_ctor_get(v_fst_3005_, 0);
                    crate::leanh::lean_inc(v_pre_3006_);
                    if crate::leanh::lean_obj_tag(v_pre_3006_) == 1 {
                        v_pre_3007_ = crate::leanh::lean_ctor_get(v_pre_3006_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_3007_) == 0 {
                            v_snd_3008_ = crate::leanh::lean_ctor_get(v___x_3004_, 1);
                            crate::leanh::lean_inc(v_snd_3008_);
                            crate::leanh::lean_dec_ref(v___x_3004_);
                            v_str_3009_ = crate::leanh::lean_ctor_get(v_fst_3005_, 1);
                            crate::leanh::lean_inc_ref(v_str_3009_);
                            crate::leanh::lean_dec_ref_known(v_fst_3005_, 2);
                            v_str_3010_ = crate::leanh::lean_ctor_get(v_pre_3006_, 1);
                            crate::leanh::lean_inc_ref(v_str_3010_);
                            crate::leanh::lean_dec_ref_known(v_pre_3006_, 2);
                            v___x_3011_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
                            v___x_3012_ = lean_string_dec_eq(v_str_3010_, v___x_3011_);
                            crate::leanh::lean_dec_ref(v_str_3010_);
                            if v___x_3012_ == 0 {
                                crate::leanh::lean_dec_ref(v_str_3009_);
                                crate::leanh::lean_dec(v_snd_3008_);
                                v___x_3013_ = l_Lean_Expr_int_x3f(v_n_3003_);
                                return v___x_3013_;
                            } else {
                                v___x_3014_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                                v___x_3015_ = lean_string_dec_eq(v_str_3009_, v___x_3014_);
                                crate::leanh::lean_dec_ref(v_str_3009_);
                                if v___x_3015_ == 0 {
                                    crate::leanh::lean_dec(v_snd_3008_);
                                    v___x_3016_ = l_Lean_Expr_int_x3f(v_n_3003_);
                                    return v___x_3016_;
                                } else {
                                    v___x_3017_ = lean_array_get_size(v_snd_3008_);
                                    v___x_3018_ = crate::leanh::lean_unsigned_to_nat(3);
                                    v___x_3019_ = lean_nat_dec_eq(v___x_3017_, v___x_3018_);
                                    if v___x_3019_ == 0 {
                                        crate::leanh::lean_dec(v_snd_3008_);
                                        v___x_3020_ = l_Lean_Expr_int_x3f(v_n_3003_);
                                        return v___x_3020_;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_n_3003_);
                                        v___x_3021_ = crate::leanh::lean_unsigned_to_nat(2);
                                        v___x_3022_ = lean_array_fget(v_snd_3008_, v___x_3021_);
                                        crate::leanh::lean_dec(v_snd_3008_);
                                        v___x_3023_ = l_Lean_Expr_nat_x3f(v___x_3022_);
                                        if crate::leanh::lean_obj_tag(v___x_3023_) == 0 {
                                            v___x_3024_ = crate::leanh::lean_box(0);
                                            return v___x_3024_;
                                        } else {
                                            v_val_3025_ =
                                                crate::leanh::lean_ctor_get(v___x_3023_, 0);
                                            v_isSharedCheck_3033_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_3023_))
                                                    as u8;
                                            if v_isSharedCheck_3033_ == 0 {
                                                v___x_3027_ = v___x_3023_;
                                                v_isShared_3028_ = v_isSharedCheck_3033_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_val_3025_);
                                                crate::leanh::lean_dec(v___x_3023_);
                                                v___x_3027_ = crate::leanh::lean_box(0);
                                                v_isShared_3028_ = v_isSharedCheck_3033_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_pre_3006_, 2);
                            crate::leanh::lean_dec_ref_known(v_fst_3005_, 2);
                            crate::leanh::lean_dec_ref(v___x_3004_);
                            v___x_3034_ = l_Lean_Expr_int_x3f(v_n_3003_);
                            return v___x_3034_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_pre_3006_);
                        crate::leanh::lean_dec_ref_known(v_fst_3005_, 2);
                        crate::leanh::lean_dec_ref(v___x_3004_);
                        v___x_3035_ = l_Lean_Expr_int_x3f(v_n_3003_);
                        return v___x_3035_;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_3005_);
                    crate::leanh::lean_dec_ref(v___x_3004_);
                    v___x_3036_ = l_Lean_Expr_int_x3f(v_n_3003_);
                    return v___x_3036_;
                }
            }
            1 => {
                v___x_3029_ = lean_nat_to_int(v_val_3025_);
                if v_isShared_3028_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3027_, 0, v___x_3029_);
                    v___x_3031_ = v___x_3027_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3032_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3029_);
                    v___x_3031_ = v_reuseFailAlloc_3032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3031_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_groundNat_x3f(
    mut v_e_3052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: u8 = 0;
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: u8 = 0;
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: u8 = 0;
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: u8 = 0;
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: u8 = 0;
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: u8 = 0;
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: u8 = 0;
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: u8 = 0;
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: u8 = 0;
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: u8 = 0;
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: u8 = 0;
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: u8 = 0;
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: u8 = 0;
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: u8 = 0;
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: u8 = 0;
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: u8 = 0;
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_3052_);
                v___x_3053_ = l_Lean_Expr_getAppFnArgs(v_e_3052_);
                v_fst_3054_ = crate::leanh::lean_ctor_get(v___x_3053_, 0);
                crate::leanh::lean_inc(v_fst_3054_);
                if crate::leanh::lean_obj_tag(v_fst_3054_) == 1 {
                    v_pre_3055_ = crate::leanh::lean_ctor_get(v_fst_3054_, 0);
                    crate::leanh::lean_inc(v_pre_3055_);
                    if crate::leanh::lean_obj_tag(v_pre_3055_) == 1 {
                        v_pre_3056_ = crate::leanh::lean_ctor_get(v_pre_3055_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_3056_) == 0 {
                            v_snd_3057_ = crate::leanh::lean_ctor_get(v___x_3053_, 1);
                            crate::leanh::lean_inc(v_snd_3057_);
                            crate::leanh::lean_dec_ref(v___x_3053_);
                            v_str_3058_ = crate::leanh::lean_ctor_get(v_fst_3054_, 1);
                            crate::leanh::lean_inc_ref(v_str_3058_);
                            crate::leanh::lean_dec_ref_known(v_fst_3054_, 2);
                            v_str_3059_ = crate::leanh::lean_ctor_get(v_pre_3055_, 1);
                            crate::leanh::lean_inc_ref(v_str_3059_);
                            crate::leanh::lean_dec_ref_known(v_pre_3055_, 2);
                            v___x_3060_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
                            v___x_3061_ = lean_string_dec_eq(v_str_3059_, v___x_3060_);
                            if v___x_3061_ == 0 {
                                v___x_3062_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0;
                                v___x_3063_ = lean_string_dec_eq(v_str_3059_, v___x_3062_);
                                if v___x_3063_ == 0 {
                                    v___x_3064_ =
                                        l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1;
                                    v___x_3065_ = lean_string_dec_eq(v_str_3059_, v___x_3064_);
                                    if v___x_3065_ == 0 {
                                        v___x_3066_ =
                                            l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
                                        v___x_3067_ = lean_string_dec_eq(v_str_3059_, v___x_3066_);
                                        if v___x_3067_ == 0 {
                                            v___x_3068_ =
                                                l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
                                            v___x_3069_ =
                                                lean_string_dec_eq(v_str_3059_, v___x_3068_);
                                            if v___x_3069_ == 0 {
                                                v___x_3070_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
                                                v___x_3071_ =
                                                    lean_string_dec_eq(v_str_3059_, v___x_3070_);
                                                crate::leanh::lean_dec_ref(v_str_3059_);
                                                if v___x_3071_ == 0 {
                                                    crate::leanh::lean_dec_ref(v_str_3058_);
                                                    crate::leanh::lean_dec(v_snd_3057_);
                                                    v___x_3072_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                    return v___x_3072_;
                                                } else {
                                                    v___x_3073_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
                                                    v___x_3074_ = lean_string_dec_eq(
                                                        v_str_3058_,
                                                        v___x_3073_,
                                                    );
                                                    crate::leanh::lean_dec_ref(v_str_3058_);
                                                    if v___x_3074_ == 0 {
                                                        crate::leanh::lean_dec(v_snd_3057_);
                                                        v___x_3075_ =
                                                            l_Lean_Expr_nat_x3f(v_e_3052_);
                                                        return v___x_3075_;
                                                    } else {
                                                        v___x_3076_ =
                                                            lean_array_get_size(v_snd_3057_);
                                                        v___x_3077_ =
                                                            crate::leanh::lean_unsigned_to_nat(6);
                                                        v___x_3078_ = lean_nat_dec_eq(
                                                            v___x_3076_,
                                                            v___x_3077_,
                                                        );
                                                        if v___x_3078_ == 0 {
                                                            crate::leanh::lean_dec(v_snd_3057_);
                                                            v___x_3079_ =
                                                                l_Lean_Expr_nat_x3f(v_e_3052_);
                                                            return v___x_3079_;
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_e_3052_);
                                                            v___f_3080_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
                                                            v___x_3081_ =
                                                                crate::leanh::lean_unsigned_to_nat(
                                                                    4,
                                                                );
                                                            v___x_3082_ = lean_array_fget(
                                                                v_snd_3057_,
                                                                v___x_3081_,
                                                            );
                                                            v___x_3083_ =
                                                                crate::leanh::lean_unsigned_to_nat(
                                                                    5,
                                                                );
                                                            v___x_3084_ = lean_array_fget(
                                                                v_snd_3057_,
                                                                v___x_3083_,
                                                            );
                                                            crate::leanh::lean_dec(v_snd_3057_);
                                                            v___x_3085_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3080_, v___x_3082_, v___x_3084_);
                                                            return v___x_3085_;
                                                        }
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_str_3059_);
                                                v___x_3086_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
                                                v___x_3087_ =
                                                    lean_string_dec_eq(v_str_3058_, v___x_3086_);
                                                crate::leanh::lean_dec_ref(v_str_3058_);
                                                if v___x_3087_ == 0 {
                                                    crate::leanh::lean_dec(v_snd_3057_);
                                                    v___x_3088_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                    return v___x_3088_;
                                                } else {
                                                    v___x_3089_ = lean_array_get_size(v_snd_3057_);
                                                    v___x_3090_ =
                                                        crate::leanh::lean_unsigned_to_nat(6);
                                                    v___x_3091_ =
                                                        lean_nat_dec_eq(v___x_3089_, v___x_3090_);
                                                    if v___x_3091_ == 0 {
                                                        crate::leanh::lean_dec(v_snd_3057_);
                                                        v___x_3092_ =
                                                            l_Lean_Expr_nat_x3f(v_e_3052_);
                                                        return v___x_3092_;
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_e_3052_);
                                                        v___f_3093_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
                                                        v___x_3094_ =
                                                            crate::leanh::lean_unsigned_to_nat(4);
                                                        v___x_3095_ = lean_array_fget(
                                                            v_snd_3057_,
                                                            v___x_3094_,
                                                        );
                                                        v___x_3096_ =
                                                            crate::leanh::lean_unsigned_to_nat(5);
                                                        v___x_3097_ = lean_array_fget(
                                                            v_snd_3057_,
                                                            v___x_3096_,
                                                        );
                                                        crate::leanh::lean_dec(v_snd_3057_);
                                                        v___x_3098_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3093_, v___x_3095_, v___x_3097_);
                                                        return v___x_3098_;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_str_3059_);
                                            v___x_3099_ =
                                                l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
                                            v___x_3100_ =
                                                lean_string_dec_eq(v_str_3058_, v___x_3099_);
                                            crate::leanh::lean_dec_ref(v_str_3058_);
                                            if v___x_3100_ == 0 {
                                                crate::leanh::lean_dec(v_snd_3057_);
                                                v___x_3101_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                return v___x_3101_;
                                            } else {
                                                v___x_3102_ = lean_array_get_size(v_snd_3057_);
                                                v___x_3103_ = crate::leanh::lean_unsigned_to_nat(6);
                                                v___x_3104_ =
                                                    lean_nat_dec_eq(v___x_3102_, v___x_3103_);
                                                if v___x_3104_ == 0 {
                                                    crate::leanh::lean_dec(v_snd_3057_);
                                                    v___x_3105_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                    return v___x_3105_;
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_e_3052_);
                                                    v___f_3106_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10;
                                                    v___x_3107_ =
                                                        crate::leanh::lean_unsigned_to_nat(4);
                                                    v___x_3108_ =
                                                        lean_array_fget(v_snd_3057_, v___x_3107_);
                                                    v___x_3109_ =
                                                        crate::leanh::lean_unsigned_to_nat(5);
                                                    v___x_3110_ =
                                                        lean_array_fget(v_snd_3057_, v___x_3109_);
                                                    crate::leanh::lean_dec(v_snd_3057_);
                                                    v___x_3111_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3106_, v___x_3108_, v___x_3110_);
                                                    return v___x_3111_;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_str_3059_);
                                        v___x_3112_ =
                                            l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11;
                                        v___x_3113_ = lean_string_dec_eq(v_str_3058_, v___x_3112_);
                                        crate::leanh::lean_dec_ref(v_str_3058_);
                                        if v___x_3113_ == 0 {
                                            crate::leanh::lean_dec(v_snd_3057_);
                                            v___x_3114_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                            return v___x_3114_;
                                        } else {
                                            v___x_3115_ = lean_array_get_size(v_snd_3057_);
                                            v___x_3116_ = crate::leanh::lean_unsigned_to_nat(6);
                                            v___x_3117_ = lean_nat_dec_eq(v___x_3115_, v___x_3116_);
                                            if v___x_3117_ == 0 {
                                                crate::leanh::lean_dec(v_snd_3057_);
                                                v___x_3118_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                return v___x_3118_;
                                            } else {
                                                crate::leanh::lean_dec_ref(v_e_3052_);
                                                v___f_3119_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12;
                                                v___x_3120_ = crate::leanh::lean_unsigned_to_nat(4);
                                                v___x_3121_ =
                                                    lean_array_fget(v_snd_3057_, v___x_3120_);
                                                v___x_3122_ = crate::leanh::lean_unsigned_to_nat(5);
                                                v___x_3123_ =
                                                    lean_array_fget(v_snd_3057_, v___x_3122_);
                                                crate::leanh::lean_dec(v_snd_3057_);
                                                v___x_3124_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3119_, v___x_3121_, v___x_3123_);
                                                return v___x_3124_;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_str_3059_);
                                    v___x_3125_ =
                                        l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13;
                                    v___x_3126_ = lean_string_dec_eq(v_str_3058_, v___x_3125_);
                                    crate::leanh::lean_dec_ref(v_str_3058_);
                                    if v___x_3126_ == 0 {
                                        crate::leanh::lean_dec(v_snd_3057_);
                                        v___x_3127_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                        return v___x_3127_;
                                    } else {
                                        v___x_3128_ = lean_array_get_size(v_snd_3057_);
                                        v___x_3129_ = crate::leanh::lean_unsigned_to_nat(6);
                                        v___x_3130_ = lean_nat_dec_eq(v___x_3128_, v___x_3129_);
                                        if v___x_3130_ == 0 {
                                            crate::leanh::lean_dec(v_snd_3057_);
                                            v___x_3131_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                            return v___x_3131_;
                                        } else {
                                            crate::leanh::lean_dec_ref(v_e_3052_);
                                            v___f_3132_ =
                                                l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14;
                                            v___x_3133_ = crate::leanh::lean_unsigned_to_nat(4);
                                            v___x_3134_ = lean_array_fget(v_snd_3057_, v___x_3133_);
                                            v___x_3135_ = crate::leanh::lean_unsigned_to_nat(5);
                                            v___x_3136_ = lean_array_fget(v_snd_3057_, v___x_3135_);
                                            crate::leanh::lean_dec(v_snd_3057_);
                                            v___x_3137_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3132_, v___x_3134_, v___x_3136_);
                                            return v___x_3137_;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_str_3059_);
                                v___x_3138_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                                v___x_3139_ = lean_string_dec_eq(v_str_3058_, v___x_3138_);
                                crate::leanh::lean_dec_ref(v_str_3058_);
                                if v___x_3139_ == 0 {
                                    crate::leanh::lean_dec(v_snd_3057_);
                                    v___x_3140_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                    return v___x_3140_;
                                } else {
                                    v___x_3141_ = lean_array_get_size(v_snd_3057_);
                                    v___x_3142_ = crate::leanh::lean_unsigned_to_nat(3);
                                    v___x_3143_ = lean_nat_dec_eq(v___x_3141_, v___x_3142_);
                                    if v___x_3143_ == 0 {
                                        crate::leanh::lean_dec(v_snd_3057_);
                                        v___x_3144_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                        return v___x_3144_;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_e_3052_);
                                        v___x_3145_ = crate::leanh::lean_unsigned_to_nat(2);
                                        v___x_3146_ = lean_array_fget(v_snd_3057_, v___x_3145_);
                                        crate::leanh::lean_dec(v_snd_3057_);
                                        v_e_3052_ = v___x_3146_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_pre_3055_, 2);
                            crate::leanh::lean_dec_ref_known(v_fst_3054_, 2);
                            crate::leanh::lean_dec_ref(v___x_3053_);
                            v___x_3148_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                            return v___x_3148_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_fst_3054_, 2);
                        crate::leanh::lean_dec(v_pre_3055_);
                        crate::leanh::lean_dec_ref(v___x_3053_);
                        v___x_3149_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                        return v___x_3149_;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_3054_);
                    crate::leanh::lean_dec_ref(v___x_3053_);
                    v___x_3150_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                    return v___x_3150_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(
    mut v_f_3151_: *mut crate::leanh::LeanObject,
    mut v_x_3152_: *mut crate::leanh::LeanObject,
    mut v_y_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3160_: u8 = 0;
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3165_: u8 = 0;
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3154_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v_x_3152_);
                if crate::leanh::lean_obj_tag(v___x_3154_) == 1 {
                    v_val_3155_ = crate::leanh::lean_ctor_get(v___x_3154_, 0);
                    crate::leanh::lean_inc(v_val_3155_);
                    crate::leanh::lean_dec_ref_known(v___x_3154_, 1);
                    v___x_3156_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v_y_3153_);
                    if crate::leanh::lean_obj_tag(v___x_3156_) == 1 {
                        v_val_3157_ = crate::leanh::lean_ctor_get(v___x_3156_, 0);
                        v_isSharedCheck_3165_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3156_)) as u8;
                        if v_isSharedCheck_3165_ == 0 {
                            v___x_3159_ = v___x_3156_;
                            v_isShared_3160_ = v_isSharedCheck_3165_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3157_);
                            crate::leanh::lean_dec(v___x_3156_);
                            v___x_3159_ = crate::leanh::lean_box(0);
                            v_isShared_3160_ = v_isSharedCheck_3165_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3156_);
                        crate::leanh::lean_dec(v_val_3155_);
                        crate::leanh::lean_dec_ref(v_f_3151_);
                        v___x_3166_ = crate::leanh::lean_box(0);
                        return v___x_3166_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3154_);
                    crate::leanh::lean_dec_ref(v_y_3153_);
                    crate::leanh::lean_dec_ref(v_f_3151_);
                    v___x_3167_ = crate::leanh::lean_box(0);
                    return v___x_3167_;
                }
            }
            1 => {
                v___x_3161_ = crate::leanh::lean_apply_2(v_f_3151_, v_val_3155_, v_val_3157_);
                if v_isShared_3160_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3159_, 0, v___x_3161_);
                    v___x_3163_ = v___x_3159_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3164_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3161_);
                    v___x_3163_ = v_reuseFailAlloc_3164_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3163_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_groundInt_x3f(
    mut v_e_3172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: u8 = 0;
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: u8 = 0;
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: u8 = 0;
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: u8 = 0;
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: u8 = 0;
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: u8 = 0;
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: u8 = 0;
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: u8 = 0;
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3210_: u8 = 0;
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3215_: u8 = 0;
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: u8 = 0;
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: u8 = 0;
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: u8 = 0;
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: u8 = 0;
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: u8 = 0;
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: u8 = 0;
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: u8 = 0;
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3284_: u8 = 0;
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3289_: u8 = 0;
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_3172_);
                v___x_3173_ = l_Lean_Expr_getAppFnArgs(v_e_3172_);
                v_fst_3174_ = crate::leanh::lean_ctor_get(v___x_3173_, 0);
                crate::leanh::lean_inc(v_fst_3174_);
                if crate::leanh::lean_obj_tag(v_fst_3174_) == 1 {
                    v_pre_3175_ = crate::leanh::lean_ctor_get(v_fst_3174_, 0);
                    crate::leanh::lean_inc(v_pre_3175_);
                    if crate::leanh::lean_obj_tag(v_pre_3175_) == 1 {
                        v_pre_3176_ = crate::leanh::lean_ctor_get(v_pre_3175_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_3176_) == 0 {
                            v_snd_3177_ = crate::leanh::lean_ctor_get(v___x_3173_, 1);
                            crate::leanh::lean_inc(v_snd_3177_);
                            crate::leanh::lean_dec_ref(v___x_3173_);
                            v_str_3178_ = crate::leanh::lean_ctor_get(v_fst_3174_, 1);
                            crate::leanh::lean_inc_ref(v_str_3178_);
                            crate::leanh::lean_dec_ref_known(v_fst_3174_, 2);
                            v_str_3179_ = crate::leanh::lean_ctor_get(v_pre_3175_, 1);
                            crate::leanh::lean_inc_ref(v_str_3179_);
                            crate::leanh::lean_dec_ref_known(v_pre_3175_, 2);
                            v___x_3180_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
                            v___x_3181_ = lean_string_dec_eq(v_str_3179_, v___x_3180_);
                            if v___x_3181_ == 0 {
                                v___x_3182_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0;
                                v___x_3183_ = lean_string_dec_eq(v_str_3179_, v___x_3182_);
                                if v___x_3183_ == 0 {
                                    v___x_3184_ =
                                        l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1;
                                    v___x_3185_ = lean_string_dec_eq(v_str_3179_, v___x_3184_);
                                    if v___x_3185_ == 0 {
                                        v___x_3186_ =
                                            l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
                                        v___x_3187_ = lean_string_dec_eq(v_str_3179_, v___x_3186_);
                                        if v___x_3187_ == 0 {
                                            v___x_3188_ =
                                                l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
                                            v___x_3189_ =
                                                lean_string_dec_eq(v_str_3179_, v___x_3188_);
                                            if v___x_3189_ == 0 {
                                                v___x_3190_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
                                                v___x_3191_ =
                                                    lean_string_dec_eq(v_str_3179_, v___x_3190_);
                                                crate::leanh::lean_dec_ref(v_str_3179_);
                                                if v___x_3191_ == 0 {
                                                    crate::leanh::lean_dec_ref(v_str_3178_);
                                                    crate::leanh::lean_dec(v_snd_3177_);
                                                    v___x_3192_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                    return v___x_3192_;
                                                } else {
                                                    v___x_3193_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
                                                    v___x_3194_ = lean_string_dec_eq(
                                                        v_str_3178_,
                                                        v___x_3193_,
                                                    );
                                                    crate::leanh::lean_dec_ref(v_str_3178_);
                                                    if v___x_3194_ == 0 {
                                                        crate::leanh::lean_dec(v_snd_3177_);
                                                        v___x_3195_ =
                                                            l_Lean_Expr_int_x3f(v_e_3172_);
                                                        return v___x_3195_;
                                                    } else {
                                                        v___x_3196_ =
                                                            lean_array_get_size(v_snd_3177_);
                                                        v___x_3197_ =
                                                            crate::leanh::lean_unsigned_to_nat(6);
                                                        v___x_3198_ = lean_nat_dec_eq(
                                                            v___x_3196_,
                                                            v___x_3197_,
                                                        );
                                                        if v___x_3198_ == 0 {
                                                            crate::leanh::lean_dec(v_snd_3177_);
                                                            v___x_3199_ =
                                                                l_Lean_Expr_int_x3f(v_e_3172_);
                                                            return v___x_3199_;
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_e_3172_);
                                                            v___x_3200_ =
                                                                crate::leanh::lean_unsigned_to_nat(
                                                                    4,
                                                                );
                                                            v___x_3201_ = lean_array_fget_borrowed(
                                                                v_snd_3177_,
                                                                v___x_3200_,
                                                            );
                                                            crate::leanh::lean_inc(v___x_3201_);
                                                            v___x_3202_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v___x_3201_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_3202_,
                                                            ) == 1
                                                            {
                                                                v_val_3203_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_3202_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_val_3203_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_3202_,
                                                                    1,
                                                                );
                                                                v___x_3204_ = crate::leanh::lean_unsigned_to_nat(5);
                                                                v___x_3205_ = lean_array_fget(
                                                                    v_snd_3177_,
                                                                    v___x_3204_,
                                                                );
                                                                crate::leanh::lean_dec(v_snd_3177_);
                                                                v___x_3206_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v___x_3205_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_3206_,
                                                                ) == 1
                                                                {
                                                                    v_val_3207_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_3206_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_3215_ = (!crate::leanh::lean_is_exclusive(v___x_3206_)) as u8;
                                                                    if v_isSharedCheck_3215_ == 0 {
                                                                        v___x_3209_ = v___x_3206_;
                                                                        v_isShared_3210_ =
                                                                            v_isSharedCheck_3215_;
                                                                        state = 1;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_val_3207_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_3206_,
                                                                        );
                                                                        v___x_3209_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_3210_ =
                                                                            v_isSharedCheck_3215_;
                                                                        state = 1;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec(
                                                                        v___x_3206_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_val_3203_,
                                                                    );
                                                                    v___x_3216_ =
                                                                        crate::leanh::lean_box(0);
                                                                    return v___x_3216_;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec(v___x_3202_);
                                                                crate::leanh::lean_dec(v_snd_3177_);
                                                                v___x_3217_ =
                                                                    crate::leanh::lean_box(0);
                                                                return v___x_3217_;
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_str_3179_);
                                                v___x_3218_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
                                                v___x_3219_ =
                                                    lean_string_dec_eq(v_str_3178_, v___x_3218_);
                                                crate::leanh::lean_dec_ref(v_str_3178_);
                                                if v___x_3219_ == 0 {
                                                    crate::leanh::lean_dec(v_snd_3177_);
                                                    v___x_3220_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                    return v___x_3220_;
                                                } else {
                                                    v___x_3221_ = lean_array_get_size(v_snd_3177_);
                                                    v___x_3222_ =
                                                        crate::leanh::lean_unsigned_to_nat(6);
                                                    v___x_3223_ =
                                                        lean_nat_dec_eq(v___x_3221_, v___x_3222_);
                                                    if v___x_3223_ == 0 {
                                                        crate::leanh::lean_dec(v_snd_3177_);
                                                        v___x_3224_ =
                                                            l_Lean_Expr_int_x3f(v_e_3172_);
                                                        return v___x_3224_;
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_e_3172_);
                                                        v___f_3225_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0;
                                                        v___x_3226_ =
                                                            crate::leanh::lean_unsigned_to_nat(4);
                                                        v___x_3227_ = lean_array_fget(
                                                            v_snd_3177_,
                                                            v___x_3226_,
                                                        );
                                                        v___x_3228_ =
                                                            crate::leanh::lean_unsigned_to_nat(5);
                                                        v___x_3229_ = lean_array_fget(
                                                            v_snd_3177_,
                                                            v___x_3228_,
                                                        );
                                                        crate::leanh::lean_dec(v_snd_3177_);
                                                        v___x_3230_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_3225_, v___x_3227_, v___x_3229_);
                                                        return v___x_3230_;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_str_3179_);
                                            v___x_3231_ =
                                                l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
                                            v___x_3232_ =
                                                lean_string_dec_eq(v_str_3178_, v___x_3231_);
                                            crate::leanh::lean_dec_ref(v_str_3178_);
                                            if v___x_3232_ == 0 {
                                                crate::leanh::lean_dec(v_snd_3177_);
                                                v___x_3233_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                return v___x_3233_;
                                            } else {
                                                v___x_3234_ = lean_array_get_size(v_snd_3177_);
                                                v___x_3235_ = crate::leanh::lean_unsigned_to_nat(6);
                                                v___x_3236_ =
                                                    lean_nat_dec_eq(v___x_3234_, v___x_3235_);
                                                if v___x_3236_ == 0 {
                                                    crate::leanh::lean_dec(v_snd_3177_);
                                                    v___x_3237_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                    return v___x_3237_;
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_e_3172_);
                                                    v___f_3238_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1;
                                                    v___x_3239_ =
                                                        crate::leanh::lean_unsigned_to_nat(4);
                                                    v___x_3240_ =
                                                        lean_array_fget(v_snd_3177_, v___x_3239_);
                                                    v___x_3241_ =
                                                        crate::leanh::lean_unsigned_to_nat(5);
                                                    v___x_3242_ =
                                                        lean_array_fget(v_snd_3177_, v___x_3241_);
                                                    crate::leanh::lean_dec(v_snd_3177_);
                                                    v___x_3243_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_3238_, v___x_3240_, v___x_3242_);
                                                    return v___x_3243_;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_str_3179_);
                                        v___x_3244_ =
                                            l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11;
                                        v___x_3245_ = lean_string_dec_eq(v_str_3178_, v___x_3244_);
                                        crate::leanh::lean_dec_ref(v_str_3178_);
                                        if v___x_3245_ == 0 {
                                            crate::leanh::lean_dec(v_snd_3177_);
                                            v___x_3246_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                            return v___x_3246_;
                                        } else {
                                            v___x_3247_ = lean_array_get_size(v_snd_3177_);
                                            v___x_3248_ = crate::leanh::lean_unsigned_to_nat(6);
                                            v___x_3249_ = lean_nat_dec_eq(v___x_3247_, v___x_3248_);
                                            if v___x_3249_ == 0 {
                                                crate::leanh::lean_dec(v_snd_3177_);
                                                v___x_3250_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                return v___x_3250_;
                                            } else {
                                                crate::leanh::lean_dec_ref(v_e_3172_);
                                                v___f_3251_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2;
                                                v___x_3252_ = crate::leanh::lean_unsigned_to_nat(4);
                                                v___x_3253_ =
                                                    lean_array_fget(v_snd_3177_, v___x_3252_);
                                                v___x_3254_ = crate::leanh::lean_unsigned_to_nat(5);
                                                v___x_3255_ =
                                                    lean_array_fget(v_snd_3177_, v___x_3254_);
                                                crate::leanh::lean_dec(v_snd_3177_);
                                                v___x_3256_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_3251_, v___x_3253_, v___x_3255_);
                                                return v___x_3256_;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_str_3179_);
                                    v___x_3257_ =
                                        l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13;
                                    v___x_3258_ = lean_string_dec_eq(v_str_3178_, v___x_3257_);
                                    crate::leanh::lean_dec_ref(v_str_3178_);
                                    if v___x_3258_ == 0 {
                                        crate::leanh::lean_dec(v_snd_3177_);
                                        v___x_3259_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                        return v___x_3259_;
                                    } else {
                                        v___x_3260_ = lean_array_get_size(v_snd_3177_);
                                        v___x_3261_ = crate::leanh::lean_unsigned_to_nat(6);
                                        v___x_3262_ = lean_nat_dec_eq(v___x_3260_, v___x_3261_);
                                        if v___x_3262_ == 0 {
                                            crate::leanh::lean_dec(v_snd_3177_);
                                            v___x_3263_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                            return v___x_3263_;
                                        } else {
                                            crate::leanh::lean_dec_ref(v_e_3172_);
                                            v___f_3264_ =
                                                l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3;
                                            v___x_3265_ = crate::leanh::lean_unsigned_to_nat(4);
                                            v___x_3266_ = lean_array_fget(v_snd_3177_, v___x_3265_);
                                            v___x_3267_ = crate::leanh::lean_unsigned_to_nat(5);
                                            v___x_3268_ = lean_array_fget(v_snd_3177_, v___x_3267_);
                                            crate::leanh::lean_dec(v_snd_3177_);
                                            v___x_3269_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_3264_, v___x_3266_, v___x_3268_);
                                            return v___x_3269_;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_str_3179_);
                                v___x_3270_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                                v___x_3271_ = lean_string_dec_eq(v_str_3178_, v___x_3270_);
                                crate::leanh::lean_dec_ref(v_str_3178_);
                                if v___x_3271_ == 0 {
                                    crate::leanh::lean_dec(v_snd_3177_);
                                    v___x_3272_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                    return v___x_3272_;
                                } else {
                                    v___x_3273_ = lean_array_get_size(v_snd_3177_);
                                    v___x_3274_ = crate::leanh::lean_unsigned_to_nat(3);
                                    v___x_3275_ = lean_nat_dec_eq(v___x_3273_, v___x_3274_);
                                    if v___x_3275_ == 0 {
                                        crate::leanh::lean_dec(v_snd_3177_);
                                        v___x_3276_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                        return v___x_3276_;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_e_3172_);
                                        v___x_3277_ = crate::leanh::lean_unsigned_to_nat(2);
                                        v___x_3278_ = lean_array_fget(v_snd_3177_, v___x_3277_);
                                        crate::leanh::lean_dec(v_snd_3177_);
                                        v___x_3279_ =
                                            l_Lean_Elab_Tactic_Omega_groundNat_x3f(v___x_3278_);
                                        if crate::leanh::lean_obj_tag(v___x_3279_) == 0 {
                                            v___x_3280_ = crate::leanh::lean_box(0);
                                            return v___x_3280_;
                                        } else {
                                            v_val_3281_ =
                                                crate::leanh::lean_ctor_get(v___x_3279_, 0);
                                            v_isSharedCheck_3289_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_3279_))
                                                    as u8;
                                            if v_isSharedCheck_3289_ == 0 {
                                                v___x_3283_ = v___x_3279_;
                                                v_isShared_3284_ = v_isSharedCheck_3289_;
                                                state = 3;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_val_3281_);
                                                crate::leanh::lean_dec(v___x_3279_);
                                                v___x_3283_ = crate::leanh::lean_box(0);
                                                v_isShared_3284_ = v_isSharedCheck_3289_;
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_pre_3175_, 2);
                            crate::leanh::lean_dec_ref_known(v_fst_3174_, 2);
                            crate::leanh::lean_dec_ref(v___x_3173_);
                            v___x_3290_ = l_Lean_Expr_int_x3f(v_e_3172_);
                            return v___x_3290_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_fst_3174_, 2);
                        crate::leanh::lean_dec(v_pre_3175_);
                        crate::leanh::lean_dec_ref(v___x_3173_);
                        v___x_3291_ = l_Lean_Expr_int_x3f(v_e_3172_);
                        return v___x_3291_;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_3174_);
                    crate::leanh::lean_dec_ref(v___x_3173_);
                    v___x_3292_ = l_Lean_Expr_int_x3f(v_e_3172_);
                    return v___x_3292_;
                }
            }
            1 => {
                v___x_3211_ = l_Int_pow(v_val_3203_, v_val_3207_);
                crate::leanh::lean_dec(v_val_3207_);
                crate::leanh::lean_dec(v_val_3203_);
                if v_isShared_3210_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3209_, 0, v___x_3211_);
                    v___x_3213_ = v___x_3209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3214_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
                    v___x_3213_ = v_reuseFailAlloc_3214_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3213_;
            }
            3 => {
                v___x_3285_ = lean_nat_to_int(v_val_3281_);
                if v_isShared_3284_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3283_, 0, v___x_3285_);
                    v___x_3287_ = v___x_3283_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3288_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3285_);
                    v___x_3287_ = v_reuseFailAlloc_3288_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(
    mut v_f_3293_: *mut crate::leanh::LeanObject,
    mut v_x_3294_: *mut crate::leanh::LeanObject,
    mut v_y_3295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3302_: u8 = 0;
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3307_: u8 = 0;
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3296_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v_x_3294_);
                if crate::leanh::lean_obj_tag(v___x_3296_) == 1 {
                    v_val_3297_ = crate::leanh::lean_ctor_get(v___x_3296_, 0);
                    crate::leanh::lean_inc(v_val_3297_);
                    crate::leanh::lean_dec_ref_known(v___x_3296_, 1);
                    v___x_3298_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v_y_3295_);
                    if crate::leanh::lean_obj_tag(v___x_3298_) == 1 {
                        v_val_3299_ = crate::leanh::lean_ctor_get(v___x_3298_, 0);
                        v_isSharedCheck_3307_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3298_)) as u8;
                        if v_isSharedCheck_3307_ == 0 {
                            v___x_3301_ = v___x_3298_;
                            v_isShared_3302_ = v_isSharedCheck_3307_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3299_);
                            crate::leanh::lean_dec(v___x_3298_);
                            v___x_3301_ = crate::leanh::lean_box(0);
                            v_isShared_3302_ = v_isSharedCheck_3307_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3298_);
                        crate::leanh::lean_dec(v_val_3297_);
                        crate::leanh::lean_dec_ref(v_f_3293_);
                        v___x_3308_ = crate::leanh::lean_box(0);
                        return v___x_3308_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3296_);
                    crate::leanh::lean_dec_ref(v_y_3295_);
                    crate::leanh::lean_dec_ref(v_f_3293_);
                    v___x_3309_ = crate::leanh::lean_box(0);
                    return v___x_3309_;
                }
            }
            1 => {
                v___x_3303_ = crate::leanh::lean_apply_2(v_f_3293_, v_val_3297_, v_val_3299_);
                if v_isShared_3302_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3301_, 0, v___x_3303_);
                    v___x_3305_ = v___x_3301_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3306_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
                    v___x_3305_ = v_reuseFailAlloc_3306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(
    mut v_a_3310_: *mut crate::leanh::LeanObject,
    mut v_b_3311_: *mut crate::leanh::LeanObject,
    mut v_a_3312_: *mut crate::leanh::LeanObject,
    mut v_a_3313_: *mut crate::leanh::LeanObject,
    mut v_a_3314_: *mut crate::leanh::LeanObject,
    mut v_a_3315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3323_: u8 = 0;
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_a_3310_);
                v___x_3317_ =
                    l_Lean_Meta_mkEqRefl(v_a_3310_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
                if crate::leanh::lean_obj_tag(v___x_3317_) == 0 {
                    v_a_3318_ = crate::leanh::lean_ctor_get(v___x_3317_, 0);
                    crate::leanh::lean_inc(v_a_3318_);
                    crate::leanh::lean_dec_ref_known(v___x_3317_, 1);
                    v___x_3319_ = l_Lean_Meta_mkEq(
                        v_a_3310_, v_b_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3319_) == 0 {
                        v_a_3320_ = crate::leanh::lean_ctor_get(v___x_3319_, 0);
                        v_isSharedCheck_3328_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3319_)) as u8;
                        if v_isSharedCheck_3328_ == 0 {
                            v___x_3322_ = v___x_3319_;
                            v_isShared_3323_ = v_isSharedCheck_3328_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3320_);
                            crate::leanh::lean_dec(v___x_3319_);
                            v___x_3322_ = crate::leanh::lean_box(0);
                            v_isShared_3323_ = v_isSharedCheck_3328_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3318_);
                        return v___x_3319_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_3311_);
                    crate::leanh::lean_dec_ref(v_a_3310_);
                    return v___x_3317_;
                }
            }
            1 => {
                v___x_3324_ = l_Lean_Meta_mkExpectedPropHint(v_a_3318_, v_a_3320_);
                if v_isShared_3323_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3322_, 0, v___x_3324_);
                    v___x_3326_ = v___x_3322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3327_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
                    v___x_3326_ = v_reuseFailAlloc_3327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType___boxed(
    mut v_a_3329_: *mut crate::leanh::LeanObject,
    mut v_b_3330_: *mut crate::leanh::LeanObject,
    mut v_a_3331_: *mut crate::leanh::LeanObject,
    mut v_a_3332_: *mut crate::leanh::LeanObject,
    mut v_a_3333_: *mut crate::leanh::LeanObject,
    mut v_a_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(
        v_a_3329_, v_b_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_,
    );
    crate::leanh::lean_dec(v_a_3334_);
    crate::leanh::lean_dec_ref(v_a_3333_);
    crate::leanh::lean_dec(v_a_3332_);
    crate::leanh::lean_dec_ref(v_a_3331_);
    return v_res_3336_;
}
pub unsafe fn l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(
    mut v_a_3337_: *mut crate::leanh::LeanObject,
    mut v_x_3338_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3339_: u8 = 0;
    let mut v_head_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3338_) == 0 {
                    v___x_3339_ = 0;
                    return v___x_3339_;
                } else {
                    v_head_3340_ = crate::leanh::lean_ctor_get(v_x_3338_, 0);
                    v_tail_3341_ = crate::leanh::lean_ctor_get(v_x_3338_, 1);
                    v___x_3342_ = lean_expr_eqv(v_a_3337_, v_head_3340_);
                    if v___x_3342_ == 0 {
                        v_x_3338_ = v_tail_3341_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3342_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0___boxed(
    mut v_a_3344_: *mut crate::leanh::LeanObject,
    mut v_x_3345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3346_: u8 = 0;
    let mut v_r_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3346_ =
        l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v_a_3344_, v_x_3345_);
    crate::leanh::lean_dec(v_x_3345_);
    crate::leanh::lean_dec_ref(v_a_3344_);
    v_r_3347_ = crate::leanh::lean_box((v_res_3346_) as usize);
    return v_r_3347_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3356_ = crate::leanh::lean_box(0);
    v___x_3357_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5;
    v___x_3358_ = l_Lean_Expr_const___override(v___x_3357_, v___x_3356_);
    return v___x_3358_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3363_ = crate::leanh::lean_box(0);
    v___x_3364_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
    v___x_3365_ = l_Lean_Expr_const___override(v___x_3364_, v___x_3363_);
    return v___x_3365_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3371_ = crate::leanh::lean_box(0);
    v___x_3372_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12;
    v___x_3373_ = l_Lean_Expr_const___override(v___x_3372_, v___x_3371_);
    return v___x_3373_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3378_ = crate::leanh::lean_box(0);
    v___x_3379_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15;
    v___x_3380_ = l_Lean_Expr_const___override(v___x_3379_, v___x_3378_);
    return v___x_3380_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3393_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3394_ = l_Lean_Level_ofNat(v___x_3393_);
    return v___x_3394_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3400_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3401_ = l_Lean_mkNatLit(v___x_3400_);
    return v___x_3401_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3424_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3425_ = lean_nat_to_int(v___x_3424_);
    return v___x_3425_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39() -> u8 {
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: u8 = 0;
    v___x_3426_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38,
    );
    v___x_3427_ = lean_int_dec_le(v___x_3426_, v___x_3426_);
    return v___x_3427_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3437_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38,
    );
    v___x_3438_ = lean_int_neg(v___x_3437_);
    return v___x_3438_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3439_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45,
    );
    v___x_3440_ = l_Int_toNat(v___x_3439_);
    return v___x_3440_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3441_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46,
    );
    v___x_3442_ = l_Lean_instToExprInt_mkNat(v___x_3441_);
    return v___x_3442_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3443_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38,
    );
    v___x_3444_ = l_Int_toNat(v___x_3443_);
    return v___x_3444_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3445_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48,
    );
    v___x_3446_ = l_Lean_instToExprInt_mkNat(v___x_3445_);
    return v___x_3446_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3447_ = crate::leanh::lean_box(0);
    v___x_3448_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23,
    );
    v___x_3449_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3449_, 0, v___x_3448_);
    crate::leanh::lean_ctor_set(v___x_3449_, 1, v___x_3447_);
    return v___x_3449_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3450_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50,
    );
    v___x_3451_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22;
    v___x_3452_ = l_Lean_Expr_const___override(v___x_3451_, v___x_3450_);
    return v___x_3452_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3457_ = crate::leanh::lean_box(0);
    v___x_3458_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53;
    v___x_3459_ = l_Lean_Expr_const___override(v___x_3458_, v___x_3457_);
    return v___x_3459_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3466_ = crate::leanh::lean_box(0);
    v___x_3467_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56;
    v___x_3468_ = l_Lean_Expr_const___override(v___x_3467_, v___x_3466_);
    return v___x_3468_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3469_ = crate::leanh::lean_box(0);
    v___x_3470_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33;
    v___x_3471_ = l_Lean_Expr_const___override(v___x_3470_, v___x_3469_);
    return v___x_3471_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3472_ = crate::leanh::lean_box(0);
    v___x_3473_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35;
    v___x_3474_ = l_Lean_Expr_const___override(v___x_3473_, v___x_3472_);
    return v___x_3474_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3475_ = crate::leanh::lean_box(0);
    v___x_3476_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37;
    v___x_3477_ = l_Lean_Expr_const___override(v___x_3476_, v___x_3475_);
    return v___x_3477_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3478_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50,
    );
    v___x_3479_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42;
    v___x_3480_ = l_Lean_Expr_const___override(v___x_3479_, v___x_3478_);
    return v___x_3480_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3481_ = crate::leanh::lean_box(0);
    v___x_3482_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44;
    v___x_3483_ = l_Lean_Expr_const___override(v___x_3482_, v___x_3481_);
    return v___x_3483_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3484_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47,
    );
    v___x_3485_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62,
    );
    v___x_3486_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once),
        _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2,
    );
    v___x_3487_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61,
    );
    v___x_3488_ = l_Lean_mkApp3(v___x_3487_, v___x_3486_, v___x_3485_, v___x_3484_);
    return v___x_3488_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3492_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3493_ = l_Lean_Level_ofNat(v___x_3492_);
    return v___x_3493_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3494_ = crate::leanh::lean_box(0);
    v___x_3495_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66,
    );
    v___x_3496_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3496_, 0, v___x_3495_);
    crate::leanh::lean_ctor_set(v___x_3496_, 1, v___x_3494_);
    return v___x_3496_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3497_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67,
    );
    v___x_3498_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65;
    v___x_3499_ = l_Lean_Expr_const___override(v___x_3498_, v___x_3497_);
    return v___x_3499_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3504_ = crate::leanh::lean_box(0);
    v___x_3505_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70;
    v___x_3506_ = l_Lean_Expr_const___override(v___x_3505_, v___x_3504_);
    return v___x_3506_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3511_ = crate::leanh::lean_box(0);
    v___x_3512_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73;
    v___x_3513_ = l_Lean_Expr_const___override(v___x_3512_, v___x_3511_);
    return v___x_3513_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3552_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50,
    );
    v___x_3553_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93;
    v___x_3554_ = l_Lean_Expr_const___override(v___x_3553_, v___x_3552_);
    return v___x_3554_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(
    mut v_e_3555_: *mut crate::leanh::LeanObject,
    mut v_a_3556_: *mut crate::leanh::LeanObject,
    mut v_a_3557_: *mut crate::leanh::LeanObject,
    mut v_a_3558_: *mut crate::leanh::LeanObject,
    mut v_a_3559_: *mut crate::leanh::LeanObject,
    mut v_a_3560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3587_: u8 = 0;
    let mut v_str_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: u8 = 0;
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: u8 = 0;
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: u8 = 0;
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: u8 = 0;
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: u8 = 0;
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: u8 = 0;
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: u8 = 0;
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: u8 = 0;
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: u8 = 0;
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: u8 = 0;
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: u8 = 0;
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3652_: u8 = 0;
    let mut v_str_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v_str_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: u8 = 0;
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: u8 = 0;
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: u8 = 0;
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: u8 = 0;
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3692_: u8 = 0;
    let mut v_unused_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: u8 = 0;
    let mut v___x_3696_: u8 = 0;
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: u8 = 0;
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: u8 = 0;
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: u8 = 0;
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3719_: u8 = 0;
    let mut v_str_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: u8 = 0;
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: u8 = 0;
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u8 = 0;
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: u8 = 0;
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b__pos_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3746_: u8 = 0;
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: u8 = 0;
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_a_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3789_: u8 = 0;
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3793_: u8 = 0;
    let mut v_reuseFailAlloc_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut v_unused_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: u8 = 0;
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: u8 = 0;
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b__pos_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3818_: u8 = 0;
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3836_: u8 = 0;
    let mut v_a_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3840_: u8 = 0;
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3844_: u8 = 0;
    let mut v___x_3845_: u8 = 0;
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3848_: u8 = 0;
    let mut v_unused_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: u8 = 0;
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: u8 = 0;
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: u8 = 0;
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ne__zero_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3878_: u8 = 0;
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3890_: u8 = 0;
    let mut v_a_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3894_: u8 = 0;
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3898_: u8 = 0;
    let mut v_a_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3902_: u8 = 0;
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut v___x_3907_: u8 = 0;
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: u8 = 0;
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: u8 = 0;
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: u8 = 0;
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v_splitNatSub_3935_: u8 = 0;
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: u8 = 0;
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: u8 = 0;
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3977_: u8 = 0;
    let mut v_str_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: u8 = 0;
    let mut v___x_3982_: u8 = 0;
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: u8 = 0;
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: u8 = 0;
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: u8 = 0;
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: u8 = 0;
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: u8 = 0;
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: u8 = 0;
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: u8 = 0;
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: u8 = 0;
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: u8 = 0;
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4034_: u8 = 0;
    let mut v_unused_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: u8 = 0;
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: u8 = 0;
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: u8 = 0;
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: u8 = 0;
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: u8 = 0;
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: u8 = 0;
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: u8 = 0;
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: u8 = 0;
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: u8 = 0;
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4081_: u8 = 0;
    let mut v_unused_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4086_: u8 = 0;
    let mut v_str_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: u8 = 0;
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4113_: u8 = 0;
    let mut v_unused_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3580_ = l_Lean_Expr_getAppFnArgs(v_e_3555_);
                v_fst_3581_ = crate::leanh::lean_ctor_get(v___x_3580_, 0);
                crate::leanh::lean_inc(v_fst_3581_);
                if crate::leanh::lean_obj_tag(v_fst_3581_) == 1 {
                    v_pre_3582_ = crate::leanh::lean_ctor_get(v_fst_3581_, 0);
                    match crate::leanh::lean_obj_tag(v_pre_3582_) {
                        1 => {
                            crate::leanh::lean_inc_ref(v_pre_3582_);
                            v_pre_3583_ = crate::leanh::lean_ctor_get(v_pre_3582_, 0);
                            if crate::leanh::lean_obj_tag(v_pre_3583_) == 0 {
                                v_snd_3584_ = crate::leanh::lean_ctor_get(v___x_3580_, 1);
                                v_isSharedCheck_4081_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3580_)) as u8;
                                if v_isSharedCheck_4081_ == 0 {
                                    v_unused_4082_ = crate::leanh::lean_ctor_get(v___x_3580_, 0);
                                    crate::leanh::lean_dec(v_unused_4082_);
                                    v___x_3586_ = v___x_3580_;
                                    v_isShared_3587_ = v_isSharedCheck_4081_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_snd_3584_);
                                    crate::leanh::lean_dec(v___x_3580_);
                                    v___x_3586_ = crate::leanh::lean_box(0);
                                    v_isShared_3587_ = v_isSharedCheck_4081_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_pre_3582_, 2);
                                crate::leanh::lean_dec_ref_known(v_fst_3581_, 2);
                                crate::leanh::lean_dec_ref(v___x_3580_);
                                state = 3;
                                continue;
                            }
                        }
                        0 => {
                            v_snd_4083_ = crate::leanh::lean_ctor_get(v___x_3580_, 1);
                            v_isSharedCheck_4113_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3580_)) as u8;
                            if v_isSharedCheck_4113_ == 0 {
                                v_unused_4114_ = crate::leanh::lean_ctor_get(v___x_3580_, 0);
                                crate::leanh::lean_dec(v_unused_4114_);
                                v___x_4085_ = v___x_3580_;
                                v_isShared_4086_ = v_isSharedCheck_4113_;
                                state = 45;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_4083_);
                                crate::leanh::lean_dec(v___x_3580_);
                                v___x_4085_ = crate::leanh::lean_box(0);
                                v_isShared_4086_ = v_isSharedCheck_4113_;
                                state = 45;
                                continue;
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec_ref_known(v_fst_3581_, 2);
                            crate::leanh::lean_dec_ref(v___x_3580_);
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_3581_);
                    crate::leanh::lean_dec_ref(v___x_3580_);
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_3563_ = crate::leanh::lean_box(0);
                v___x_3564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3564_, 0, v___x_3563_);
                return v___x_3564_;
            }
            2 => {
                v___x_3566_ = crate::leanh::lean_box(0);
                v___x_3567_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3567_, 0, v___x_3566_);
                return v___x_3567_;
            }
            3 => {
                v___x_3569_ = crate::leanh::lean_box(0);
                v___x_3570_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3570_, 0, v___x_3569_);
                return v___x_3570_;
            }
            4 => {
                v___x_3572_ = crate::leanh::lean_box(0);
                v___x_3573_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3573_, 0, v___x_3572_);
                return v___x_3573_;
            }
            5 => {
                v___x_3575_ = crate::leanh::lean_box(0);
                v___x_3576_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3576_, 0, v___x_3575_);
                return v___x_3576_;
            }
            6 => {
                v___x_3578_ = crate::leanh::lean_box(0);
                v___x_3579_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3579_, 0, v___x_3578_);
                return v___x_3579_;
            }
            7 => {
                v_str_3588_ = crate::leanh::lean_ctor_get(v_fst_3581_, 1);
                crate::leanh::lean_inc_ref(v_str_3588_);
                crate::leanh::lean_dec_ref_known(v_fst_3581_, 2);
                v_str_3589_ = crate::leanh::lean_ctor_get(v_pre_3582_, 1);
                crate::leanh::lean_inc_ref(v_str_3589_);
                crate::leanh::lean_dec_ref_known(v_pre_3582_, 2);
                v___x_3590_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
                v___x_3591_ = lean_string_dec_eq(v_str_3589_, v___x_3590_);
                if v___x_3591_ == 0 {
                    v___x_3592_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
                    v___x_3593_ = lean_string_dec_eq(v_str_3589_, v___x_3592_);
                    if v___x_3593_ == 0 {
                        v___x_3594_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0;
                        v___x_3595_ = lean_string_dec_eq(v_str_3589_, v___x_3594_);
                        if v___x_3595_ == 0 {
                            v___x_3596_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1;
                            v___x_3597_ = lean_string_dec_eq(v_str_3589_, v___x_3596_);
                            if v___x_3597_ == 0 {
                                v___x_3598_ =
                                    l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2;
                                v___x_3599_ = lean_string_dec_eq(v_str_3589_, v___x_3598_);
                                crate::leanh::lean_dec_ref(v_str_3589_);
                                if v___x_3599_ == 0 {
                                    crate::leanh::lean_dec_ref(v_str_3588_);
                                    crate::leanh::lean_del_object(v___x_3586_);
                                    crate::leanh::lean_dec(v_snd_3584_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3600_ =
                                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3;
                                    v___x_3601_ = lean_string_dec_eq(v_str_3588_, v___x_3600_);
                                    crate::leanh::lean_dec_ref(v_str_3588_);
                                    if v___x_3601_ == 0 {
                                        crate::leanh::lean_del_object(v___x_3586_);
                                        crate::leanh::lean_dec(v_snd_3584_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_3602_ = lean_array_get_size(v_snd_3584_);
                                        v___x_3603_ = crate::leanh::lean_unsigned_to_nat(4);
                                        v___x_3604_ = lean_nat_dec_eq(v___x_3602_, v___x_3603_);
                                        if v___x_3604_ == 0 {
                                            crate::leanh::lean_del_object(v___x_3586_);
                                            crate::leanh::lean_dec(v_snd_3584_);
                                            state = 3;
                                            continue;
                                        } else {
                                            v___x_3605_ = crate::leanh::lean_unsigned_to_nat(2);
                                            v___x_3606_ = lean_array_fget(v_snd_3584_, v___x_3605_);
                                            v___x_3607_ = crate::leanh::lean_unsigned_to_nat(3);
                                            v___x_3608_ = lean_array_fget(v_snd_3584_, v___x_3607_);
                                            crate::leanh::lean_dec(v_snd_3584_);
                                            v___x_3609_ = crate::leanh::lean_box(0);
                                            v___x_3610_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6);
                                            crate::leanh::lean_inc(v___x_3608_);
                                            crate::leanh::lean_inc(v___x_3606_);
                                            v___x_3611_ = l_Lean_mkAppB(
                                                v___x_3610_,
                                                v___x_3606_,
                                                v___x_3608_,
                                            );
                                            v___x_3612_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9);
                                            v___x_3613_ = l_Lean_mkAppB(
                                                v___x_3612_,
                                                v___x_3606_,
                                                v___x_3608_,
                                            );
                                            if v_isShared_3587_ == 0 {
                                                crate::leanh::lean_ctor_set_tag(v___x_3586_, 1);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3586_,
                                                    1,
                                                    v___x_3609_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3586_,
                                                    0,
                                                    v___x_3613_,
                                                );
                                                v___x_3615_ = v___x_3586_;
                                                state = 8;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_3618_ =
                                                    crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v_reuseFailAlloc_3618_,
                                                    0,
                                                    v___x_3613_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v_reuseFailAlloc_3618_,
                                                    1,
                                                    v___x_3609_,
                                                );
                                                v___x_3615_ = v_reuseFailAlloc_3618_;
                                                state = 8;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_str_3589_);
                                v___x_3619_ =
                                    l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
                                v___x_3620_ = lean_string_dec_eq(v_str_3588_, v___x_3619_);
                                crate::leanh::lean_dec_ref(v_str_3588_);
                                if v___x_3620_ == 0 {
                                    crate::leanh::lean_del_object(v___x_3586_);
                                    crate::leanh::lean_dec(v_snd_3584_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3621_ = lean_array_get_size(v_snd_3584_);
                                    v___x_3622_ = crate::leanh::lean_unsigned_to_nat(4);
                                    v___x_3623_ = lean_nat_dec_eq(v___x_3621_, v___x_3622_);
                                    if v___x_3623_ == 0 {
                                        crate::leanh::lean_del_object(v___x_3586_);
                                        crate::leanh::lean_dec(v_snd_3584_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_3624_ = crate::leanh::lean_unsigned_to_nat(2);
                                        v___x_3625_ = lean_array_fget(v_snd_3584_, v___x_3624_);
                                        v___x_3626_ = crate::leanh::lean_unsigned_to_nat(3);
                                        v___x_3627_ = lean_array_fget(v_snd_3584_, v___x_3626_);
                                        crate::leanh::lean_dec(v_snd_3584_);
                                        v___x_3628_ = crate::leanh::lean_box(0);
                                        v___x_3629_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13);
                                        crate::leanh::lean_inc(v___x_3627_);
                                        crate::leanh::lean_inc(v___x_3625_);
                                        v___x_3630_ =
                                            l_Lean_mkAppB(v___x_3629_, v___x_3625_, v___x_3627_);
                                        v___x_3631_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16);
                                        v___x_3632_ =
                                            l_Lean_mkAppB(v___x_3631_, v___x_3625_, v___x_3627_);
                                        if v_isShared_3587_ == 0 {
                                            crate::leanh::lean_ctor_set_tag(v___x_3586_, 1);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3586_,
                                                1,
                                                v___x_3628_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3586_,
                                                0,
                                                v___x_3632_,
                                            );
                                            v___x_3634_ = v___x_3586_;
                                            state = 9;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3637_ =
                                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3637_,
                                                0,
                                                v___x_3632_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3637_,
                                                1,
                                                v___x_3628_,
                                            );
                                            v___x_3634_ = v_reuseFailAlloc_3637_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_str_3589_);
                            v___x_3638_ =
                                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17;
                            v___x_3639_ = lean_string_dec_eq(v_str_3588_, v___x_3638_);
                            crate::leanh::lean_dec_ref(v_str_3588_);
                            if v___x_3639_ == 0 {
                                crate::leanh::lean_del_object(v___x_3586_);
                                crate::leanh::lean_dec(v_snd_3584_);
                                state = 3;
                                continue;
                            } else {
                                v___x_3640_ = lean_array_get_size(v_snd_3584_);
                                v___x_3641_ = crate::leanh::lean_unsigned_to_nat(6);
                                v___x_3642_ = lean_nat_dec_eq(v___x_3640_, v___x_3641_);
                                if v___x_3642_ == 0 {
                                    crate::leanh::lean_del_object(v___x_3586_);
                                    crate::leanh::lean_dec(v_snd_3584_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3643_ = crate::leanh::lean_unsigned_to_nat(5);
                                    v___x_3644_ = lean_array_fget(v_snd_3584_, v___x_3643_);
                                    crate::leanh::lean_inc(v___x_3644_);
                                    v___x_3645_ = l_Lean_Expr_getAppFnArgs(v___x_3644_);
                                    v_fst_3646_ = crate::leanh::lean_ctor_get(v___x_3645_, 0);
                                    crate::leanh::lean_inc(v_fst_3646_);
                                    if crate::leanh::lean_obj_tag(v_fst_3646_) == 1 {
                                        v_pre_3647_ = crate::leanh::lean_ctor_get(v_fst_3646_, 0);
                                        crate::leanh::lean_inc(v_pre_3647_);
                                        if crate::leanh::lean_obj_tag(v_pre_3647_) == 1 {
                                            v_pre_3648_ =
                                                crate::leanh::lean_ctor_get(v_pre_3647_, 0);
                                            if crate::leanh::lean_obj_tag(v_pre_3648_) == 0 {
                                                v_snd_3649_ =
                                                    crate::leanh::lean_ctor_get(v___x_3645_, 1);
                                                v_isSharedCheck_3848_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_3645_))
                                                        as u8;
                                                if v_isSharedCheck_3848_ == 0 {
                                                    v_unused_3849_ =
                                                        crate::leanh::lean_ctor_get(v___x_3645_, 0);
                                                    crate::leanh::lean_dec(v_unused_3849_);
                                                    v___x_3651_ = v___x_3645_;
                                                    v_isShared_3652_ = v_isSharedCheck_3848_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_snd_3649_);
                                                    crate::leanh::lean_dec(v___x_3645_);
                                                    v___x_3651_ = crate::leanh::lean_box(0);
                                                    v_isShared_3652_ = v_isSharedCheck_3848_;
                                                    state = 10;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref_known(v_pre_3647_, 2);
                                                crate::leanh::lean_dec_ref_known(v_fst_3646_, 2);
                                                crate::leanh::lean_dec_ref(v___x_3645_);
                                                crate::leanh::lean_dec(v___x_3644_);
                                                crate::leanh::lean_del_object(v___x_3586_);
                                                crate::leanh::lean_dec(v_snd_3584_);
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref_known(v_fst_3646_, 2);
                                            crate::leanh::lean_dec(v_pre_3647_);
                                            crate::leanh::lean_dec_ref(v___x_3645_);
                                            crate::leanh::lean_dec(v___x_3644_);
                                            crate::leanh::lean_del_object(v___x_3586_);
                                            crate::leanh::lean_dec(v_snd_3584_);
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_fst_3646_);
                                        crate::leanh::lean_dec_ref(v___x_3645_);
                                        crate::leanh::lean_dec(v___x_3644_);
                                        crate::leanh::lean_del_object(v___x_3586_);
                                        crate::leanh::lean_dec(v_snd_3584_);
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_str_3589_);
                        v___x_3850_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
                        v___x_3851_ = lean_string_dec_eq(v_str_3588_, v___x_3850_);
                        crate::leanh::lean_dec_ref(v_str_3588_);
                        if v___x_3851_ == 0 {
                            crate::leanh::lean_del_object(v___x_3586_);
                            crate::leanh::lean_dec(v_snd_3584_);
                            state = 3;
                            continue;
                        } else {
                            v___x_3852_ = lean_array_get_size(v_snd_3584_);
                            v___x_3853_ = crate::leanh::lean_unsigned_to_nat(6);
                            v___x_3854_ = lean_nat_dec_eq(v___x_3852_, v___x_3853_);
                            if v___x_3854_ == 0 {
                                crate::leanh::lean_del_object(v___x_3586_);
                                crate::leanh::lean_dec(v_snd_3584_);
                                state = 3;
                                continue;
                            } else {
                                v___x_3855_ = crate::leanh::lean_unsigned_to_nat(5);
                                v___x_3856_ = lean_array_fget(v_snd_3584_, v___x_3855_);
                                crate::leanh::lean_inc(v___x_3856_);
                                v___x_3857_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_3856_);
                                if crate::leanh::lean_obj_tag(v___x_3857_) == 0 {
                                    crate::leanh::lean_dec(v___x_3856_);
                                    crate::leanh::lean_del_object(v___x_3586_);
                                    crate::leanh::lean_dec(v_snd_3584_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_3858_ = crate::leanh::lean_ctor_get(v___x_3857_, 0);
                                    crate::leanh::lean_inc(v_val_3858_);
                                    crate::leanh::lean_dec_ref_known(v___x_3857_, 1);
                                    v___x_3859_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v___x_3860_ = lean_nat_dec_eq(v_val_3858_, v___x_3859_);
                                    crate::leanh::lean_dec(v_val_3858_);
                                    if v___x_3860_ == 0 {
                                        v___x_3861_ = crate::leanh::lean_unsigned_to_nat(4);
                                        v___x_3862_ = lean_array_fget(v_snd_3584_, v___x_3861_);
                                        crate::leanh::lean_dec(v_snd_3584_);
                                        v___x_3863_ = crate::leanh::lean_box(0);
                                        v___x_3864_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68);
                                        v___x_3865_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once), _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
                                        v___x_3907_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
                                        if v___x_3907_ == 0 {
                                            v___x_3908_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
                                            v___y_3867_ = v___x_3908_;
                                            state = 30;
                                            continue;
                                        } else {
                                            v___x_3909_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
                                            v___y_3867_ = v___x_3909_;
                                            state = 30;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_3856_);
                                        crate::leanh::lean_del_object(v___x_3586_);
                                        crate::leanh::lean_dec(v_snd_3584_);
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_str_3589_);
                    v___x_3910_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                    v___x_3911_ = lean_string_dec_eq(v_str_3588_, v___x_3910_);
                    crate::leanh::lean_dec_ref(v_str_3588_);
                    if v___x_3911_ == 0 {
                        crate::leanh::lean_del_object(v___x_3586_);
                        crate::leanh::lean_dec(v_snd_3584_);
                        state = 3;
                        continue;
                    } else {
                        v___x_3912_ = lean_array_get_size(v_snd_3584_);
                        v___x_3913_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_3914_ = lean_nat_dec_eq(v___x_3912_, v___x_3913_);
                        if v___x_3914_ == 0 {
                            crate::leanh::lean_del_object(v___x_3586_);
                            crate::leanh::lean_dec(v_snd_3584_);
                            state = 3;
                            continue;
                        } else {
                            v___x_3915_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_3916_ = lean_array_fget_borrowed(v_snd_3584_, v___x_3915_);
                            if crate::leanh::lean_obj_tag(v___x_3916_) == 4 {
                                v_declName_3917_ = crate::leanh::lean_ctor_get(v___x_3916_, 0);
                                if crate::leanh::lean_obj_tag(v_declName_3917_) == 1 {
                                    v_pre_3918_ = crate::leanh::lean_ctor_get(v_declName_3917_, 0);
                                    if crate::leanh::lean_obj_tag(v_pre_3918_) == 0 {
                                        v_us_3919_ = crate::leanh::lean_ctor_get(v___x_3916_, 1);
                                        crate::leanh::lean_inc(v_us_3919_);
                                        v_str_3920_ =
                                            crate::leanh::lean_ctor_get(v_declName_3917_, 1);
                                        v___x_3921_ =
                                            l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
                                        v___x_3934_ = lean_string_dec_eq(v_str_3920_, v___x_3921_);
                                        if v___x_3934_ == 0 {
                                            crate::leanh::lean_dec(v_us_3919_);
                                            crate::leanh::lean_del_object(v___x_3586_);
                                            crate::leanh::lean_dec(v_snd_3584_);
                                            state = 3;
                                            continue;
                                        } else {
                                            if crate::leanh::lean_obj_tag(v_us_3919_) == 0 {
                                                v_splitNatSub_3935_ =
                                                    crate::leanh::lean_ctor_get_uint8(
                                                        v_a_3556_, 1 as u32,
                                                    );
                                                v___x_3936_ = crate::leanh::lean_unsigned_to_nat(2);
                                                v___x_3937_ =
                                                    lean_array_fget(v_snd_3584_, v___x_3936_);
                                                crate::leanh::lean_dec(v_snd_3584_);
                                                v___x_3938_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78;
                                                v___x_3939_ = l_Lean_Expr_const___override(
                                                    v___x_3938_,
                                                    v_us_3919_,
                                                );
                                                crate::leanh::lean_inc(v___x_3937_);
                                                v___x_3940_ = l_Lean_Expr_app___override(
                                                    v___x_3939_,
                                                    v___x_3937_,
                                                );
                                                v___x_3941_ = crate::leanh::lean_box(0);
                                                v_r_3942_ =
                                                    crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v_r_3942_,
                                                    0,
                                                    v___x_3940_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v_r_3942_,
                                                    1,
                                                    v___x_3941_,
                                                );
                                                if v_splitNatSub_3935_ == 1 {
                                                    v___x_3970_ =
                                                        l_Lean_Expr_getAppFnArgs(v___x_3937_);
                                                    v_fst_3971_ =
                                                        crate::leanh::lean_ctor_get(v___x_3970_, 0);
                                                    crate::leanh::lean_inc(v_fst_3971_);
                                                    if crate::leanh::lean_obj_tag(v_fst_3971_) == 1
                                                    {
                                                        v_pre_3972_ = crate::leanh::lean_ctor_get(
                                                            v_fst_3971_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_pre_3972_);
                                                        if crate::leanh::lean_obj_tag(v_pre_3972_)
                                                            == 1
                                                        {
                                                            v_pre_3973_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_pre_3972_,
                                                                    0,
                                                                );
                                                            if crate::leanh::lean_obj_tag(
                                                                v_pre_3973_,
                                                            ) == 0
                                                            {
                                                                v_snd_3974_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_3970_,
                                                                        1,
                                                                    );
                                                                v_isSharedCheck_4034_ = (!crate::leanh::lean_is_exclusive(v___x_3970_)) as u8;
                                                                if v_isSharedCheck_4034_ == 0 {
                                                                    v_unused_4035_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_3970_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_dec(
                                                                        v_unused_4035_,
                                                                    );
                                                                    v___x_3976_ = v___x_3970_;
                                                                    v_isShared_3977_ =
                                                                        v_isSharedCheck_4034_;
                                                                    state = 43;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_snd_3974_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_3970_,
                                                                    );
                                                                    v___x_3976_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_3977_ =
                                                                        v_isSharedCheck_4034_;
                                                                    state = 43;
                                                                    continue;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_pre_3972_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_fst_3971_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_3970_,
                                                                );
                                                                crate::leanh::lean_del_object(
                                                                    v___x_3586_,
                                                                );
                                                                v___x_4036_ =
                                                                    crate::leanh::lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_4036_,
                                                                    0,
                                                                    v_r_3942_,
                                                                );
                                                                return v___x_4036_;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_fst_3971_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_dec(v_pre_3972_);
                                                            crate::leanh::lean_dec_ref(v___x_3970_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_3586_,
                                                            );
                                                            v___x_4037_ =
                                                                crate::leanh::lean_alloc_ctor(
                                                                    0,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_4037_,
                                                                0,
                                                                v_r_3942_,
                                                            );
                                                            return v___x_4037_;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_fst_3971_);
                                                        crate::leanh::lean_dec_ref(v___x_3970_);
                                                        crate::leanh::lean_del_object(v___x_3586_);
                                                        v___x_4038_ = crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_4038_,
                                                            0,
                                                            v_r_3942_,
                                                        );
                                                        return v___x_4038_;
                                                    }
                                                } else {
                                                    v___x_4039_ =
                                                        l_Lean_Expr_getAppFnArgs(v___x_3937_);
                                                    v_fst_4040_ =
                                                        crate::leanh::lean_ctor_get(v___x_4039_, 0);
                                                    crate::leanh::lean_inc(v_fst_4040_);
                                                    if crate::leanh::lean_obj_tag(v_fst_4040_) == 1
                                                    {
                                                        v_pre_4041_ = crate::leanh::lean_ctor_get(
                                                            v_fst_4040_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_pre_4041_);
                                                        if crate::leanh::lean_obj_tag(v_pre_4041_)
                                                            == 1
                                                        {
                                                            v_pre_4042_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_pre_4041_,
                                                                    0,
                                                                );
                                                            if crate::leanh::lean_obj_tag(
                                                                v_pre_4042_,
                                                            ) == 0
                                                            {
                                                                v_snd_4043_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_4039_,
                                                                        1,
                                                                    );
                                                                crate::leanh::lean_inc(v_snd_4043_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_4039_,
                                                                );
                                                                v_str_4044_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_fst_4040_,
                                                                        1,
                                                                    );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_str_4044_,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_fst_4040_,
                                                                    2,
                                                                );
                                                                v_str_4045_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_pre_4041_,
                                                                        1,
                                                                    );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_str_4045_,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_pre_4041_,
                                                                    2,
                                                                );
                                                                v___x_4046_ = lean_string_dec_eq(
                                                                    v_str_4045_,
                                                                    v___x_3921_,
                                                                );
                                                                if v___x_4046_ == 0 {
                                                                    crate::leanh::lean_del_object(
                                                                        v___x_3586_,
                                                                    );
                                                                    v___x_4047_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82;
                                                                    v___x_4048_ =
                                                                        lean_string_dec_eq(
                                                                            v_str_4045_,
                                                                            v___x_4047_,
                                                                        );
                                                                    if v___x_4048_ == 0 {
                                                                        v___x_4049_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79;
                                                                        v___x_4050_ =
                                                                            lean_string_dec_eq(
                                                                                v_str_4045_,
                                                                                v___x_4049_,
                                                                            );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_str_4045_,
                                                                        );
                                                                        if v___x_4050_ == 0 {
                                                                            crate::leanh::lean_dec_ref(v_str_4044_);
                                                                            crate::leanh::lean_dec(
                                                                                v_snd_4043_,
                                                                            );
                                                                            v___x_4051_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                            crate::leanh::lean_ctor_set(v___x_4051_, 0, v_r_3942_);
                                                                            return v___x_4051_;
                                                                        } else {
                                                                            v___x_4052_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86;
                                                                            v___x_4053_ =
                                                                                lean_string_dec_eq(
                                                                                    v_str_4044_,
                                                                                    v___x_4052_,
                                                                                );
                                                                            crate::leanh::lean_dec_ref(v_str_4044_);
                                                                            if v___x_4053_ == 0 {
                                                                                crate::leanh::lean_dec(v_snd_4043_);
                                                                                v___x_4054_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                                crate::leanh::lean_ctor_set(v___x_4054_, 0, v_r_3942_);
                                                                                return v___x_4054_;
                                                                            } else {
                                                                                v___x_4055_ = lean_array_get_size(v_snd_4043_);
                                                                                v___x_4056_ =
                                                                                    lean_nat_dec_eq(
                                                                                        v___x_4055_,
                                                                                        v___x_3936_,
                                                                                    );
                                                                                if v___x_4056_ == 0
                                                                                {
                                                                                    crate::leanh::lean_dec(v_snd_4043_);
                                                                                    v___x_4057_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                                    crate::leanh::lean_ctor_set(v___x_4057_, 0, v_r_3942_);
                                                                                    return v___x_4057_;
                                                                                } else {
                                                                                    v___x_4058_ = lean_array_fget(v_snd_4043_, v___x_3915_);
                                                                                    v___x_4059_ = crate::leanh::lean_unsigned_to_nat(1);
                                                                                    v___x_4060_ = lean_array_fget(v_snd_4043_, v___x_4059_);
                                                                                    crate::leanh::lean_dec(v_snd_4043_);
                                                                                    v_n_3944_ =
                                                                                        v___x_4058_;
                                                                                    v_x_3945_ =
                                                                                        v___x_4060_;
                                                                                    state = 40;
                                                                                    continue;
                                                                                }
                                                                            }
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_str_4045_,
                                                                        );
                                                                        v___x_4061_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87;
                                                                        v___x_4062_ =
                                                                            lean_string_dec_eq(
                                                                                v_str_4044_,
                                                                                v___x_4061_,
                                                                            );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_str_4044_,
                                                                        );
                                                                        if v___x_4062_ == 0 {
                                                                            crate::leanh::lean_dec(
                                                                                v_snd_4043_,
                                                                            );
                                                                            v___x_4063_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                            crate::leanh::lean_ctor_set(v___x_4063_, 0, v_r_3942_);
                                                                            return v___x_4063_;
                                                                        } else {
                                                                            v___x_4064_ =
                                                                                lean_array_get_size(
                                                                                    v_snd_4043_,
                                                                                );
                                                                            v___x_4065_ =
                                                                                lean_nat_dec_eq(
                                                                                    v___x_4064_,
                                                                                    v___x_3936_,
                                                                                );
                                                                            if v___x_4065_ == 0 {
                                                                                crate::leanh::lean_dec(v_snd_4043_);
                                                                                v___x_4066_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                                crate::leanh::lean_ctor_set(v___x_4066_, 0, v_r_3942_);
                                                                                return v___x_4066_;
                                                                            } else {
                                                                                v___x_4067_ =
                                                                                    lean_array_fget(
                                                                                        v_snd_4043_,
                                                                                        v___x_3915_,
                                                                                    );
                                                                                v___x_4068_ = crate::leanh::lean_unsigned_to_nat(1);
                                                                                v___x_4069_ =
                                                                                    lean_array_fget(
                                                                                        v_snd_4043_,
                                                                                        v___x_4068_,
                                                                                    );
                                                                                crate::leanh::lean_dec(v_snd_4043_);
                                                                                v_n_3954_ =
                                                                                    v___x_4067_;
                                                                                v_i_3955_ =
                                                                                    v___x_4069_;
                                                                                state = 41;
                                                                                continue;
                                                                            }
                                                                        }
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_str_4045_,
                                                                    );
                                                                    v___x_4070_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88;
                                                                    v___x_4071_ =
                                                                        lean_string_dec_eq(
                                                                            v_str_4044_,
                                                                            v___x_4070_,
                                                                        );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_str_4044_,
                                                                    );
                                                                    if v___x_4071_ == 0 {
                                                                        crate::leanh::lean_dec(
                                                                            v_snd_4043_,
                                                                        );
                                                                        crate::leanh::lean_del_object(v___x_3586_);
                                                                        v___x_4072_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                        crate::leanh::lean_ctor_set(
                                                                            v___x_4072_,
                                                                            0,
                                                                            v_r_3942_,
                                                                        );
                                                                        return v___x_4072_;
                                                                    } else {
                                                                        v___x_4073_ =
                                                                            lean_array_get_size(
                                                                                v_snd_4043_,
                                                                            );
                                                                        v___x_4074_ = crate::leanh::lean_unsigned_to_nat(1);
                                                                        v___x_4075_ =
                                                                            lean_nat_dec_eq(
                                                                                v___x_4073_,
                                                                                v___x_4074_,
                                                                            );
                                                                        if v___x_4075_ == 0 {
                                                                            crate::leanh::lean_dec(
                                                                                v_snd_4043_,
                                                                            );
                                                                            crate::leanh::lean_del_object(v___x_3586_);
                                                                            v___x_4076_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                            crate::leanh::lean_ctor_set(v___x_4076_, 0, v_r_3942_);
                                                                            return v___x_4076_;
                                                                        } else {
                                                                            v___x_4077_ =
                                                                                lean_array_fget(
                                                                                    v_snd_4043_,
                                                                                    v___x_3915_,
                                                                                );
                                                                            crate::leanh::lean_dec(
                                                                                v_snd_4043_,
                                                                            );
                                                                            v_x_3964_ = v___x_4077_;
                                                                            state = 42;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_pre_4041_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_fst_4040_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_4039_,
                                                                );
                                                                crate::leanh::lean_del_object(
                                                                    v___x_3586_,
                                                                );
                                                                v___x_4078_ =
                                                                    crate::leanh::lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_4078_,
                                                                    0,
                                                                    v_r_3942_,
                                                                );
                                                                return v___x_4078_;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_fst_4040_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_dec(v_pre_4041_);
                                                            crate::leanh::lean_dec_ref(v___x_4039_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_3586_,
                                                            );
                                                            v___x_4079_ =
                                                                crate::leanh::lean_alloc_ctor(
                                                                    0,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_4079_,
                                                                0,
                                                                v_r_3942_,
                                                            );
                                                            return v___x_4079_;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_fst_4040_);
                                                        crate::leanh::lean_dec_ref(v___x_4039_);
                                                        crate::leanh::lean_del_object(v___x_3586_);
                                                        v___x_4080_ = crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_4080_,
                                                            0,
                                                            v_r_3942_,
                                                        );
                                                        return v___x_4080_;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_us_3919_);
                                                crate::leanh::lean_del_object(v___x_3586_);
                                                crate::leanh::lean_dec(v_snd_3584_);
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_del_object(v___x_3586_);
                                        crate::leanh::lean_dec(v_snd_3584_);
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_3586_);
                                    crate::leanh::lean_dec(v_snd_3584_);
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_3586_);
                                crate::leanh::lean_dec(v_snd_3584_);
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            8 => {
                v___x_3616_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3616_, 0, v___x_3611_);
                crate::leanh::lean_ctor_set(v___x_3616_, 1, v___x_3615_);
                v___x_3617_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3617_, 0, v___x_3616_);
                return v___x_3617_;
            }
            9 => {
                v___x_3635_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3635_, 0, v___x_3630_);
                crate::leanh::lean_ctor_set(v___x_3635_, 1, v___x_3634_);
                v___x_3636_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3636_, 0, v___x_3635_);
                return v___x_3636_;
            }
            10 => {
                v_str_3653_ = crate::leanh::lean_ctor_get(v_fst_3646_, 1);
                crate::leanh::lean_inc_ref(v_str_3653_);
                crate::leanh::lean_dec_ref_known(v_fst_3646_, 2);
                v_str_3654_ = crate::leanh::lean_ctor_get(v_pre_3647_, 1);
                crate::leanh::lean_inc_ref(v_str_3654_);
                crate::leanh::lean_dec_ref_known(v_pre_3647_, 2);
                v___x_3655_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3656_ = lean_array_fget(v_snd_3584_, v___x_3655_);
                crate::leanh::lean_dec(v_snd_3584_);
                v___x_3694_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
                v___x_3695_ = lean_string_dec_eq(v_str_3654_, v___x_3694_);
                if v___x_3695_ == 0 {
                    v___x_3696_ = lean_string_dec_eq(v_str_3654_, v___x_3590_);
                    crate::leanh::lean_dec_ref(v_str_3654_);
                    if v___x_3696_ == 0 {
                        crate::leanh::lean_dec(v___x_3656_);
                        crate::leanh::lean_dec_ref(v_str_3653_);
                        crate::leanh::lean_del_object(v___x_3651_);
                        crate::leanh::lean_dec(v_snd_3649_);
                        crate::leanh::lean_dec(v___x_3644_);
                        crate::leanh::lean_del_object(v___x_3586_);
                        state = 4;
                        continue;
                    } else {
                        v___x_3697_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                        v___x_3698_ = lean_string_dec_eq(v_str_3653_, v___x_3697_);
                        crate::leanh::lean_dec_ref(v_str_3653_);
                        if v___x_3698_ == 0 {
                            crate::leanh::lean_dec(v___x_3656_);
                            crate::leanh::lean_del_object(v___x_3651_);
                            crate::leanh::lean_dec(v_snd_3649_);
                            crate::leanh::lean_dec(v___x_3644_);
                            crate::leanh::lean_del_object(v___x_3586_);
                            state = 4;
                            continue;
                        } else {
                            v___x_3699_ = lean_array_get_size(v_snd_3649_);
                            v___x_3700_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_3701_ = lean_nat_dec_eq(v___x_3699_, v___x_3700_);
                            if v___x_3701_ == 0 {
                                crate::leanh::lean_dec(v___x_3656_);
                                crate::leanh::lean_del_object(v___x_3651_);
                                crate::leanh::lean_dec(v_snd_3649_);
                                crate::leanh::lean_dec(v___x_3644_);
                                crate::leanh::lean_del_object(v___x_3586_);
                                state = 4;
                                continue;
                            } else {
                                v___x_3702_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_3703_ = lean_array_fget_borrowed(v_snd_3649_, v___x_3702_);
                                if crate::leanh::lean_obj_tag(v___x_3703_) == 4 {
                                    v_declName_3704_ = crate::leanh::lean_ctor_get(v___x_3703_, 0);
                                    if crate::leanh::lean_obj_tag(v_declName_3704_) == 1 {
                                        v_pre_3705_ =
                                            crate::leanh::lean_ctor_get(v_declName_3704_, 0);
                                        if crate::leanh::lean_obj_tag(v_pre_3705_) == 0 {
                                            v_us_3706_ =
                                                crate::leanh::lean_ctor_get(v___x_3703_, 1);
                                            crate::leanh::lean_inc(v_us_3706_);
                                            v_str_3707_ =
                                                crate::leanh::lean_ctor_get(v_declName_3704_, 1);
                                            v___x_3708_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
                                            v___x_3709_ =
                                                lean_string_dec_eq(v_str_3707_, v___x_3708_);
                                            if v___x_3709_ == 0 {
                                                crate::leanh::lean_dec(v_us_3706_);
                                                crate::leanh::lean_dec(v___x_3656_);
                                                crate::leanh::lean_del_object(v___x_3651_);
                                                crate::leanh::lean_dec(v_snd_3649_);
                                                crate::leanh::lean_dec(v___x_3644_);
                                                crate::leanh::lean_del_object(v___x_3586_);
                                                state = 4;
                                                continue;
                                            } else {
                                                if crate::leanh::lean_obj_tag(v_us_3706_) == 0 {
                                                    v___x_3710_ =
                                                        crate::leanh::lean_unsigned_to_nat(2);
                                                    v___x_3711_ =
                                                        lean_array_fget(v_snd_3649_, v___x_3710_);
                                                    crate::leanh::lean_dec(v_snd_3649_);
                                                    crate::leanh::lean_inc(v___x_3711_);
                                                    v___x_3712_ =
                                                        l_Lean_Expr_getAppFnArgs(v___x_3711_);
                                                    v_fst_3713_ =
                                                        crate::leanh::lean_ctor_get(v___x_3712_, 0);
                                                    crate::leanh::lean_inc(v_fst_3713_);
                                                    if crate::leanh::lean_obj_tag(v_fst_3713_) == 1
                                                    {
                                                        v_pre_3714_ = crate::leanh::lean_ctor_get(
                                                            v_fst_3713_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_pre_3714_);
                                                        if crate::leanh::lean_obj_tag(v_pre_3714_)
                                                            == 1
                                                        {
                                                            v_pre_3715_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_pre_3714_,
                                                                    0,
                                                                );
                                                            if crate::leanh::lean_obj_tag(
                                                                v_pre_3715_,
                                                            ) == 0
                                                            {
                                                                v_snd_3716_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_3712_,
                                                                        1,
                                                                    );
                                                                v_isSharedCheck_3795_ = (!crate::leanh::lean_is_exclusive(v___x_3712_)) as u8;
                                                                if v_isSharedCheck_3795_ == 0 {
                                                                    v_unused_3796_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_3712_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_dec(
                                                                        v_unused_3796_,
                                                                    );
                                                                    v___x_3718_ = v___x_3712_;
                                                                    v_isShared_3719_ =
                                                                        v_isSharedCheck_3795_;
                                                                    state = 14;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_snd_3716_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_3712_,
                                                                    );
                                                                    v___x_3718_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_3719_ =
                                                                        v_isSharedCheck_3795_;
                                                                    state = 14;
                                                                    continue;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_pre_3714_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_fst_3713_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_3712_,
                                                                );
                                                                crate::leanh::lean_dec(v___x_3711_);
                                                                crate::leanh::lean_del_object(
                                                                    v___x_3651_,
                                                                );
                                                                crate::leanh::lean_del_object(
                                                                    v___x_3586_,
                                                                );
                                                                state = 11;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(v_pre_3714_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_fst_3713_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_dec_ref(v___x_3712_);
                                                            crate::leanh::lean_dec(v___x_3711_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_3651_,
                                                            );
                                                            crate::leanh::lean_del_object(
                                                                v___x_3586_,
                                                            );
                                                            state = 11;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_fst_3713_);
                                                        crate::leanh::lean_dec_ref(v___x_3712_);
                                                        crate::leanh::lean_dec(v___x_3711_);
                                                        crate::leanh::lean_del_object(v___x_3651_);
                                                        crate::leanh::lean_del_object(v___x_3586_);
                                                        state = 11;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_us_3706_);
                                                    crate::leanh::lean_dec(v___x_3656_);
                                                    crate::leanh::lean_del_object(v___x_3651_);
                                                    crate::leanh::lean_dec(v_snd_3649_);
                                                    crate::leanh::lean_dec(v___x_3644_);
                                                    crate::leanh::lean_del_object(v___x_3586_);
                                                    state = 4;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v___x_3656_);
                                            crate::leanh::lean_del_object(v___x_3651_);
                                            crate::leanh::lean_dec(v_snd_3649_);
                                            crate::leanh::lean_dec(v___x_3644_);
                                            crate::leanh::lean_del_object(v___x_3586_);
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_3656_);
                                        crate::leanh::lean_del_object(v___x_3651_);
                                        crate::leanh::lean_dec(v_snd_3649_);
                                        crate::leanh::lean_dec(v___x_3644_);
                                        crate::leanh::lean_del_object(v___x_3586_);
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_3656_);
                                    crate::leanh::lean_del_object(v___x_3651_);
                                    crate::leanh::lean_dec(v_snd_3649_);
                                    crate::leanh::lean_dec(v___x_3644_);
                                    crate::leanh::lean_del_object(v___x_3586_);
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_str_3654_);
                    v___x_3797_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
                    v___x_3798_ = lean_string_dec_eq(v_str_3653_, v___x_3797_);
                    crate::leanh::lean_dec_ref(v_str_3653_);
                    if v___x_3798_ == 0 {
                        crate::leanh::lean_dec(v___x_3656_);
                        crate::leanh::lean_del_object(v___x_3651_);
                        crate::leanh::lean_dec(v_snd_3649_);
                        crate::leanh::lean_dec(v___x_3644_);
                        crate::leanh::lean_del_object(v___x_3586_);
                        state = 4;
                        continue;
                    } else {
                        v___x_3799_ = lean_array_get_size(v_snd_3649_);
                        v___x_3800_ = lean_nat_dec_eq(v___x_3799_, v___x_3641_);
                        if v___x_3800_ == 0 {
                            crate::leanh::lean_dec(v___x_3656_);
                            crate::leanh::lean_del_object(v___x_3651_);
                            crate::leanh::lean_dec(v_snd_3649_);
                            crate::leanh::lean_dec(v___x_3644_);
                            crate::leanh::lean_del_object(v___x_3586_);
                            state = 4;
                            continue;
                        } else {
                            v___x_3801_ = lean_array_fget(v_snd_3649_, v___x_3655_);
                            crate::leanh::lean_inc(v___x_3801_);
                            v___x_3802_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_3801_);
                            if crate::leanh::lean_obj_tag(v___x_3802_) == 0 {
                                crate::leanh::lean_dec(v___x_3801_);
                                crate::leanh::lean_dec(v___x_3656_);
                                crate::leanh::lean_del_object(v___x_3651_);
                                crate::leanh::lean_dec(v_snd_3649_);
                                crate::leanh::lean_dec(v___x_3644_);
                                crate::leanh::lean_del_object(v___x_3586_);
                                state = 2;
                                continue;
                            } else {
                                v_val_3803_ = crate::leanh::lean_ctor_get(v___x_3802_, 0);
                                crate::leanh::lean_inc(v_val_3803_);
                                crate::leanh::lean_dec_ref_known(v___x_3802_, 1);
                                v___x_3804_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_3805_ = lean_nat_dec_eq(v_val_3803_, v___x_3804_);
                                crate::leanh::lean_dec(v_val_3803_);
                                if v___x_3805_ == 0 {
                                    v___x_3806_ = lean_array_fget(v_snd_3649_, v___x_3643_);
                                    crate::leanh::lean_dec(v_snd_3649_);
                                    v___x_3807_ = crate::leanh::lean_box(0);
                                    v___x_3808_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51);
                                    v___x_3809_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once), _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
                                    v___x_3810_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54);
                                    v___x_3845_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
                                    if v___x_3845_ == 0 {
                                        v___x_3846_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
                                        v___y_3812_ = v___x_3846_;
                                        state = 23;
                                        continue;
                                    } else {
                                        v___x_3847_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
                                        v___y_3812_ = v___x_3847_;
                                        state = 23;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_3801_);
                                    crate::leanh::lean_dec(v___x_3656_);
                                    crate::leanh::lean_del_object(v___x_3651_);
                                    crate::leanh::lean_dec(v_snd_3649_);
                                    crate::leanh::lean_dec(v___x_3644_);
                                    crate::leanh::lean_del_object(v___x_3586_);
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            11 => {
                v___x_3658_ = l_Lean_Expr_getAppFnArgs(v___x_3656_);
                v_fst_3659_ = crate::leanh::lean_ctor_get(v___x_3658_, 0);
                crate::leanh::lean_inc(v_fst_3659_);
                if crate::leanh::lean_obj_tag(v_fst_3659_) == 1 {
                    v_pre_3660_ = crate::leanh::lean_ctor_get(v_fst_3659_, 0);
                    crate::leanh::lean_inc(v_pre_3660_);
                    if crate::leanh::lean_obj_tag(v_pre_3660_) == 1 {
                        v_pre_3661_ = crate::leanh::lean_ctor_get(v_pre_3660_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_3661_) == 0 {
                            v_snd_3662_ = crate::leanh::lean_ctor_get(v___x_3658_, 1);
                            v_isSharedCheck_3692_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3658_)) as u8;
                            if v_isSharedCheck_3692_ == 0 {
                                v_unused_3693_ = crate::leanh::lean_ctor_get(v___x_3658_, 0);
                                crate::leanh::lean_dec(v_unused_3693_);
                                v___x_3664_ = v___x_3658_;
                                v_isShared_3665_ = v_isSharedCheck_3692_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_3662_);
                                crate::leanh::lean_dec(v___x_3658_);
                                v___x_3664_ = crate::leanh::lean_box(0);
                                v_isShared_3665_ = v_isSharedCheck_3692_;
                                state = 12;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_pre_3660_, 2);
                            crate::leanh::lean_dec_ref_known(v_fst_3659_, 2);
                            crate::leanh::lean_dec_ref(v___x_3658_);
                            crate::leanh::lean_dec(v___x_3644_);
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_fst_3659_, 2);
                        crate::leanh::lean_dec(v_pre_3660_);
                        crate::leanh::lean_dec_ref(v___x_3658_);
                        crate::leanh::lean_dec(v___x_3644_);
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_3659_);
                    crate::leanh::lean_dec_ref(v___x_3658_);
                    crate::leanh::lean_dec(v___x_3644_);
                    state = 5;
                    continue;
                }
            }
            12 => {
                v_str_3666_ = crate::leanh::lean_ctor_get(v_fst_3659_, 1);
                crate::leanh::lean_inc_ref(v_str_3666_);
                crate::leanh::lean_dec_ref_known(v_fst_3659_, 2);
                v_str_3667_ = crate::leanh::lean_ctor_get(v_pre_3660_, 1);
                crate::leanh::lean_inc_ref(v_str_3667_);
                crate::leanh::lean_dec_ref_known(v_pre_3660_, 2);
                v___x_3668_ = lean_string_dec_eq(v_str_3667_, v___x_3590_);
                crate::leanh::lean_dec_ref(v_str_3667_);
                if v___x_3668_ == 0 {
                    crate::leanh::lean_dec_ref(v_str_3666_);
                    crate::leanh::lean_del_object(v___x_3664_);
                    crate::leanh::lean_dec(v_snd_3662_);
                    crate::leanh::lean_dec(v___x_3644_);
                    state = 5;
                    continue;
                } else {
                    v___x_3669_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                    v___x_3670_ = lean_string_dec_eq(v_str_3666_, v___x_3669_);
                    crate::leanh::lean_dec_ref(v_str_3666_);
                    if v___x_3670_ == 0 {
                        crate::leanh::lean_del_object(v___x_3664_);
                        crate::leanh::lean_dec(v_snd_3662_);
                        crate::leanh::lean_dec(v___x_3644_);
                        state = 5;
                        continue;
                    } else {
                        v___x_3671_ = lean_array_get_size(v_snd_3662_);
                        v___x_3672_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_3673_ = lean_nat_dec_eq(v___x_3671_, v___x_3672_);
                        if v___x_3673_ == 0 {
                            crate::leanh::lean_del_object(v___x_3664_);
                            crate::leanh::lean_dec(v_snd_3662_);
                            crate::leanh::lean_dec(v___x_3644_);
                            state = 5;
                            continue;
                        } else {
                            v___x_3674_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_3675_ = lean_array_fget_borrowed(v_snd_3662_, v___x_3674_);
                            if crate::leanh::lean_obj_tag(v___x_3675_) == 4 {
                                v_declName_3676_ = crate::leanh::lean_ctor_get(v___x_3675_, 0);
                                if crate::leanh::lean_obj_tag(v_declName_3676_) == 1 {
                                    v_pre_3677_ = crate::leanh::lean_ctor_get(v_declName_3676_, 0);
                                    if crate::leanh::lean_obj_tag(v_pre_3677_) == 0 {
                                        v_us_3678_ = crate::leanh::lean_ctor_get(v___x_3675_, 1);
                                        crate::leanh::lean_inc(v_us_3678_);
                                        v_str_3679_ =
                                            crate::leanh::lean_ctor_get(v_declName_3676_, 1);
                                        v___x_3680_ =
                                            l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
                                        v___x_3681_ = lean_string_dec_eq(v_str_3679_, v___x_3680_);
                                        if v___x_3681_ == 0 {
                                            crate::leanh::lean_dec(v_us_3678_);
                                            crate::leanh::lean_del_object(v___x_3664_);
                                            crate::leanh::lean_dec(v_snd_3662_);
                                            crate::leanh::lean_dec(v___x_3644_);
                                            state = 5;
                                            continue;
                                        } else {
                                            if crate::leanh::lean_obj_tag(v_us_3678_) == 0 {
                                                v___x_3682_ = crate::leanh::lean_unsigned_to_nat(2);
                                                v___x_3683_ =
                                                    lean_array_fget(v_snd_3662_, v___x_3682_);
                                                crate::leanh::lean_dec(v_snd_3662_);
                                                v___x_3684_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19;
                                                v___x_3685_ = l_Lean_Expr_const___override(
                                                    v___x_3684_,
                                                    v_us_3678_,
                                                );
                                                v___x_3686_ = l_Lean_mkAppB(
                                                    v___x_3685_,
                                                    v___x_3683_,
                                                    v___x_3644_,
                                                );
                                                v___x_3687_ = crate::leanh::lean_box(0);
                                                if v_isShared_3665_ == 0 {
                                                    crate::leanh::lean_ctor_set_tag(v___x_3664_, 1);
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3664_,
                                                        1,
                                                        v___x_3687_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3664_,
                                                        0,
                                                        v___x_3686_,
                                                    );
                                                    v___x_3689_ = v___x_3664_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3691_ =
                                                        crate::leanh::lean_alloc_ctor(
                                                            1,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                    crate::leanh::lean_ctor_set(
                                                        v_reuseFailAlloc_3691_,
                                                        0,
                                                        v___x_3686_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v_reuseFailAlloc_3691_,
                                                        1,
                                                        v___x_3687_,
                                                    );
                                                    v___x_3689_ = v_reuseFailAlloc_3691_;
                                                    state = 13;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_us_3678_);
                                                crate::leanh::lean_del_object(v___x_3664_);
                                                crate::leanh::lean_dec(v_snd_3662_);
                                                crate::leanh::lean_dec(v___x_3644_);
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_del_object(v___x_3664_);
                                        crate::leanh::lean_dec(v_snd_3662_);
                                        crate::leanh::lean_dec(v___x_3644_);
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_3664_);
                                    crate::leanh::lean_dec(v_snd_3662_);
                                    crate::leanh::lean_dec(v___x_3644_);
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_3664_);
                                crate::leanh::lean_dec(v_snd_3662_);
                                crate::leanh::lean_dec(v___x_3644_);
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            13 => {
                v___x_3690_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3690_, 0, v___x_3689_);
                return v___x_3690_;
            }
            14 => {
                v_str_3720_ = crate::leanh::lean_ctor_get(v_fst_3713_, 1);
                crate::leanh::lean_inc_ref(v_str_3720_);
                crate::leanh::lean_dec_ref_known(v_fst_3713_, 2);
                v_str_3721_ = crate::leanh::lean_ctor_get(v_pre_3714_, 1);
                crate::leanh::lean_inc_ref(v_str_3721_);
                crate::leanh::lean_dec_ref_known(v_pre_3714_, 2);
                v___x_3722_ = lean_string_dec_eq(v_str_3721_, v___x_3694_);
                crate::leanh::lean_dec_ref(v_str_3721_);
                if v___x_3722_ == 0 {
                    crate::leanh::lean_dec_ref(v_str_3720_);
                    crate::leanh::lean_del_object(v___x_3718_);
                    crate::leanh::lean_dec(v_snd_3716_);
                    crate::leanh::lean_dec(v___x_3711_);
                    crate::leanh::lean_del_object(v___x_3651_);
                    crate::leanh::lean_del_object(v___x_3586_);
                    state = 11;
                    continue;
                } else {
                    v___x_3723_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
                    v___x_3724_ = lean_string_dec_eq(v_str_3720_, v___x_3723_);
                    crate::leanh::lean_dec_ref(v_str_3720_);
                    if v___x_3724_ == 0 {
                        crate::leanh::lean_del_object(v___x_3718_);
                        crate::leanh::lean_dec(v_snd_3716_);
                        crate::leanh::lean_dec(v___x_3711_);
                        crate::leanh::lean_del_object(v___x_3651_);
                        crate::leanh::lean_del_object(v___x_3586_);
                        state = 11;
                        continue;
                    } else {
                        v___x_3725_ = lean_array_get_size(v_snd_3716_);
                        v___x_3726_ = lean_nat_dec_eq(v___x_3725_, v___x_3641_);
                        if v___x_3726_ == 0 {
                            crate::leanh::lean_del_object(v___x_3718_);
                            crate::leanh::lean_dec(v_snd_3716_);
                            crate::leanh::lean_dec(v___x_3711_);
                            crate::leanh::lean_del_object(v___x_3651_);
                            crate::leanh::lean_del_object(v___x_3586_);
                            state = 11;
                            continue;
                        } else {
                            v___x_3727_ = lean_array_fget(v_snd_3716_, v___x_3655_);
                            crate::leanh::lean_inc(v___x_3727_);
                            v___x_3728_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_3727_);
                            if crate::leanh::lean_obj_tag(v___x_3728_) == 0 {
                                crate::leanh::lean_dec(v___x_3727_);
                                crate::leanh::lean_del_object(v___x_3718_);
                                crate::leanh::lean_dec(v_snd_3716_);
                                crate::leanh::lean_dec(v___x_3711_);
                                crate::leanh::lean_dec(v___x_3656_);
                                crate::leanh::lean_del_object(v___x_3651_);
                                crate::leanh::lean_dec(v___x_3644_);
                                crate::leanh::lean_del_object(v___x_3586_);
                                state = 6;
                                continue;
                            } else {
                                v_val_3729_ = crate::leanh::lean_ctor_get(v___x_3728_, 0);
                                crate::leanh::lean_inc(v_val_3729_);
                                crate::leanh::lean_dec_ref_known(v___x_3728_, 1);
                                v___x_3730_ = lean_nat_dec_eq(v_val_3729_, v___x_3702_);
                                crate::leanh::lean_dec(v_val_3729_);
                                if v___x_3730_ == 0 {
                                    v___x_3731_ =
                                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22;
                                    v___x_3732_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23);
                                    if v_isShared_3719_ == 0 {
                                        crate::leanh::lean_ctor_set_tag(v___x_3718_, 1);
                                        crate::leanh::lean_ctor_set(v___x_3718_, 1, v_us_3706_);
                                        crate::leanh::lean_ctor_set(v___x_3718_, 0, v___x_3732_);
                                        v___x_3734_ = v___x_3718_;
                                        state = 15;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3794_ =
                                            crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3794_,
                                            0,
                                            v___x_3732_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3794_,
                                            1,
                                            v_us_3706_,
                                        );
                                        v___x_3734_ = v_reuseFailAlloc_3794_;
                                        state = 15;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_3727_);
                                    crate::leanh::lean_del_object(v___x_3718_);
                                    crate::leanh::lean_dec(v_snd_3716_);
                                    crate::leanh::lean_dec(v___x_3711_);
                                    crate::leanh::lean_dec(v___x_3656_);
                                    crate::leanh::lean_del_object(v___x_3651_);
                                    crate::leanh::lean_dec(v___x_3644_);
                                    crate::leanh::lean_del_object(v___x_3586_);
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            15 => {
                crate::leanh::lean_inc_ref(v___x_3734_);
                v___x_3735_ = l_Lean_Expr_const___override(v___x_3731_, v___x_3734_);
                v___x_3736_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24;
                v___x_3737_ = l_Lean_Expr_const___override(v___x_3736_, v_us_3706_);
                v___x_3738_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26;
                v___x_3739_ = l_Lean_Expr_const___override(v___x_3738_, v_us_3706_);
                v___x_3740_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27,
                );
                crate::leanh::lean_inc(v___x_3727_);
                v_b__pos_3741_ = l_Lean_mkApp4(
                    v___x_3735_,
                    v___x_3737_,
                    v___x_3739_,
                    v___x_3740_,
                    v___x_3727_,
                );
                v___x_3742_ = l_Lean_Meta_mkDecideProof(
                    v_b__pos_3741_,
                    v_a_3557_,
                    v_a_3558_,
                    v_a_3559_,
                    v_a_3560_,
                );
                if crate::leanh::lean_obj_tag(v___x_3742_) == 0 {
                    v_a_3743_ = crate::leanh::lean_ctor_get(v___x_3742_, 0);
                    v_isSharedCheck_3785_ = (!crate::leanh::lean_is_exclusive(v___x_3742_)) as u8;
                    if v_isSharedCheck_3785_ == 0 {
                        v___x_3745_ = v___x_3742_;
                        v_isShared_3746_ = v_isSharedCheck_3785_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3743_);
                        crate::leanh::lean_dec(v___x_3742_);
                        v___x_3745_ = crate::leanh::lean_box(0);
                        v_isShared_3746_ = v_isSharedCheck_3785_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3734_);
                    crate::leanh::lean_dec(v___x_3727_);
                    crate::leanh::lean_dec(v_snd_3716_);
                    crate::leanh::lean_dec(v___x_3711_);
                    crate::leanh::lean_dec(v___x_3656_);
                    crate::leanh::lean_del_object(v___x_3651_);
                    crate::leanh::lean_dec(v___x_3644_);
                    crate::leanh::lean_del_object(v___x_3586_);
                    v_a_3786_ = crate::leanh::lean_ctor_get(v___x_3742_, 0);
                    v_isSharedCheck_3793_ = (!crate::leanh::lean_is_exclusive(v___x_3742_)) as u8;
                    if v_isSharedCheck_3793_ == 0 {
                        v___x_3788_ = v___x_3742_;
                        v_isShared_3789_ = v_isSharedCheck_3793_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3786_);
                        crate::leanh::lean_dec(v___x_3742_);
                        v___x_3788_ = crate::leanh::lean_box(0);
                        v_isShared_3789_ = v_isSharedCheck_3793_;
                        state = 21;
                        continue;
                    }
                }
            }
            16 => {
                v___x_3747_ = lean_array_fget(v_snd_3716_, v___x_3643_);
                crate::leanh::lean_dec(v_snd_3716_);
                v___x_3748_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29;
                v___x_3749_ = l_Lean_Expr_const___override(v___x_3748_, v_us_3706_);
                v___x_3750_ = l_Lean_mkApp3(v___x_3749_, v___x_3727_, v___x_3747_, v_a_3743_);
                v___x_3751_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31;
                v___x_3752_ = l_Lean_Expr_const___override(v___x_3751_, v_us_3706_);
                v___x_3753_ = l_Lean_mkAppB(v___x_3752_, v___x_3711_, v___x_3750_);
                v___x_3754_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33;
                v___x_3755_ = l_Lean_Expr_const___override(v___x_3754_, v_us_3706_);
                v___x_3756_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35;
                v___x_3757_ = l_Lean_Expr_const___override(v___x_3756_, v_us_3706_);
                v___x_3775_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39,
                );
                if v___x_3775_ == 0 {
                    v___x_3776_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42;
                    v___x_3777_ = l_Lean_Expr_const___override(v___x_3776_, v___x_3734_);
                    v___x_3778_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1;
                    v___x_3779_ = l_Lean_Expr_const___override(v___x_3778_, v_us_3706_);
                    v___x_3780_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44;
                    v___x_3781_ = l_Lean_Expr_const___override(v___x_3780_, v_us_3706_);
                    v___x_3782_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once
                        ),
                        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47,
                    );
                    v___x_3783_ = l_Lean_mkApp3(v___x_3777_, v___x_3779_, v___x_3781_, v___x_3782_);
                    v___y_3759_ = v___x_3783_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_3734_);
                    v___x_3784_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once
                        ),
                        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49,
                    );
                    v___y_3759_ = v___x_3784_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                crate::leanh::lean_inc_ref(v___x_3753_);
                crate::leanh::lean_inc_n(v___x_3644_, 2);
                v___x_3760_ = l_Lean_mkApp3(v___x_3757_, v___x_3644_, v___y_3759_, v___x_3753_);
                crate::leanh::lean_inc(v___x_3656_);
                v___x_3761_ = l_Lean_mkApp3(v___x_3755_, v___x_3656_, v___x_3644_, v___x_3760_);
                v___x_3762_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37;
                v___x_3763_ = l_Lean_Expr_const___override(v___x_3762_, v_us_3706_);
                v___x_3764_ = l_Lean_mkApp3(v___x_3763_, v___x_3656_, v___x_3644_, v___x_3753_);
                v___x_3765_ = crate::leanh::lean_box(0);
                if v_isShared_3652_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3651_, 1);
                    crate::leanh::lean_ctor_set(v___x_3651_, 1, v___x_3765_);
                    crate::leanh::lean_ctor_set(v___x_3651_, 0, v___x_3764_);
                    v___x_3767_ = v___x_3651_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3774_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3764_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 1, v___x_3765_);
                    v___x_3767_ = v_reuseFailAlloc_3774_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3587_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3586_, 1);
                    crate::leanh::lean_ctor_set(v___x_3586_, 1, v___x_3767_);
                    crate::leanh::lean_ctor_set(v___x_3586_, 0, v___x_3761_);
                    v___x_3769_ = v___x_3586_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3773_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3773_, 1, v___x_3767_);
                    v___x_3769_ = v_reuseFailAlloc_3773_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3746_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3745_, 0, v___x_3769_);
                    v___x_3771_ = v___x_3745_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3769_);
                    v___x_3771_ = v_reuseFailAlloc_3772_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3771_;
            }
            21 => {
                if v_isShared_3789_ == 0 {
                    v___x_3791_ = v___x_3788_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3792_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
                    v___x_3791_ = v_reuseFailAlloc_3792_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3791_;
            }
            23 => {
                crate::leanh::lean_inc(v___x_3801_);
                crate::leanh::lean_inc_ref(v___y_3812_);
                v_b__pos_3813_ = l_Lean_mkApp4(
                    v___x_3808_,
                    v___x_3809_,
                    v___x_3810_,
                    v___y_3812_,
                    v___x_3801_,
                );
                v___x_3814_ = l_Lean_Meta_mkDecideProof(
                    v_b__pos_3813_,
                    v_a_3557_,
                    v_a_3558_,
                    v_a_3559_,
                    v_a_3560_,
                );
                if crate::leanh::lean_obj_tag(v___x_3814_) == 0 {
                    v_a_3815_ = crate::leanh::lean_ctor_get(v___x_3814_, 0);
                    v_isSharedCheck_3836_ = (!crate::leanh::lean_is_exclusive(v___x_3814_)) as u8;
                    if v_isSharedCheck_3836_ == 0 {
                        v___x_3817_ = v___x_3814_;
                        v_isShared_3818_ = v_isSharedCheck_3836_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3815_);
                        crate::leanh::lean_dec(v___x_3814_);
                        v___x_3817_ = crate::leanh::lean_box(0);
                        v_isShared_3818_ = v_isSharedCheck_3836_;
                        state = 24;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3806_);
                    crate::leanh::lean_dec(v___x_3801_);
                    crate::leanh::lean_dec(v___x_3656_);
                    crate::leanh::lean_del_object(v___x_3651_);
                    crate::leanh::lean_dec(v___x_3644_);
                    crate::leanh::lean_del_object(v___x_3586_);
                    v_a_3837_ = crate::leanh::lean_ctor_get(v___x_3814_, 0);
                    v_isSharedCheck_3844_ = (!crate::leanh::lean_is_exclusive(v___x_3814_)) as u8;
                    if v_isSharedCheck_3844_ == 0 {
                        v___x_3839_ = v___x_3814_;
                        v_isShared_3840_ = v_isSharedCheck_3844_;
                        state = 28;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3837_);
                        crate::leanh::lean_dec(v___x_3814_);
                        v___x_3839_ = crate::leanh::lean_box(0);
                        v_isShared_3840_ = v_isSharedCheck_3844_;
                        state = 28;
                        continue;
                    }
                }
            }
            24 => {
                v___x_3819_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57,
                );
                v___x_3820_ = l_Lean_mkApp3(v___x_3819_, v___x_3801_, v___x_3806_, v_a_3815_);
                v___x_3821_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58,
                );
                v___x_3822_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59,
                );
                crate::leanh::lean_inc_ref(v___x_3820_);
                crate::leanh::lean_inc_ref(v___y_3812_);
                crate::leanh::lean_inc_n(v___x_3644_, 2);
                v___x_3823_ = l_Lean_mkApp3(v___x_3822_, v___x_3644_, v___y_3812_, v___x_3820_);
                crate::leanh::lean_inc(v___x_3656_);
                v___x_3824_ = l_Lean_mkApp3(v___x_3821_, v___x_3656_, v___x_3644_, v___x_3823_);
                v___x_3825_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60,
                );
                v___x_3826_ = l_Lean_mkApp3(v___x_3825_, v___x_3656_, v___x_3644_, v___x_3820_);
                if v_isShared_3652_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3651_, 1);
                    crate::leanh::lean_ctor_set(v___x_3651_, 1, v___x_3807_);
                    crate::leanh::lean_ctor_set(v___x_3651_, 0, v___x_3826_);
                    v___x_3828_ = v___x_3651_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3835_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3826_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3835_, 1, v___x_3807_);
                    v___x_3828_ = v_reuseFailAlloc_3835_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_3587_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3586_, 1);
                    crate::leanh::lean_ctor_set(v___x_3586_, 1, v___x_3828_);
                    crate::leanh::lean_ctor_set(v___x_3586_, 0, v___x_3824_);
                    v___x_3830_ = v___x_3586_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3834_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 1, v___x_3828_);
                    v___x_3830_ = v_reuseFailAlloc_3834_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_3818_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3817_, 0, v___x_3830_);
                    v___x_3832_ = v___x_3817_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3833_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3830_);
                    v___x_3832_ = v_reuseFailAlloc_3833_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3832_;
            }
            28 => {
                if v_isShared_3840_ == 0 {
                    v___x_3842_ = v___x_3839_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3843_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
                    v___x_3842_ = v_reuseFailAlloc_3843_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3842_;
            }
            30 => {
                crate::leanh::lean_inc_ref(v___y_3867_);
                crate::leanh::lean_inc(v___x_3856_);
                v_ne__zero_3868_ =
                    l_Lean_mkApp3(v___x_3864_, v___x_3865_, v___x_3856_, v___y_3867_);
                v___x_3869_ = l_Lean_Meta_mkDecideProof(
                    v_ne__zero_3868_,
                    v_a_3557_,
                    v_a_3558_,
                    v_a_3559_,
                    v_a_3560_,
                );
                if crate::leanh::lean_obj_tag(v___x_3869_) == 0 {
                    v_a_3870_ = crate::leanh::lean_ctor_get(v___x_3869_, 0);
                    crate::leanh::lean_inc(v_a_3870_);
                    crate::leanh::lean_dec_ref_known(v___x_3869_, 1);
                    v___x_3871_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once
                        ),
                        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51,
                    );
                    v___x_3872_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once
                        ),
                        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54,
                    );
                    crate::leanh::lean_inc(v___x_3856_);
                    crate::leanh::lean_inc_ref(v___y_3867_);
                    v_pos_3873_ = l_Lean_mkApp4(
                        v___x_3871_,
                        v___x_3865_,
                        v___x_3872_,
                        v___y_3867_,
                        v___x_3856_,
                    );
                    v___x_3874_ = l_Lean_Meta_mkDecideProof(
                        v_pos_3873_,
                        v_a_3557_,
                        v_a_3558_,
                        v_a_3559_,
                        v_a_3560_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3874_) == 0 {
                        v_a_3875_ = crate::leanh::lean_ctor_get(v___x_3874_, 0);
                        v_isSharedCheck_3890_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3874_)) as u8;
                        if v_isSharedCheck_3890_ == 0 {
                            v___x_3877_ = v___x_3874_;
                            v_isShared_3878_ = v_isSharedCheck_3890_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3875_);
                            crate::leanh::lean_dec(v___x_3874_);
                            v___x_3877_ = crate::leanh::lean_box(0);
                            v_isShared_3878_ = v_isSharedCheck_3890_;
                            state = 31;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3870_);
                        crate::leanh::lean_dec(v___x_3862_);
                        crate::leanh::lean_dec(v___x_3856_);
                        crate::leanh::lean_del_object(v___x_3586_);
                        v_a_3891_ = crate::leanh::lean_ctor_get(v___x_3874_, 0);
                        v_isSharedCheck_3898_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3874_)) as u8;
                        if v_isSharedCheck_3898_ == 0 {
                            v___x_3893_ = v___x_3874_;
                            v_isShared_3894_ = v_isSharedCheck_3898_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3891_);
                            crate::leanh::lean_dec(v___x_3874_);
                            v___x_3893_ = crate::leanh::lean_box(0);
                            v_isShared_3894_ = v_isSharedCheck_3898_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3862_);
                    crate::leanh::lean_dec(v___x_3856_);
                    crate::leanh::lean_del_object(v___x_3586_);
                    v_a_3899_ = crate::leanh::lean_ctor_get(v___x_3869_, 0);
                    v_isSharedCheck_3906_ = (!crate::leanh::lean_is_exclusive(v___x_3869_)) as u8;
                    if v_isSharedCheck_3906_ == 0 {
                        v___x_3901_ = v___x_3869_;
                        v_isShared_3902_ = v_isSharedCheck_3906_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3899_);
                        crate::leanh::lean_dec(v___x_3869_);
                        v___x_3901_ = crate::leanh::lean_box(0);
                        v_isShared_3902_ = v_isSharedCheck_3906_;
                        state = 36;
                        continue;
                    }
                }
            }
            31 => {
                v___x_3879_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71,
                );
                crate::leanh::lean_inc(v___x_3856_);
                crate::leanh::lean_inc(v___x_3862_);
                v___x_3880_ = l_Lean_mkApp3(v___x_3879_, v___x_3862_, v___x_3856_, v_a_3870_);
                v___x_3881_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74,
                );
                v___x_3882_ = l_Lean_mkApp3(v___x_3881_, v___x_3862_, v___x_3856_, v_a_3875_);
                if v_isShared_3587_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3586_, 1);
                    crate::leanh::lean_ctor_set(v___x_3586_, 1, v___x_3863_);
                    crate::leanh::lean_ctor_set(v___x_3586_, 0, v___x_3882_);
                    v___x_3884_ = v___x_3586_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3889_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3889_, 1, v___x_3863_);
                    v___x_3884_ = v_reuseFailAlloc_3889_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_3885_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3885_, 0, v___x_3880_);
                crate::leanh::lean_ctor_set(v___x_3885_, 1, v___x_3884_);
                if v_isShared_3878_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3877_, 0, v___x_3885_);
                    v___x_3887_ = v___x_3877_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3888_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3885_);
                    v___x_3887_ = v_reuseFailAlloc_3888_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3887_;
            }
            34 => {
                if v_isShared_3894_ == 0 {
                    v___x_3896_ = v___x_3893_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3897_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
                    v___x_3896_ = v_reuseFailAlloc_3897_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_3896_;
            }
            36 => {
                if v_isShared_3902_ == 0 {
                    v___x_3904_ = v___x_3901_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
                    v___x_3904_ = v_reuseFailAlloc_3905_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3904_;
            }
            38 => {
                v___x_3925_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76;
                v___x_3926_ = l_Lean_Expr_const___override(v___x_3925_, v_us_3919_);
                v___x_3927_ = l_Lean_Expr_app___override(v___x_3926_, v___y_3923_);
                v___x_3928_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(
                    v___x_3927_,
                    v___y_3924_,
                );
                if v___x_3928_ == 0 {
                    if v_isShared_3587_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3586_, 1);
                        crate::leanh::lean_ctor_set(v___x_3586_, 1, v___y_3924_);
                        crate::leanh::lean_ctor_set(v___x_3586_, 0, v___x_3927_);
                        v___x_3930_ = v___x_3586_;
                        state = 39;
                        continue;
                    } else {
                        v_reuseFailAlloc_3932_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3927_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 1, v___y_3924_);
                        v___x_3930_ = v_reuseFailAlloc_3932_;
                        state = 39;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3927_);
                    crate::leanh::lean_del_object(v___x_3586_);
                    v___x_3933_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3933_, 0, v___y_3924_);
                    return v___x_3933_;
                }
            }
            39 => {
                v___x_3931_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3931_, 0, v___x_3930_);
                return v___x_3931_;
            }
            40 => {
                v___x_3946_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81;
                v___x_3947_ = l_Lean_Expr_const___override(v___x_3946_, v_us_3919_);
                v___x_3948_ = l_Lean_mkAppB(v___x_3947_, v_n_3944_, v_x_3945_);
                v___x_3949_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(
                    v___x_3948_,
                    v_r_3942_,
                );
                if v___x_3949_ == 0 {
                    v___x_3950_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3950_, 0, v___x_3948_);
                    crate::leanh::lean_ctor_set(v___x_3950_, 1, v_r_3942_);
                    v___x_3951_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3951_, 0, v___x_3950_);
                    return v___x_3951_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_3948_);
                    v___x_3952_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3952_, 0, v_r_3942_);
                    return v___x_3952_;
                }
            }
            41 => {
                v___x_3956_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83;
                v___x_3957_ = l_Lean_Expr_const___override(v___x_3956_, v_us_3919_);
                v___x_3958_ = l_Lean_mkAppB(v___x_3957_, v_n_3954_, v_i_3955_);
                v___x_3959_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(
                    v___x_3958_,
                    v_r_3942_,
                );
                if v___x_3959_ == 0 {
                    v___x_3960_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3960_, 0, v___x_3958_);
                    crate::leanh::lean_ctor_set(v___x_3960_, 1, v_r_3942_);
                    v___x_3961_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_3960_);
                    return v___x_3961_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_3958_);
                    v___x_3962_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3962_, 0, v_r_3942_);
                    return v___x_3962_;
                }
            }
            42 => {
                v___x_3965_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85;
                v___x_3966_ = l_Lean_Expr_const___override(v___x_3965_, v_us_3919_);
                crate::leanh::lean_inc_ref(v_x_3964_);
                v___x_3967_ = l_Lean_Expr_app___override(v___x_3966_, v_x_3964_);
                v___x_3968_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(
                    v___x_3967_,
                    v_r_3942_,
                );
                if v___x_3968_ == 0 {
                    v___x_3969_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3969_, 0, v___x_3967_);
                    crate::leanh::lean_ctor_set(v___x_3969_, 1, v_r_3942_);
                    v___y_3923_ = v_x_3964_;
                    v___y_3924_ = v___x_3969_;
                    state = 38;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_3967_);
                    v___y_3923_ = v_x_3964_;
                    v___y_3924_ = v_r_3942_;
                    state = 38;
                    continue;
                }
            }
            43 => {
                v_str_3978_ = crate::leanh::lean_ctor_get(v_fst_3971_, 1);
                crate::leanh::lean_inc_ref(v_str_3978_);
                crate::leanh::lean_dec_ref_known(v_fst_3971_, 2);
                v_str_3979_ = crate::leanh::lean_ctor_get(v_pre_3972_, 1);
                crate::leanh::lean_inc_ref(v_str_3979_);
                crate::leanh::lean_dec_ref_known(v_pre_3972_, 2);
                v___x_3980_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
                v___x_3981_ = lean_string_dec_eq(v_str_3979_, v___x_3980_);
                if v___x_3981_ == 0 {
                    crate::leanh::lean_del_object(v___x_3976_);
                    v___x_3982_ = lean_string_dec_eq(v_str_3979_, v___x_3921_);
                    if v___x_3982_ == 0 {
                        crate::leanh::lean_del_object(v___x_3586_);
                        v___x_3983_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82;
                        v___x_3984_ = lean_string_dec_eq(v_str_3979_, v___x_3983_);
                        if v___x_3984_ == 0 {
                            v___x_3985_ =
                                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79;
                            v___x_3986_ = lean_string_dec_eq(v_str_3979_, v___x_3985_);
                            crate::leanh::lean_dec_ref(v_str_3979_);
                            if v___x_3986_ == 0 {
                                crate::leanh::lean_dec_ref(v_str_3978_);
                                crate::leanh::lean_dec(v_snd_3974_);
                                v___x_3987_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3987_, 0, v_r_3942_);
                                return v___x_3987_;
                            } else {
                                v___x_3988_ =
                                    l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86;
                                v___x_3989_ = lean_string_dec_eq(v_str_3978_, v___x_3988_);
                                crate::leanh::lean_dec_ref(v_str_3978_);
                                if v___x_3989_ == 0 {
                                    crate::leanh::lean_dec(v_snd_3974_);
                                    v___x_3990_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3990_, 0, v_r_3942_);
                                    return v___x_3990_;
                                } else {
                                    v___x_3991_ = lean_array_get_size(v_snd_3974_);
                                    v___x_3992_ = lean_nat_dec_eq(v___x_3991_, v___x_3936_);
                                    if v___x_3992_ == 0 {
                                        crate::leanh::lean_dec(v_snd_3974_);
                                        v___x_3993_ =
                                            crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3993_, 0, v_r_3942_);
                                        return v___x_3993_;
                                    } else {
                                        v___x_3994_ = lean_array_fget(v_snd_3974_, v___x_3915_);
                                        v___x_3995_ = crate::leanh::lean_unsigned_to_nat(1);
                                        v___x_3996_ = lean_array_fget(v_snd_3974_, v___x_3995_);
                                        crate::leanh::lean_dec(v_snd_3974_);
                                        v_n_3944_ = v___x_3994_;
                                        v_x_3945_ = v___x_3996_;
                                        state = 40;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_str_3979_);
                            v___x_3997_ =
                                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87;
                            v___x_3998_ = lean_string_dec_eq(v_str_3978_, v___x_3997_);
                            crate::leanh::lean_dec_ref(v_str_3978_);
                            if v___x_3998_ == 0 {
                                crate::leanh::lean_dec(v_snd_3974_);
                                v___x_3999_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3999_, 0, v_r_3942_);
                                return v___x_3999_;
                            } else {
                                v___x_4000_ = lean_array_get_size(v_snd_3974_);
                                v___x_4001_ = lean_nat_dec_eq(v___x_4000_, v___x_3936_);
                                if v___x_4001_ == 0 {
                                    crate::leanh::lean_dec(v_snd_3974_);
                                    v___x_4002_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4002_, 0, v_r_3942_);
                                    return v___x_4002_;
                                } else {
                                    v___x_4003_ = lean_array_fget(v_snd_3974_, v___x_3915_);
                                    v___x_4004_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_4005_ = lean_array_fget(v_snd_3974_, v___x_4004_);
                                    crate::leanh::lean_dec(v_snd_3974_);
                                    v_n_3954_ = v___x_4003_;
                                    v_i_3955_ = v___x_4005_;
                                    state = 41;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_str_3979_);
                        v___x_4006_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88;
                        v___x_4007_ = lean_string_dec_eq(v_str_3978_, v___x_4006_);
                        crate::leanh::lean_dec_ref(v_str_3978_);
                        if v___x_4007_ == 0 {
                            crate::leanh::lean_dec(v_snd_3974_);
                            crate::leanh::lean_del_object(v___x_3586_);
                            v___x_4008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4008_, 0, v_r_3942_);
                            return v___x_4008_;
                        } else {
                            v___x_4009_ = lean_array_get_size(v_snd_3974_);
                            v___x_4010_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4011_ = lean_nat_dec_eq(v___x_4009_, v___x_4010_);
                            if v___x_4011_ == 0 {
                                crate::leanh::lean_dec(v_snd_3974_);
                                crate::leanh::lean_del_object(v___x_3586_);
                                v___x_4012_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4012_, 0, v_r_3942_);
                                return v___x_4012_;
                            } else {
                                v___x_4013_ = lean_array_fget(v_snd_3974_, v___x_3915_);
                                crate::leanh::lean_dec(v_snd_3974_);
                                v_x_3964_ = v___x_4013_;
                                state = 42;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_str_3979_);
                    crate::leanh::lean_del_object(v___x_3586_);
                    v___x_4014_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
                    v___x_4015_ = lean_string_dec_eq(v_str_3978_, v___x_4014_);
                    crate::leanh::lean_dec_ref(v_str_3978_);
                    if v___x_4015_ == 0 {
                        crate::leanh::lean_del_object(v___x_3976_);
                        crate::leanh::lean_dec(v_snd_3974_);
                        v___x_4016_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4016_, 0, v_r_3942_);
                        return v___x_4016_;
                    } else {
                        v___x_4017_ = lean_array_get_size(v_snd_3974_);
                        v___x_4018_ = crate::leanh::lean_unsigned_to_nat(6);
                        v___x_4019_ = lean_nat_dec_eq(v___x_4017_, v___x_4018_);
                        if v___x_4019_ == 0 {
                            crate::leanh::lean_del_object(v___x_3976_);
                            crate::leanh::lean_dec(v_snd_3974_);
                            v___x_4020_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4020_, 0, v_r_3942_);
                            return v___x_4020_;
                        } else {
                            v___x_4021_ = crate::leanh::lean_unsigned_to_nat(4);
                            v___x_4022_ = lean_array_fget(v_snd_3974_, v___x_4021_);
                            v___x_4023_ = crate::leanh::lean_unsigned_to_nat(5);
                            v___x_4024_ = lean_array_fget(v_snd_3974_, v___x_4023_);
                            crate::leanh::lean_dec(v_snd_3974_);
                            v___x_4025_ =
                                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90;
                            v___x_4026_ = l_Lean_Expr_const___override(v___x_4025_, v_us_3919_);
                            v___x_4027_ = l_Lean_mkAppB(v___x_4026_, v___x_4022_, v___x_4024_);
                            v___x_4028_ =
                                l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(
                                    v___x_4027_,
                                    v_r_3942_,
                                );
                            if v___x_4028_ == 0 {
                                if v_isShared_3977_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_3976_, 1);
                                    crate::leanh::lean_ctor_set(v___x_3976_, 1, v_r_3942_);
                                    crate::leanh::lean_ctor_set(v___x_3976_, 0, v___x_4027_);
                                    v___x_4030_ = v___x_3976_;
                                    state = 44;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4032_ =
                                        crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4032_,
                                        0,
                                        v___x_4027_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4032_,
                                        1,
                                        v_r_3942_,
                                    );
                                    v___x_4030_ = v_reuseFailAlloc_4032_;
                                    state = 44;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4027_);
                                crate::leanh::lean_del_object(v___x_3976_);
                                v___x_4033_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4033_, 0, v_r_3942_);
                                return v___x_4033_;
                            }
                        }
                    }
                }
            }
            44 => {
                v___x_4031_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4031_, 0, v___x_4030_);
                return v___x_4031_;
            }
            45 => {
                v_str_4087_ = crate::leanh::lean_ctor_get(v_fst_3581_, 1);
                crate::leanh::lean_inc_ref(v_str_4087_);
                crate::leanh::lean_dec_ref_known(v_fst_3581_, 2);
                v___x_4088_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91;
                v___x_4089_ = lean_string_dec_eq(v_str_4087_, v___x_4088_);
                crate::leanh::lean_dec_ref(v_str_4087_);
                if v___x_4089_ == 0 {
                    crate::leanh::lean_del_object(v___x_4085_);
                    crate::leanh::lean_dec(v_snd_4083_);
                    state = 3;
                    continue;
                } else {
                    v___x_4090_ = lean_array_get_size(v_snd_4083_);
                    v___x_4091_ = crate::leanh::lean_unsigned_to_nat(5);
                    v___x_4092_ = lean_nat_dec_eq(v___x_4090_, v___x_4091_);
                    if v___x_4092_ == 0 {
                        crate::leanh::lean_del_object(v___x_4085_);
                        crate::leanh::lean_dec(v_snd_4083_);
                        state = 3;
                        continue;
                    } else {
                        v___x_4093_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4094_ = lean_array_fget(v_snd_4083_, v___x_4093_);
                        v___x_4095_ = crate::leanh::lean_box(0);
                        v___x_4096_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once
                            ),
                            _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2,
                        );
                        v___x_4097_ = lean_expr_eqv(v___x_4094_, v___x_4096_);
                        if v___x_4097_ == 0 {
                            crate::leanh::lean_dec(v___x_4094_);
                            crate::leanh::lean_del_object(v___x_4085_);
                            crate::leanh::lean_dec(v_snd_4083_);
                            v___x_4098_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4098_, 0, v___x_4095_);
                            return v___x_4098_;
                        } else {
                            v___x_4099_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4100_ = lean_array_fget(v_snd_4083_, v___x_4099_);
                            v___x_4101_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_4102_ = lean_array_fget(v_snd_4083_, v___x_4101_);
                            v___x_4103_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_4104_ = lean_array_fget(v_snd_4083_, v___x_4103_);
                            v___x_4105_ = crate::leanh::lean_unsigned_to_nat(4);
                            v___x_4106_ = lean_array_fget(v_snd_4083_, v___x_4105_);
                            crate::leanh::lean_dec(v_snd_4083_);
                            v___x_4107_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94_once
                                ),
                                _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94,
                            );
                            v___x_4108_ = l_Lean_mkApp5(
                                v___x_4107_,
                                v___x_4094_,
                                v___x_4100_,
                                v___x_4102_,
                                v___x_4104_,
                                v___x_4106_,
                            );
                            if v_isShared_4086_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_4085_, 1);
                                crate::leanh::lean_ctor_set(v___x_4085_, 1, v___x_4095_);
                                crate::leanh::lean_ctor_set(v___x_4085_, 0, v___x_4108_);
                                v___x_4110_ = v___x_4085_;
                                state = 46;
                                continue;
                            } else {
                                v_reuseFailAlloc_4112_ =
                                    crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4108_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 1, v___x_4095_);
                                v___x_4110_ = v_reuseFailAlloc_4112_;
                                state = 46;
                                continue;
                            }
                        }
                    }
                }
            }
            46 => {
                v___x_4111_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4111_, 0, v___x_4110_);
                return v___x_4111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___boxed(
    mut v_e_4115_: *mut crate::leanh::LeanObject,
    mut v_a_4116_: *mut crate::leanh::LeanObject,
    mut v_a_4117_: *mut crate::leanh::LeanObject,
    mut v_a_4118_: *mut crate::leanh::LeanObject,
    mut v_a_4119_: *mut crate::leanh::LeanObject,
    mut v_a_4120_: *mut crate::leanh::LeanObject,
    mut v_a_4121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4122_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(
        v_e_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_,
    );
    crate::leanh::lean_dec(v_a_4120_);
    crate::leanh::lean_dec_ref(v_a_4119_);
    crate::leanh::lean_dec(v_a_4118_);
    crate::leanh::lean_dec_ref(v_a_4117_);
    crate::leanh::lean_dec_ref(v_a_4116_);
    return v_res_4122_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_analyzeAtom(
    mut v_e_4123_: *mut crate::leanh::LeanObject,
    mut v_a_4124_: *mut crate::leanh::LeanObject,
    mut v_a_4125_: *mut crate::leanh::LeanObject,
    mut v_a_4126_: *mut crate::leanh::LeanObject,
    mut v_a_4127_: u8,
    mut v_a_4128_: *mut crate::leanh::LeanObject,
    mut v_a_4129_: *mut crate::leanh::LeanObject,
    mut v_a_4130_: *mut crate::leanh::LeanObject,
    mut v_a_4131_: *mut crate::leanh::LeanObject,
    mut v_a_4132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4134_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(
        v_e_4123_, v_a_4126_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_,
    );
    return v___x_4134_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(
    mut v_e_4135_: *mut crate::leanh::LeanObject,
    mut v_a_4136_: *mut crate::leanh::LeanObject,
    mut v_a_4137_: *mut crate::leanh::LeanObject,
    mut v_a_4138_: *mut crate::leanh::LeanObject,
    mut v_a_4139_: *mut crate::leanh::LeanObject,
    mut v_a_4140_: *mut crate::leanh::LeanObject,
    mut v_a_4141_: *mut crate::leanh::LeanObject,
    mut v_a_4142_: *mut crate::leanh::LeanObject,
    mut v_a_4143_: *mut crate::leanh::LeanObject,
    mut v_a_4144_: *mut crate::leanh::LeanObject,
    mut v_a_4145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4146_: u8 = 0;
    let mut v_res_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4146_ = (crate::leanh::lean_unbox(v_a_4139_) as u8);
    v_res_4147_ = l_Lean_Elab_Tactic_Omega_analyzeAtom(
        v_e_4135_,
        v_a_4136_,
        v_a_4137_,
        v_a_4138_,
        v_a_boxed_4146_,
        v_a_4140_,
        v_a_4141_,
        v_a_4142_,
        v_a_4143_,
        v_a_4144_,
    );
    crate::leanh::lean_dec(v_a_4144_);
    crate::leanh::lean_dec_ref(v_a_4143_);
    crate::leanh::lean_dec(v_a_4142_);
    crate::leanh::lean_dec_ref(v_a_4141_);
    crate::leanh::lean_dec(v_a_4140_);
    crate::leanh::lean_dec_ref(v_a_4138_);
    crate::leanh::lean_dec(v_a_4137_);
    crate::leanh::lean_dec(v_a_4136_);
    return v_res_4147_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(
    mut v_a_4148_: *mut crate::leanh::LeanObject,
    mut v_x_4149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: u8 = 0;
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4149_) == 0 {
                    v___x_4150_ = crate::leanh::lean_box(0);
                    return v___x_4150_;
                } else {
                    v_key_4151_ = crate::leanh::lean_ctor_get(v_x_4149_, 0);
                    v_value_4152_ = crate::leanh::lean_ctor_get(v_x_4149_, 1);
                    v_tail_4153_ = crate::leanh::lean_ctor_get(v_x_4149_, 2);
                    v___x_4154_ = lean_expr_eqv(v_key_4151_, v_a_4148_);
                    if v___x_4154_ == 0 {
                        v_x_4149_ = v_tail_4153_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_4152_);
                        v___x_4156_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4156_, 0, v_value_4152_);
                        return v___x_4156_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg___boxed(
    mut v_a_4157_: *mut crate::leanh::LeanObject,
    mut v_x_4158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4159_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_4157_, v_x_4158_);
    crate::leanh::lean_dec(v_x_4158_);
    crate::leanh::lean_dec_ref(v_a_4157_);
    return v_res_4159_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(
    mut v_m_4160_: *mut crate::leanh::LeanObject,
    mut v_a_4161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: u64 = 0;
    let mut v___x_4165_: u64 = 0;
    let mut v___x_4166_: u64 = 0;
    let mut v_fold_4167_: u64 = 0;
    let mut v___x_4168_: u64 = 0;
    let mut v___x_4169_: u64 = 0;
    let mut v___x_4170_: u64 = 0;
    let mut v___x_4171_: usize = 0;
    let mut v___x_4172_: usize = 0;
    let mut v___x_4173_: usize = 0;
    let mut v___x_4174_: usize = 0;
    let mut v___x_4175_: usize = 0;
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4162_ = crate::leanh::lean_ctor_get(v_m_4160_, 1);
    v___x_4163_ = lean_array_get_size(v_buckets_4162_);
    v___x_4164_ = l_Lean_Expr_hash(v_a_4161_);
    v___x_4165_ = 32u64;
    v___x_4166_ = lean_uint64_shift_right(v___x_4164_, v___x_4165_);
    v_fold_4167_ = lean_uint64_xor(v___x_4164_, v___x_4166_);
    v___x_4168_ = 16u64;
    v___x_4169_ = lean_uint64_shift_right(v_fold_4167_, v___x_4168_);
    v___x_4170_ = lean_uint64_xor(v_fold_4167_, v___x_4169_);
    v___x_4171_ = lean_uint64_to_usize(v___x_4170_);
    v___x_4172_ = lean_usize_of_nat(v___x_4163_);
    v___x_4173_ = 1usize;
    v___x_4174_ = lean_usize_sub(v___x_4172_, v___x_4173_);
    v___x_4175_ = lean_usize_land(v___x_4171_, v___x_4174_);
    v___x_4176_ = lean_array_uget_borrowed(v_buckets_4162_, v___x_4175_);
    v___x_4177_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_4161_, v___x_4176_);
    return v___x_4177_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(
    mut v_m_4178_: *mut crate::leanh::LeanObject,
    mut v_a_4179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4180_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_4178_, v_a_4179_);
    crate::leanh::lean_dec_ref(v_a_4179_);
    crate::leanh::lean_dec_ref(v_m_4178_);
    return v_res_4180_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(
    mut v_a_4181_: *mut crate::leanh::LeanObject,
    mut v_x_4182_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4183_: u8 = 0;
    let mut v_key_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4182_) == 0 {
                    v___x_4183_ = 0;
                    return v___x_4183_;
                } else {
                    v_key_4184_ = crate::leanh::lean_ctor_get(v_x_4182_, 0);
                    v_tail_4185_ = crate::leanh::lean_ctor_get(v_x_4182_, 2);
                    v___x_4186_ = lean_expr_eqv(v_key_4184_, v_a_4181_);
                    if v___x_4186_ == 0 {
                        v_x_4182_ = v_tail_4185_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4186_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg___boxed(
    mut v_a_4188_: *mut crate::leanh::LeanObject,
    mut v_x_4189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4190_: u8 = 0;
    let mut v_r_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_4188_, v_x_4189_);
    crate::leanh::lean_dec(v_x_4189_);
    crate::leanh::lean_dec_ref(v_a_4188_);
    v_r_4191_ = crate::leanh::lean_box((v_res_4190_) as usize);
    return v_r_4191_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(
    mut v_x_4192_: *mut crate::leanh::LeanObject,
    mut v_x_4193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: u64 = 0;
    let mut v___x_4202_: u64 = 0;
    let mut v___x_4203_: u64 = 0;
    let mut v_fold_4204_: u64 = 0;
    let mut v___x_4205_: u64 = 0;
    let mut v___x_4206_: u64 = 0;
    let mut v___x_4207_: u64 = 0;
    let mut v___x_4208_: usize = 0;
    let mut v___x_4209_: usize = 0;
    let mut v___x_4210_: usize = 0;
    let mut v___x_4211_: usize = 0;
    let mut v___x_4212_: usize = 0;
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4219_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4193_) == 0 {
                    return v_x_4192_;
                } else {
                    v_key_4194_ = crate::leanh::lean_ctor_get(v_x_4193_, 0);
                    v_value_4195_ = crate::leanh::lean_ctor_get(v_x_4193_, 1);
                    v_tail_4196_ = crate::leanh::lean_ctor_get(v_x_4193_, 2);
                    v_isSharedCheck_4219_ = (!crate::leanh::lean_is_exclusive(v_x_4193_)) as u8;
                    if v_isSharedCheck_4219_ == 0 {
                        v___x_4198_ = v_x_4193_;
                        v_isShared_4199_ = v_isSharedCheck_4219_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4196_);
                        crate::leanh::lean_inc(v_value_4195_);
                        crate::leanh::lean_inc(v_key_4194_);
                        crate::leanh::lean_dec(v_x_4193_);
                        v___x_4198_ = crate::leanh::lean_box(0);
                        v_isShared_4199_ = v_isSharedCheck_4219_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4200_ = lean_array_get_size(v_x_4192_);
                v___x_4201_ = l_Lean_Expr_hash(v_key_4194_);
                v___x_4202_ = 32u64;
                v___x_4203_ = lean_uint64_shift_right(v___x_4201_, v___x_4202_);
                v_fold_4204_ = lean_uint64_xor(v___x_4201_, v___x_4203_);
                v___x_4205_ = 16u64;
                v___x_4206_ = lean_uint64_shift_right(v_fold_4204_, v___x_4205_);
                v___x_4207_ = lean_uint64_xor(v_fold_4204_, v___x_4206_);
                v___x_4208_ = lean_uint64_to_usize(v___x_4207_);
                v___x_4209_ = lean_usize_of_nat(v___x_4200_);
                v___x_4210_ = 1usize;
                v___x_4211_ = lean_usize_sub(v___x_4209_, v___x_4210_);
                v___x_4212_ = lean_usize_land(v___x_4208_, v___x_4211_);
                v___x_4213_ = lean_array_uget_borrowed(v_x_4192_, v___x_4212_);
                crate::leanh::lean_inc(v___x_4213_);
                if v_isShared_4199_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4198_, 2, v___x_4213_);
                    v___x_4215_ = v___x_4198_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4218_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_key_4194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 1, v_value_4195_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 2, v___x_4213_);
                    v___x_4215_ = v_reuseFailAlloc_4218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4216_ = lean_array_uset(v_x_4192_, v___x_4212_, v___x_4215_);
                v_x_4192_ = v___x_4216_;
                v_x_4193_ = v_tail_4196_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(
    mut v_i_4220_: *mut crate::leanh::LeanObject,
    mut v_source_4221_: *mut crate::leanh::LeanObject,
    mut v_target_4222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: u8 = 0;
    let mut v_es_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4223_ = lean_array_get_size(v_source_4221_);
                v___x_4224_ = lean_nat_dec_lt(v_i_4220_, v___x_4223_);
                if v___x_4224_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4221_);
                    crate::leanh::lean_dec(v_i_4220_);
                    return v_target_4222_;
                } else {
                    v_es_4225_ = lean_array_fget(v_source_4221_, v_i_4220_);
                    v___x_4226_ = crate::leanh::lean_box(0);
                    v_source_4227_ = lean_array_fset(v_source_4221_, v_i_4220_, v___x_4226_);
                    v_target_4228_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(v_target_4222_, v_es_4225_);
                    v___x_4229_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4230_ = lean_nat_add(v_i_4220_, v___x_4229_);
                    crate::leanh::lean_dec(v_i_4220_);
                    v_i_4220_ = v___x_4230_;
                    v_source_4221_ = v_source_4227_;
                    v_target_4222_ = v_target_4228_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(
    mut v_data_4232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4233_ = lean_array_get_size(v_data_4232_);
    v___x_4234_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4235_ = lean_nat_mul(v___x_4233_, v___x_4234_);
    v___x_4236_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4237_ = crate::leanh::lean_box(0);
    v___x_4238_ = lean_mk_array(v_nbuckets_4235_, v___x_4237_);
    v___x_4239_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(v___x_4236_, v_data_4232_, v___x_4238_);
    return v___x_4239_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(
    mut v_a_4240_: *mut crate::leanh::LeanObject,
    mut v_b_4241_: *mut crate::leanh::LeanObject,
    mut v_x_4242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v___x_4249_: u8 = 0;
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4242_) == 0 {
                    crate::leanh::lean_dec(v_b_4241_);
                    crate::leanh::lean_dec_ref(v_a_4240_);
                    return v_x_4242_;
                } else {
                    v_key_4243_ = crate::leanh::lean_ctor_get(v_x_4242_, 0);
                    v_value_4244_ = crate::leanh::lean_ctor_get(v_x_4242_, 1);
                    v_tail_4245_ = crate::leanh::lean_ctor_get(v_x_4242_, 2);
                    v_isSharedCheck_4257_ = (!crate::leanh::lean_is_exclusive(v_x_4242_)) as u8;
                    if v_isSharedCheck_4257_ == 0 {
                        v___x_4247_ = v_x_4242_;
                        v_isShared_4248_ = v_isSharedCheck_4257_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4245_);
                        crate::leanh::lean_inc(v_value_4244_);
                        crate::leanh::lean_inc(v_key_4243_);
                        crate::leanh::lean_dec(v_x_4242_);
                        v___x_4247_ = crate::leanh::lean_box(0);
                        v_isShared_4248_ = v_isSharedCheck_4257_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4249_ = lean_expr_eqv(v_key_4243_, v_a_4240_);
                if v___x_4249_ == 0 {
                    v___x_4250_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_4240_, v_b_4241_, v_tail_4245_);
                    if v_isShared_4248_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4247_, 2, v___x_4250_);
                        v___x_4252_ = v___x_4247_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4253_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_key_4243_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4253_, 1, v_value_4244_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4253_, 2, v___x_4250_);
                        v___x_4252_ = v_reuseFailAlloc_4253_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_4244_);
                    crate::leanh::lean_dec(v_key_4243_);
                    if v_isShared_4248_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4247_, 1, v_b_4241_);
                        crate::leanh::lean_ctor_set(v___x_4247_, 0, v_a_4240_);
                        v___x_4255_ = v___x_4247_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4256_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4240_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 1, v_b_4241_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 2, v_tail_4245_);
                        v___x_4255_ = v_reuseFailAlloc_4256_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4252_;
            }
            3 => {
                return v___x_4255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(
    mut v_m_4258_: *mut crate::leanh::LeanObject,
    mut v_a_4259_: *mut crate::leanh::LeanObject,
    mut v_b_4260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4265_: u8 = 0;
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: u64 = 0;
    let mut v___x_4268_: u64 = 0;
    let mut v___x_4269_: u64 = 0;
    let mut v_fold_4270_: u64 = 0;
    let mut v___x_4271_: u64 = 0;
    let mut v___x_4272_: u64 = 0;
    let mut v___x_4273_: u64 = 0;
    let mut v___x_4274_: usize = 0;
    let mut v___x_4275_: usize = 0;
    let mut v___x_4276_: usize = 0;
    let mut v___x_4277_: usize = 0;
    let mut v___x_4278_: usize = 0;
    let mut v_bkt_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: u8 = 0;
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: u8 = 0;
    let mut v_val_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4261_ = crate::leanh::lean_ctor_get(v_m_4258_, 0);
                v_buckets_4262_ = crate::leanh::lean_ctor_get(v_m_4258_, 1);
                v_isSharedCheck_4305_ = (!crate::leanh::lean_is_exclusive(v_m_4258_)) as u8;
                if v_isSharedCheck_4305_ == 0 {
                    v___x_4264_ = v_m_4258_;
                    v_isShared_4265_ = v_isSharedCheck_4305_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4262_);
                    crate::leanh::lean_inc(v_size_4261_);
                    crate::leanh::lean_dec(v_m_4258_);
                    v___x_4264_ = crate::leanh::lean_box(0);
                    v_isShared_4265_ = v_isSharedCheck_4305_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4266_ = lean_array_get_size(v_buckets_4262_);
                v___x_4267_ = l_Lean_Expr_hash(v_a_4259_);
                v___x_4268_ = 32u64;
                v___x_4269_ = lean_uint64_shift_right(v___x_4267_, v___x_4268_);
                v_fold_4270_ = lean_uint64_xor(v___x_4267_, v___x_4269_);
                v___x_4271_ = 16u64;
                v___x_4272_ = lean_uint64_shift_right(v_fold_4270_, v___x_4271_);
                v___x_4273_ = lean_uint64_xor(v_fold_4270_, v___x_4272_);
                v___x_4274_ = lean_uint64_to_usize(v___x_4273_);
                v___x_4275_ = lean_usize_of_nat(v___x_4266_);
                v___x_4276_ = 1usize;
                v___x_4277_ = lean_usize_sub(v___x_4275_, v___x_4276_);
                v___x_4278_ = lean_usize_land(v___x_4274_, v___x_4277_);
                v_bkt_4279_ = lean_array_uget_borrowed(v_buckets_4262_, v___x_4278_);
                v___x_4280_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_4259_, v_bkt_4279_);
                if v___x_4280_ == 0 {
                    v___x_4281_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4282_ = lean_nat_add(v_size_4261_, v___x_4281_);
                    crate::leanh::lean_dec(v_size_4261_);
                    crate::leanh::lean_inc(v_bkt_4279_);
                    v___x_4283_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4283_, 0, v_a_4259_);
                    crate::leanh::lean_ctor_set(v___x_4283_, 1, v_b_4260_);
                    crate::leanh::lean_ctor_set(v___x_4283_, 2, v_bkt_4279_);
                    v_buckets_x27_4284_ =
                        lean_array_uset(v_buckets_4262_, v___x_4278_, v___x_4283_);
                    v___x_4285_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4286_ = lean_nat_mul(v_size_x27_4282_, v___x_4285_);
                    v___x_4287_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4288_ = lean_nat_div(v___x_4286_, v___x_4287_);
                    crate::leanh::lean_dec(v___x_4286_);
                    v___x_4289_ = lean_array_get_size(v_buckets_x27_4284_);
                    v___x_4290_ = lean_nat_dec_le(v___x_4288_, v___x_4289_);
                    crate::leanh::lean_dec(v___x_4288_);
                    if v___x_4290_ == 0 {
                        v_val_4291_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(v_buckets_x27_4284_);
                        if v_isShared_4265_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4264_, 1, v_val_4291_);
                            crate::leanh::lean_ctor_set(v___x_4264_, 0, v_size_x27_4282_);
                            v___x_4293_ = v___x_4264_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4294_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4294_,
                                0,
                                v_size_x27_4282_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4294_, 1, v_val_4291_);
                            v___x_4293_ = v_reuseFailAlloc_4294_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_4265_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4264_, 1, v_buckets_x27_4284_);
                            crate::leanh::lean_ctor_set(v___x_4264_, 0, v_size_x27_4282_);
                            v___x_4296_ = v___x_4264_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4297_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4297_,
                                0,
                                v_size_x27_4282_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4297_,
                                1,
                                v_buckets_x27_4284_,
                            );
                            v___x_4296_ = v_reuseFailAlloc_4297_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_4279_);
                    v___x_4298_ = crate::leanh::lean_box(0);
                    v_buckets_x27_4299_ =
                        lean_array_uset(v_buckets_4262_, v___x_4278_, v___x_4298_);
                    v___x_4300_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_4259_, v_b_4260_, v_bkt_4279_);
                    v___x_4301_ = lean_array_uset(v_buckets_x27_4299_, v___x_4278_, v___x_4300_);
                    if v_isShared_4265_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4264_, 1, v___x_4301_);
                        v___x_4303_ = v___x_4264_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4304_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_size_4261_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4304_, 1, v___x_4301_);
                        v___x_4303_ = v_reuseFailAlloc_4304_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4293_;
            }
            3 => {
                return v___x_4296_;
            }
            4 => {
                return v___x_4303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(
    mut v_msgData_4306_: *mut crate::leanh::LeanObject,
    mut v___y_4307_: *mut crate::leanh::LeanObject,
    mut v___y_4308_: *mut crate::leanh::LeanObject,
    mut v___y_4309_: *mut crate::leanh::LeanObject,
    mut v___y_4310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4312_ = lean_st_ref_get(v___y_4310_);
    v_env_4313_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
    crate::leanh::lean_inc_ref(v_env_4313_);
    crate::leanh::lean_dec(v___x_4312_);
    v___x_4314_ = lean_st_ref_get(v___y_4308_);
    v_mctx_4315_ = crate::leanh::lean_ctor_get(v___x_4314_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4315_);
    crate::leanh::lean_dec(v___x_4314_);
    v_lctx_4316_ = crate::leanh::lean_ctor_get(v___y_4307_, 2);
    v_options_4317_ = crate::leanh::lean_ctor_get(v___y_4309_, 2);
    crate::leanh::lean_inc_ref(v_options_4317_);
    crate::leanh::lean_inc_ref(v_lctx_4316_);
    v___x_4318_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4318_, 0, v_env_4313_);
    crate::leanh::lean_ctor_set(v___x_4318_, 1, v_mctx_4315_);
    crate::leanh::lean_ctor_set(v___x_4318_, 2, v_lctx_4316_);
    crate::leanh::lean_ctor_set(v___x_4318_, 3, v_options_4317_);
    v___x_4319_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4319_, 0, v___x_4318_);
    crate::leanh::lean_ctor_set(v___x_4319_, 1, v_msgData_4306_);
    v___x_4320_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4320_, 0, v___x_4319_);
    return v___x_4320_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8___boxed(
    mut v_msgData_4321_: *mut crate::leanh::LeanObject,
    mut v___y_4322_: *mut crate::leanh::LeanObject,
    mut v___y_4323_: *mut crate::leanh::LeanObject,
    mut v___y_4324_: *mut crate::leanh::LeanObject,
    mut v___y_4325_: *mut crate::leanh::LeanObject,
    mut v___y_4326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4327_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(v_msgData_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
    crate::leanh::lean_dec(v___y_4325_);
    crate::leanh::lean_dec_ref(v___y_4324_);
    crate::leanh::lean_dec(v___y_4323_);
    crate::leanh::lean_dec_ref(v___y_4322_);
    return v_res_4327_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0()
-> f64 {
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: f64 = 0.0;
    v___x_4328_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4329_ = lean_float_of_nat(v___x_4328_);
    return v___x_4329_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(
    mut v_cls_4333_: *mut crate::leanh::LeanObject,
    mut v_msg_4334_: *mut crate::leanh::LeanObject,
    mut v___y_4335_: *mut crate::leanh::LeanObject,
    mut v___y_4336_: *mut crate::leanh::LeanObject,
    mut v___y_4337_: *mut crate::leanh::LeanObject,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4345_: u8 = 0;
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v_tid_4359_: u64 = 0;
    let mut v_traces_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4363_: u8 = 0;
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: f64 = 0.0;
    let mut v___x_4366_: u8 = 0;
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4384_: u8 = 0;
    let mut v_isSharedCheck_4385_: u8 = 0;
    let mut v_isSharedCheck_4386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4340_ = crate::leanh::lean_ctor_get(v___y_4337_, 5);
                v___x_4341_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(v_msg_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
                v_a_4342_ = crate::leanh::lean_ctor_get(v___x_4341_, 0);
                v_isSharedCheck_4386_ = (!crate::leanh::lean_is_exclusive(v___x_4341_)) as u8;
                if v_isSharedCheck_4386_ == 0 {
                    v___x_4344_ = v___x_4341_;
                    v_isShared_4345_ = v_isSharedCheck_4386_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4342_);
                    crate::leanh::lean_dec(v___x_4341_);
                    v___x_4344_ = crate::leanh::lean_box(0);
                    v_isShared_4345_ = v_isSharedCheck_4386_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4346_ = lean_st_ref_take(v___y_4338_);
                v_traceState_4347_ = crate::leanh::lean_ctor_get(v___x_4346_, 4);
                v_env_4348_ = crate::leanh::lean_ctor_get(v___x_4346_, 0);
                v_nextMacroScope_4349_ = crate::leanh::lean_ctor_get(v___x_4346_, 1);
                v_ngen_4350_ = crate::leanh::lean_ctor_get(v___x_4346_, 2);
                v_auxDeclNGen_4351_ = crate::leanh::lean_ctor_get(v___x_4346_, 3);
                v_cache_4352_ = crate::leanh::lean_ctor_get(v___x_4346_, 5);
                v_messages_4353_ = crate::leanh::lean_ctor_get(v___x_4346_, 6);
                v_infoState_4354_ = crate::leanh::lean_ctor_get(v___x_4346_, 7);
                v_snapshotTasks_4355_ = crate::leanh::lean_ctor_get(v___x_4346_, 8);
                v_isSharedCheck_4385_ = (!crate::leanh::lean_is_exclusive(v___x_4346_)) as u8;
                if v_isSharedCheck_4385_ == 0 {
                    v___x_4357_ = v___x_4346_;
                    v_isShared_4358_ = v_isSharedCheck_4385_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4355_);
                    crate::leanh::lean_inc(v_infoState_4354_);
                    crate::leanh::lean_inc(v_messages_4353_);
                    crate::leanh::lean_inc(v_cache_4352_);
                    crate::leanh::lean_inc(v_traceState_4347_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4351_);
                    crate::leanh::lean_inc(v_ngen_4350_);
                    crate::leanh::lean_inc(v_nextMacroScope_4349_);
                    crate::leanh::lean_inc(v_env_4348_);
                    crate::leanh::lean_dec(v___x_4346_);
                    v___x_4357_ = crate::leanh::lean_box(0);
                    v_isShared_4358_ = v_isSharedCheck_4385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4359_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_4347_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4360_ = crate::leanh::lean_ctor_get(v_traceState_4347_, 0);
                v_isSharedCheck_4384_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_4347_)) as u8;
                if v_isSharedCheck_4384_ == 0 {
                    v___x_4362_ = v_traceState_4347_;
                    v_isShared_4363_ = v_isSharedCheck_4384_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4360_);
                    crate::leanh::lean_dec(v_traceState_4347_);
                    v___x_4362_ = crate::leanh::lean_box(0);
                    v_isShared_4363_ = v_isSharedCheck_4384_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4364_ = crate::leanh::lean_box(0);
                v___x_4365_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0);
                v___x_4366_ = 0;
                v___x_4367_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1;
                v___x_4368_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_4368_, 0, v_cls_4333_);
                crate::leanh::lean_ctor_set(v___x_4368_, 1, v___x_4364_);
                crate::leanh::lean_ctor_set(v___x_4368_, 2, v___x_4367_);
                crate::leanh::lean_ctor_set_float(
                    v___x_4368_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4365_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_4368_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4365_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4368_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4366_,
                );
                v___x_4369_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2;
                v___x_4370_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4370_, 0, v___x_4368_);
                crate::leanh::lean_ctor_set(v___x_4370_, 1, v_a_4342_);
                crate::leanh::lean_ctor_set(v___x_4370_, 2, v___x_4369_);
                crate::leanh::lean_inc(v_ref_4340_);
                v___x_4371_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4371_, 0, v_ref_4340_);
                crate::leanh::lean_ctor_set(v___x_4371_, 1, v___x_4370_);
                v___x_4372_ = l_Lean_PersistentArray_push___redArg(v_traces_4360_, v___x_4371_);
                if v_isShared_4363_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4362_, 0, v___x_4372_);
                    v___x_4374_ = v___x_4362_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4383_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4372_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4383_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_4359_,
                    );
                    v___x_4374_ = v_reuseFailAlloc_4383_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4358_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4357_, 4, v___x_4374_);
                    v___x_4376_ = v___x_4357_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4382_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_env_4348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_nextMacroScope_4349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 2, v_ngen_4350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 3, v_auxDeclNGen_4351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 4, v___x_4374_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 5, v_cache_4352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 6, v_messages_4353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 7, v_infoState_4354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 8, v_snapshotTasks_4355_);
                    v___x_4376_ = v_reuseFailAlloc_4382_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4377_ = lean_st_ref_set(v___y_4338_, v___x_4376_);
                v___x_4378_ = crate::leanh::lean_box(0);
                if v_isShared_4345_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4344_, 0, v___x_4378_);
                    v___x_4380_ = v___x_4344_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4381_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4378_);
                    v___x_4380_ = v_reuseFailAlloc_4381_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4380_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___boxed(
    mut v_cls_4387_: *mut crate::leanh::LeanObject,
    mut v_msg_4388_: *mut crate::leanh::LeanObject,
    mut v___y_4389_: *mut crate::leanh::LeanObject,
    mut v___y_4390_: *mut crate::leanh::LeanObject,
    mut v___y_4391_: *mut crate::leanh::LeanObject,
    mut v___y_4392_: *mut crate::leanh::LeanObject,
    mut v___y_4393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4394_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(
        v_cls_4387_,
        v_msg_4388_,
        v___y_4389_,
        v___y_4390_,
        v___y_4391_,
        v___y_4392_,
    );
    crate::leanh::lean_dec(v___y_4392_);
    crate::leanh::lean_dec_ref(v___y_4391_);
    crate::leanh::lean_dec(v___y_4390_);
    crate::leanh::lean_dec_ref(v___y_4389_);
    return v_res_4394_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(
    mut v_x_4395_: *mut crate::leanh::LeanObject,
    mut v_x_4396_: *mut crate::leanh::LeanObject,
    mut v___y_4397_: *mut crate::leanh::LeanObject,
    mut v___y_4398_: *mut crate::leanh::LeanObject,
    mut v___y_4399_: *mut crate::leanh::LeanObject,
    mut v___y_4400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4408_: u8 = 0;
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4418_: u8 = 0;
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4422_: u8 = 0;
    let mut v_isSharedCheck_4423_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4395_) == 0 {
                    v___x_4402_ = l_List_reverse___redArg(v_x_4396_);
                    v___x_4403_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4403_, 0, v___x_4402_);
                    return v___x_4403_;
                } else {
                    v_head_4404_ = crate::leanh::lean_ctor_get(v_x_4395_, 0);
                    v_tail_4405_ = crate::leanh::lean_ctor_get(v_x_4395_, 1);
                    v_isSharedCheck_4423_ = (!crate::leanh::lean_is_exclusive(v_x_4395_)) as u8;
                    if v_isSharedCheck_4423_ == 0 {
                        v___x_4407_ = v_x_4395_;
                        v_isShared_4408_ = v_isSharedCheck_4423_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4405_);
                        crate::leanh::lean_inc(v_head_4404_);
                        crate::leanh::lean_dec(v_x_4395_);
                        v___x_4407_ = crate::leanh::lean_box(0);
                        v_isShared_4408_ = v_isSharedCheck_4423_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_4400_);
                crate::leanh::lean_inc_ref(v___y_4399_);
                crate::leanh::lean_inc(v___y_4398_);
                crate::leanh::lean_inc_ref(v___y_4397_);
                v___x_4409_ = lean_infer_type(
                    v_head_4404_,
                    v___y_4397_,
                    v___y_4398_,
                    v___y_4399_,
                    v___y_4400_,
                );
                if crate::leanh::lean_obj_tag(v___x_4409_) == 0 {
                    v_a_4410_ = crate::leanh::lean_ctor_get(v___x_4409_, 0);
                    crate::leanh::lean_inc(v_a_4410_);
                    crate::leanh::lean_dec_ref_known(v___x_4409_, 1);
                    if v_isShared_4408_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4407_, 1, v_x_4396_);
                        crate::leanh::lean_ctor_set(v___x_4407_, 0, v_a_4410_);
                        v___x_4412_ = v___x_4407_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4414_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4410_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 1, v_x_4396_);
                        v___x_4412_ = v_reuseFailAlloc_4414_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4407_);
                    crate::leanh::lean_dec(v_tail_4405_);
                    crate::leanh::lean_dec(v_x_4396_);
                    v_a_4415_ = crate::leanh::lean_ctor_get(v___x_4409_, 0);
                    v_isSharedCheck_4422_ = (!crate::leanh::lean_is_exclusive(v___x_4409_)) as u8;
                    if v_isSharedCheck_4422_ == 0 {
                        v___x_4417_ = v___x_4409_;
                        v_isShared_4418_ = v_isSharedCheck_4422_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4415_);
                        crate::leanh::lean_dec(v___x_4409_);
                        v___x_4417_ = crate::leanh::lean_box(0);
                        v_isShared_4418_ = v_isSharedCheck_4422_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4395_ = v_tail_4405_;
                v_x_4396_ = v___x_4412_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4418_ == 0 {
                    v___x_4420_ = v___x_4417_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4421_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
                    v___x_4420_ = v_reuseFailAlloc_4421_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___boxed(
    mut v_x_4424_: *mut crate::leanh::LeanObject,
    mut v_x_4425_: *mut crate::leanh::LeanObject,
    mut v___y_4426_: *mut crate::leanh::LeanObject,
    mut v___y_4427_: *mut crate::leanh::LeanObject,
    mut v___y_4428_: *mut crate::leanh::LeanObject,
    mut v___y_4429_: *mut crate::leanh::LeanObject,
    mut v___y_4430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4431_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(
        v_x_4424_,
        v_x_4425_,
        v___y_4426_,
        v___y_4427_,
        v___y_4428_,
        v___y_4429_,
    );
    crate::leanh::lean_dec(v___y_4429_);
    crate::leanh::lean_dec_ref(v___y_4428_);
    crate::leanh::lean_dec(v___y_4427_);
    crate::leanh::lean_dec_ref(v___y_4426_);
    return v_res_4431_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(
    mut v_a_4432_: *mut crate::leanh::LeanObject,
    mut v_a_4433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4439_: u8 = 0;
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4445_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4432_) == 0 {
                    v___x_4434_ = l_List_reverse___redArg(v_a_4433_);
                    return v___x_4434_;
                } else {
                    v_head_4435_ = crate::leanh::lean_ctor_get(v_a_4432_, 0);
                    v_tail_4436_ = crate::leanh::lean_ctor_get(v_a_4432_, 1);
                    v_isSharedCheck_4445_ = (!crate::leanh::lean_is_exclusive(v_a_4432_)) as u8;
                    if v_isSharedCheck_4445_ == 0 {
                        v___x_4438_ = v_a_4432_;
                        v_isShared_4439_ = v_isSharedCheck_4445_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4436_);
                        crate::leanh::lean_inc(v_head_4435_);
                        crate::leanh::lean_dec(v_a_4432_);
                        v___x_4438_ = crate::leanh::lean_box(0);
                        v_isShared_4439_ = v_isSharedCheck_4445_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4440_ = l_Lean_MessageData_ofExpr(v_head_4435_);
                if v_isShared_4439_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4438_, 1, v_a_4433_);
                    crate::leanh::lean_ctor_set(v___x_4438_, 0, v___x_4440_);
                    v___x_4442_ = v___x_4438_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4444_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4444_, 1, v_a_4433_);
                    v___x_4442_ = v_reuseFailAlloc_4444_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4432_ = v_tail_4436_;
                v_a_4433_ = v___x_4442_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4452_ = l_Lean_Elab_Tactic_Omega_lookup___closed__1;
    v___x_4453_ = l_Lean_Elab_Tactic_Omega_lookup___closed__3;
    v___x_4454_ = l_Lean_Name_append(v___x_4453_, v___x_4452_);
    return v___x_4454_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4456_ = l_Lean_Elab_Tactic_Omega_lookup___closed__5;
    v___x_4457_ = l_Lean_stringToMessageData(v___x_4456_);
    return v___x_4457_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_lookup___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4459_ = l_Lean_Elab_Tactic_Omega_lookup___closed__7;
    v___x_4460_ = l_Lean_stringToMessageData(v___x_4459_);
    return v___x_4460_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_lookup(
    mut v_e_4461_: *mut crate::leanh::LeanObject,
    mut v_a_4462_: *mut crate::leanh::LeanObject,
    mut v_a_4463_: *mut crate::leanh::LeanObject,
    mut v_a_4464_: *mut crate::leanh::LeanObject,
    mut v_a_4465_: u8,
    mut v_a_4466_: *mut crate::leanh::LeanObject,
    mut v_a_4467_: *mut crate::leanh::LeanObject,
    mut v_a_4468_: *mut crate::leanh::LeanObject,
    mut v_a_4469_: *mut crate::leanh::LeanObject,
    mut v_a_4470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4477_: u8 = 0;
    let mut v___y_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4493_: u8 = 0;
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4499_: u8 = 0;
    let mut v___y_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4507_: u8 = 0;
    let mut v_a_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: u8 = 0;
    let mut v___x_4513_: u8 = 0;
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4525_: u8 = 0;
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4529_: u8 = 0;
    let mut v_a_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4533_: u8 = 0;
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4537_: u8 = 0;
    let mut v_a_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4541_: u8 = 0;
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4545_: u8 = 0;
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: u8 = 0;
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4555_: u8 = 0;
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4559_: u8 = 0;
    let mut v_val_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4563_: u8 = 0;
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4569_: u8 = 0;
    let mut v_isSharedCheck_4570_: u8 = 0;
    let mut v_a_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4574_: u8 = 0;
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4472_ = lean_st_ref_get(v_a_4463_);
                v___x_4473_ = l_Lean_Meta_Canonicalizer_canon(
                    v_e_4461_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_,
                );
                if crate::leanh::lean_obj_tag(v___x_4473_) == 0 {
                    v_a_4474_ = crate::leanh::lean_ctor_get(v___x_4473_, 0);
                    v_isSharedCheck_4570_ = (!crate::leanh::lean_is_exclusive(v___x_4473_)) as u8;
                    if v_isSharedCheck_4570_ == 0 {
                        v___x_4476_ = v___x_4473_;
                        v_isShared_4477_ = v_isSharedCheck_4570_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4474_);
                        crate::leanh::lean_dec(v___x_4473_);
                        v___x_4476_ = crate::leanh::lean_box(0);
                        v_isShared_4477_ = v_isSharedCheck_4570_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4472_);
                    v_a_4571_ = crate::leanh::lean_ctor_get(v___x_4473_, 0);
                    v_isSharedCheck_4578_ = (!crate::leanh::lean_is_exclusive(v___x_4473_)) as u8;
                    if v_isSharedCheck_4578_ == 0 {
                        v___x_4573_ = v___x_4473_;
                        v_isShared_4574_ = v_isSharedCheck_4578_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4571_);
                        crate::leanh::lean_dec(v___x_4473_);
                        v___x_4573_ = crate::leanh::lean_box(0);
                        v_isShared_4574_ = v_isSharedCheck_4578_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v___x_4472_, v_a_4474_);
                crate::leanh::lean_dec(v___x_4472_);
                if crate::leanh::lean_obj_tag(v___x_4490_) == 0 {
                    v_options_4491_ = crate::leanh::lean_ctor_get(v_a_4469_, 2);
                    v_inheritedTraceOptions_4492_ = crate::leanh::lean_ctor_get(v_a_4469_, 13);
                    v_hasTrace_4493_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_4491_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_4494_ = l_Lean_Elab_Tactic_Omega_lookup___closed__1;
                    if v_hasTrace_4493_ == 0 {
                        v___y_4496_ = v_a_4462_;
                        v___y_4497_ = v_a_4463_;
                        v___y_4498_ = v_a_4464_;
                        v___y_4499_ = v_a_4465_;
                        v___y_4500_ = v_a_4466_;
                        v___y_4501_ = v_a_4467_;
                        v___y_4502_ = v_a_4468_;
                        v___y_4503_ = v_a_4469_;
                        v___y_4504_ = v_a_4470_;
                        state = 4;
                        continue;
                    } else {
                        v___x_4546_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_lookup___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Omega_lookup___closed__4_once
                            ),
                            _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4,
                        );
                        v___x_4547_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4492_,
                            v_options_4491_,
                            v___x_4546_,
                        );
                        if v___x_4547_ == 0 {
                            v___y_4496_ = v_a_4462_;
                            v___y_4497_ = v_a_4463_;
                            v___y_4498_ = v_a_4464_;
                            v___y_4499_ = v_a_4465_;
                            v___y_4500_ = v_a_4466_;
                            v___y_4501_ = v_a_4467_;
                            v___y_4502_ = v_a_4468_;
                            v___y_4503_ = v_a_4469_;
                            v___y_4504_ = v_a_4470_;
                            state = 4;
                            continue;
                        } else {
                            v___x_4548_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_Omega_lookup___closed__8
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_Omega_lookup___closed__8_once
                                ),
                                _init_l_Lean_Elab_Tactic_Omega_lookup___closed__8,
                            );
                            crate::leanh::lean_inc(v_a_4474_);
                            v___x_4549_ = l_Lean_MessageData_ofExpr(v_a_4474_);
                            v___x_4550_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4550_, 0, v___x_4548_);
                            crate::leanh::lean_ctor_set(v___x_4550_, 1, v___x_4549_);
                            v___x_4551_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v___x_4494_, v___x_4550_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
                            if crate::leanh::lean_obj_tag(v___x_4551_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4551_, 1);
                                v___y_4496_ = v_a_4462_;
                                v___y_4497_ = v_a_4463_;
                                v___y_4498_ = v_a_4464_;
                                v___y_4499_ = v_a_4465_;
                                v___y_4500_ = v_a_4466_;
                                v___y_4501_ = v_a_4467_;
                                v___y_4502_ = v_a_4468_;
                                v___y_4503_ = v_a_4469_;
                                v___y_4504_ = v_a_4470_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_4476_);
                                crate::leanh::lean_dec(v_a_4474_);
                                v_a_4552_ = crate::leanh::lean_ctor_get(v___x_4551_, 0);
                                v_isSharedCheck_4559_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4551_)) as u8;
                                if v_isSharedCheck_4559_ == 0 {
                                    v___x_4554_ = v___x_4551_;
                                    v_isShared_4555_ = v_isSharedCheck_4559_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4552_);
                                    crate::leanh::lean_dec(v___x_4551_);
                                    v___x_4554_ = crate::leanh::lean_box(0);
                                    v_isShared_4555_ = v_isSharedCheck_4559_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4476_);
                    crate::leanh::lean_dec(v_a_4474_);
                    v_val_4560_ = crate::leanh::lean_ctor_get(v___x_4490_, 0);
                    v_isSharedCheck_4569_ = (!crate::leanh::lean_is_exclusive(v___x_4490_)) as u8;
                    if v_isSharedCheck_4569_ == 0 {
                        v___x_4562_ = v___x_4490_;
                        v_isShared_4563_ = v_isSharedCheck_4569_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4560_);
                        crate::leanh::lean_dec(v___x_4490_);
                        v___x_4562_ = crate::leanh::lean_box(0);
                        v_isShared_4563_ = v_isSharedCheck_4569_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4481_ = lean_st_ref_take(v___y_4480_);
                v_size_4482_ = crate::leanh::lean_ctor_get(v___x_4481_, 0);
                crate::leanh::lean_inc_n(v_size_4482_, 2);
                v___x_4483_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v___x_4481_, v_a_4474_, v_size_4482_);
                v___x_4484_ = lean_st_ref_set(v___y_4480_, v___x_4483_);
                v___x_4485_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4485_, 0, v___y_4479_);
                v___x_4486_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4486_, 0, v_size_4482_);
                crate::leanh::lean_ctor_set(v___x_4486_, 1, v___x_4485_);
                if v_isShared_4477_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4476_, 0, v___x_4486_);
                    v___x_4488_ = v___x_4476_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4489_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4489_, 0, v___x_4486_);
                    v___x_4488_ = v_reuseFailAlloc_4489_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4488_;
            }
            4 => {
                crate::leanh::lean_inc(v_a_4474_);
                v___x_4505_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(
                    v_a_4474_,
                    v___y_4498_,
                    v___y_4501_,
                    v___y_4502_,
                    v___y_4503_,
                    v___y_4504_,
                );
                if crate::leanh::lean_obj_tag(v___x_4505_) == 0 {
                    v_options_4506_ = crate::leanh::lean_ctor_get(v___y_4503_, 2);
                    v_hasTrace_4507_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_4506_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4507_ == 0 {
                        v_a_4508_ = crate::leanh::lean_ctor_get(v___x_4505_, 0);
                        crate::leanh::lean_inc(v_a_4508_);
                        crate::leanh::lean_dec_ref_known(v___x_4505_, 1);
                        v___y_4479_ = v_a_4508_;
                        v___y_4480_ = v___y_4497_;
                        state = 2;
                        continue;
                    } else {
                        v_a_4509_ = crate::leanh::lean_ctor_get(v___x_4505_, 0);
                        crate::leanh::lean_inc(v_a_4509_);
                        crate::leanh::lean_dec_ref_known(v___x_4505_, 1);
                        v_inheritedTraceOptions_4510_ =
                            crate::leanh::lean_ctor_get(v___y_4503_, 13);
                        v___x_4511_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_lookup___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Omega_lookup___closed__4_once
                            ),
                            _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4,
                        );
                        v___x_4512_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4510_,
                            v_options_4506_,
                            v___x_4511_,
                        );
                        if v___x_4512_ == 0 {
                            v___y_4479_ = v_a_4509_;
                            v___y_4480_ = v___y_4497_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4513_ = l_List_isEmpty___redArg(v_a_4509_);
                            if v___x_4513_ == 0 {
                                if v___x_4512_ == 0 {
                                    v___y_4479_ = v_a_4509_;
                                    v___y_4480_ = v___y_4497_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_4514_ = crate::leanh::lean_box(0);
                                    crate::leanh::lean_inc(v_a_4509_);
                                    v___x_4515_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_a_4509_, v___x_4514_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
                                    if crate::leanh::lean_obj_tag(v___x_4515_) == 0 {
                                        v_a_4516_ = crate::leanh::lean_ctor_get(v___x_4515_, 0);
                                        crate::leanh::lean_inc(v_a_4516_);
                                        crate::leanh::lean_dec_ref_known(v___x_4515_, 1);
                                        v___x_4517_ = crate::leanh::lean_obj_once(
                                            core::ptr::addr_of_mut!(
                                                l_Lean_Elab_Tactic_Omega_lookup___closed__6
                                            ),
                                            core::ptr::addr_of_mut!(
                                                l_Lean_Elab_Tactic_Omega_lookup___closed__6_once
                                            ),
                                            _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6,
                                        );
                                        v___x_4518_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(v_a_4516_, v___x_4514_);
                                        v___x_4519_ = l_Lean_MessageData_ofList(v___x_4518_);
                                        v___x_4520_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4520_, 0, v___x_4517_);
                                        crate::leanh::lean_ctor_set(v___x_4520_, 1, v___x_4519_);
                                        v___x_4521_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v___x_4494_, v___x_4520_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
                                        if crate::leanh::lean_obj_tag(v___x_4521_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_4521_, 1);
                                            v___y_4479_ = v_a_4509_;
                                            v___y_4480_ = v___y_4497_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_a_4509_);
                                            crate::leanh::lean_del_object(v___x_4476_);
                                            crate::leanh::lean_dec(v_a_4474_);
                                            v_a_4522_ = crate::leanh::lean_ctor_get(v___x_4521_, 0);
                                            v_isSharedCheck_4529_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4521_))
                                                    as u8;
                                            if v_isSharedCheck_4529_ == 0 {
                                                v___x_4524_ = v___x_4521_;
                                                v_isShared_4525_ = v_isSharedCheck_4529_;
                                                state = 5;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_4522_);
                                                crate::leanh::lean_dec(v___x_4521_);
                                                v___x_4524_ = crate::leanh::lean_box(0);
                                                v_isShared_4525_ = v_isSharedCheck_4529_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_4509_);
                                        crate::leanh::lean_del_object(v___x_4476_);
                                        crate::leanh::lean_dec(v_a_4474_);
                                        v_a_4530_ = crate::leanh::lean_ctor_get(v___x_4515_, 0);
                                        v_isSharedCheck_4537_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4515_)) as u8;
                                        if v_isSharedCheck_4537_ == 0 {
                                            v___x_4532_ = v___x_4515_;
                                            v_isShared_4533_ = v_isSharedCheck_4537_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4530_);
                                            crate::leanh::lean_dec(v___x_4515_);
                                            v___x_4532_ = crate::leanh::lean_box(0);
                                            v_isShared_4533_ = v_isSharedCheck_4537_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___y_4479_ = v_a_4509_;
                                v___y_4480_ = v___y_4497_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4476_);
                    crate::leanh::lean_dec(v_a_4474_);
                    v_a_4538_ = crate::leanh::lean_ctor_get(v___x_4505_, 0);
                    v_isSharedCheck_4545_ = (!crate::leanh::lean_is_exclusive(v___x_4505_)) as u8;
                    if v_isSharedCheck_4545_ == 0 {
                        v___x_4540_ = v___x_4505_;
                        v_isShared_4541_ = v_isSharedCheck_4545_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4538_);
                        crate::leanh::lean_dec(v___x_4505_);
                        v___x_4540_ = crate::leanh::lean_box(0);
                        v_isShared_4541_ = v_isSharedCheck_4545_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_4525_ == 0 {
                    v___x_4527_ = v___x_4524_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4528_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
                    v___x_4527_ = v_reuseFailAlloc_4528_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4527_;
            }
            7 => {
                if v_isShared_4533_ == 0 {
                    v___x_4535_ = v___x_4532_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4530_);
                    v___x_4535_ = v_reuseFailAlloc_4536_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4535_;
            }
            9 => {
                if v_isShared_4541_ == 0 {
                    v___x_4543_ = v___x_4540_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
                    v___x_4543_ = v_reuseFailAlloc_4544_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4543_;
            }
            11 => {
                if v_isShared_4555_ == 0 {
                    v___x_4557_ = v___x_4554_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4558_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
                    v___x_4557_ = v_reuseFailAlloc_4558_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4557_;
            }
            13 => {
                v___x_4564_ = crate::leanh::lean_box(0);
                v___x_4565_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4565_, 0, v_val_4560_);
                crate::leanh::lean_ctor_set(v___x_4565_, 1, v___x_4564_);
                if v_isShared_4563_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4562_, 0);
                    crate::leanh::lean_ctor_set(v___x_4562_, 0, v___x_4565_);
                    v___x_4567_ = v___x_4562_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4568_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4568_, 0, v___x_4565_);
                    v___x_4567_ = v_reuseFailAlloc_4568_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4567_;
            }
            15 => {
                if v_isShared_4574_ == 0 {
                    v___x_4576_ = v___x_4573_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4577_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
                    v___x_4576_ = v_reuseFailAlloc_4577_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_lookup___boxed(
    mut v_e_4579_: *mut crate::leanh::LeanObject,
    mut v_a_4580_: *mut crate::leanh::LeanObject,
    mut v_a_4581_: *mut crate::leanh::LeanObject,
    mut v_a_4582_: *mut crate::leanh::LeanObject,
    mut v_a_4583_: *mut crate::leanh::LeanObject,
    mut v_a_4584_: *mut crate::leanh::LeanObject,
    mut v_a_4585_: *mut crate::leanh::LeanObject,
    mut v_a_4586_: *mut crate::leanh::LeanObject,
    mut v_a_4587_: *mut crate::leanh::LeanObject,
    mut v_a_4588_: *mut crate::leanh::LeanObject,
    mut v_a_4589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4590_: u8 = 0;
    let mut v_res_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4590_ = (crate::leanh::lean_unbox(v_a_4583_) as u8);
    v_res_4591_ = l_Lean_Elab_Tactic_Omega_lookup(
        v_e_4579_,
        v_a_4580_,
        v_a_4581_,
        v_a_4582_,
        v_a_boxed_4590_,
        v_a_4584_,
        v_a_4585_,
        v_a_4586_,
        v_a_4587_,
        v_a_4588_,
    );
    crate::leanh::lean_dec(v_a_4588_);
    crate::leanh::lean_dec_ref(v_a_4587_);
    crate::leanh::lean_dec(v_a_4586_);
    crate::leanh::lean_dec_ref(v_a_4585_);
    crate::leanh::lean_dec(v_a_4584_);
    crate::leanh::lean_dec_ref(v_a_4582_);
    crate::leanh::lean_dec(v_a_4581_);
    crate::leanh::lean_dec(v_a_4580_);
    return v_res_4591_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(
    mut v_00_u03b2_4592_: *mut crate::leanh::LeanObject,
    mut v_m_4593_: *mut crate::leanh::LeanObject,
    mut v_a_4594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4595_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_4593_, v_a_4594_);
    return v___x_4595_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(
    mut v_00_u03b2_4596_: *mut crate::leanh::LeanObject,
    mut v_m_4597_: *mut crate::leanh::LeanObject,
    mut v_a_4598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(v_00_u03b2_4596_, v_m_4597_, v_a_4598_);
    crate::leanh::lean_dec_ref(v_a_4598_);
    crate::leanh::lean_dec_ref(v_m_4597_);
    return v_res_4599_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1(
    mut v_00_u03b2_4600_: *mut crate::leanh::LeanObject,
    mut v_m_4601_: *mut crate::leanh::LeanObject,
    mut v_a_4602_: *mut crate::leanh::LeanObject,
    mut v_b_4603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4604_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v_m_4601_, v_a_4602_, v_b_4603_);
    return v___x_4604_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(
    mut v_x_4605_: *mut crate::leanh::LeanObject,
    mut v_x_4606_: *mut crate::leanh::LeanObject,
    mut v___y_4607_: *mut crate::leanh::LeanObject,
    mut v___y_4608_: *mut crate::leanh::LeanObject,
    mut v___y_4609_: *mut crate::leanh::LeanObject,
    mut v___y_4610_: u8,
    mut v___y_4611_: *mut crate::leanh::LeanObject,
    mut v___y_4612_: *mut crate::leanh::LeanObject,
    mut v___y_4613_: *mut crate::leanh::LeanObject,
    mut v___y_4614_: *mut crate::leanh::LeanObject,
    mut v___y_4615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4617_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(
        v_x_4605_,
        v_x_4606_,
        v___y_4612_,
        v___y_4613_,
        v___y_4614_,
        v___y_4615_,
    );
    return v___x_4617_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___boxed(
    mut v_x_4618_: *mut crate::leanh::LeanObject,
    mut v_x_4619_: *mut crate::leanh::LeanObject,
    mut v___y_4620_: *mut crate::leanh::LeanObject,
    mut v___y_4621_: *mut crate::leanh::LeanObject,
    mut v___y_4622_: *mut crate::leanh::LeanObject,
    mut v___y_4623_: *mut crate::leanh::LeanObject,
    mut v___y_4624_: *mut crate::leanh::LeanObject,
    mut v___y_4625_: *mut crate::leanh::LeanObject,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
    mut v___y_4628_: *mut crate::leanh::LeanObject,
    mut v___y_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_42932__boxed_4630_: u8 = 0;
    let mut v_res_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_42932__boxed_4630_ = (crate::leanh::lean_unbox(v___y_4623_) as u8);
    v_res_4631_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(
        v_x_4618_,
        v_x_4619_,
        v___y_4620_,
        v___y_4621_,
        v___y_4622_,
        v___y_42932__boxed_4630_,
        v___y_4624_,
        v___y_4625_,
        v___y_4626_,
        v___y_4627_,
        v___y_4628_,
    );
    crate::leanh::lean_dec(v___y_4628_);
    crate::leanh::lean_dec_ref(v___y_4627_);
    crate::leanh::lean_dec(v___y_4626_);
    crate::leanh::lean_dec_ref(v___y_4625_);
    crate::leanh::lean_dec(v___y_4624_);
    crate::leanh::lean_dec_ref(v___y_4622_);
    crate::leanh::lean_dec(v___y_4621_);
    crate::leanh::lean_dec(v___y_4620_);
    return v_res_4631_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(
    mut v_cls_4632_: *mut crate::leanh::LeanObject,
    mut v_msg_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
    mut v___y_4635_: *mut crate::leanh::LeanObject,
    mut v___y_4636_: *mut crate::leanh::LeanObject,
    mut v___y_4637_: u8,
    mut v___y_4638_: *mut crate::leanh::LeanObject,
    mut v___y_4639_: *mut crate::leanh::LeanObject,
    mut v___y_4640_: *mut crate::leanh::LeanObject,
    mut v___y_4641_: *mut crate::leanh::LeanObject,
    mut v___y_4642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4644_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(
        v_cls_4632_,
        v_msg_4633_,
        v___y_4639_,
        v___y_4640_,
        v___y_4641_,
        v___y_4642_,
    );
    return v___x_4644_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___boxed(
    mut v_cls_4645_: *mut crate::leanh::LeanObject,
    mut v_msg_4646_: *mut crate::leanh::LeanObject,
    mut v___y_4647_: *mut crate::leanh::LeanObject,
    mut v___y_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
    mut v___y_4652_: *mut crate::leanh::LeanObject,
    mut v___y_4653_: *mut crate::leanh::LeanObject,
    mut v___y_4654_: *mut crate::leanh::LeanObject,
    mut v___y_4655_: *mut crate::leanh::LeanObject,
    mut v___y_4656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_42968__boxed_4657_: u8 = 0;
    let mut v_res_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_42968__boxed_4657_ = (crate::leanh::lean_unbox(v___y_4650_) as u8);
    v_res_4658_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(
        v_cls_4645_,
        v_msg_4646_,
        v___y_4647_,
        v___y_4648_,
        v___y_4649_,
        v___y_42968__boxed_4657_,
        v___y_4651_,
        v___y_4652_,
        v___y_4653_,
        v___y_4654_,
        v___y_4655_,
    );
    crate::leanh::lean_dec(v___y_4655_);
    crate::leanh::lean_dec_ref(v___y_4654_);
    crate::leanh::lean_dec(v___y_4653_);
    crate::leanh::lean_dec_ref(v___y_4652_);
    crate::leanh::lean_dec(v___y_4651_);
    crate::leanh::lean_dec_ref(v___y_4649_);
    crate::leanh::lean_dec(v___y_4648_);
    crate::leanh::lean_dec(v___y_4647_);
    return v_res_4658_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(
    mut v_00_u03b2_4659_: *mut crate::leanh::LeanObject,
    mut v_a_4660_: *mut crate::leanh::LeanObject,
    mut v_x_4661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4662_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_4660_, v_x_4661_);
    return v___x_4662_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___boxed(
    mut v_00_u03b2_4663_: *mut crate::leanh::LeanObject,
    mut v_a_4664_: *mut crate::leanh::LeanObject,
    mut v_x_4665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4666_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(v_00_u03b2_4663_, v_a_4664_, v_x_4665_);
    crate::leanh::lean_dec(v_x_4665_);
    crate::leanh::lean_dec_ref(v_a_4664_);
    return v_res_4666_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(
    mut v_00_u03b2_4667_: *mut crate::leanh::LeanObject,
    mut v_a_4668_: *mut crate::leanh::LeanObject,
    mut v_x_4669_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4670_: u8 = 0;
    v___x_4670_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_4668_, v_x_4669_);
    return v___x_4670_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___boxed(
    mut v_00_u03b2_4671_: *mut crate::leanh::LeanObject,
    mut v_a_4672_: *mut crate::leanh::LeanObject,
    mut v_x_4673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4674_: u8 = 0;
    let mut v_r_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4674_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(v_00_u03b2_4671_, v_a_4672_, v_x_4673_);
    crate::leanh::lean_dec(v_x_4673_);
    crate::leanh::lean_dec_ref(v_a_4672_);
    v_r_4675_ = crate::leanh::lean_box((v_res_4674_) as usize);
    return v_r_4675_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3(
    mut v_00_u03b2_4676_: *mut crate::leanh::LeanObject,
    mut v_data_4677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4678_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(v_data_4677_);
    return v___x_4678_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4(
    mut v_00_u03b2_4679_: *mut crate::leanh::LeanObject,
    mut v_a_4680_: *mut crate::leanh::LeanObject,
    mut v_b_4681_: *mut crate::leanh::LeanObject,
    mut v_x_4682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4683_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_4680_, v_b_4681_, v_x_4682_);
    return v___x_4683_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4(
    mut v_00_u03b2_4684_: *mut crate::leanh::LeanObject,
    mut v_i_4685_: *mut crate::leanh::LeanObject,
    mut v_source_4686_: *mut crate::leanh::LeanObject,
    mut v_target_4687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4688_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(v_i_4685_, v_source_4686_, v_target_4687_);
    return v___x_4688_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9(
    mut v_00_u03b2_4689_: *mut crate::leanh::LeanObject,
    mut v_x_4690_: *mut crate::leanh::LeanObject,
    mut v_x_4691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4692_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(v_x_4690_, v_x_4691_);
    return v___x_4692_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Canonicalizer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Omega_OmegaM(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Omega_OmegaM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Canonicalizer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
}
