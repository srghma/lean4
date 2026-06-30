// Lean compiler output
// Module: Lean.Elab.Tactic.Omega.OmegaM
// Imports: Lean.Meta.AppBuilder Lean.Meta.Canonicalizer Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_infer_type, lean_int_dec_le,
    lean_int_neg, lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_shiftr, lean_nat_sub,
    lean_nat_to_int, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_string_dec_eq, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_sub,
};
use crate::r#gen::Init::Data::Int::Basic::{
    l_Int_add___boxed, l_Int_mul___boxed, l_Int_pow, l_Int_sub___boxed, l_Int_toNat,
};
use crate::r#gen::Init::Data::Int::DivMod::Basic::l_Int_ediv___boxed;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Nat_add___boxed, l_Nat_div___boxed, l_Nat_mul___boxed, l_Nat_pow___boxed,
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
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2_value:
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
    m_data: [67, 111, 101, 102, 102, 115, 0],
};
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3_value:
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
    m_data: [111, 102, 76, 105, 115, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        17910073349994400881 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        10725639862586182856 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        11430621368878064144 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0_value:
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
    m_data: [72, 65, 100, 100, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1_value:
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
    m_data: [72, 77, 117, 108, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2_value:
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
    m_data: [72, 83, 117, 98, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3_value:
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
    m_data: [72, 68, 105, 118, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4_value:
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
    m_data: [72, 80, 111, 119, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5_value:
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
    m_data: [104, 80, 111, 119, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6_value:
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
    m_fun: l_Nat_pow___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7_value:
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
    m_data: [104, 68, 105, 118, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8_value:
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
    m_fun: l_Nat_div___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9_value:
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
    m_data: [104, 83, 117, 98, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10_value:
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
    m_fun: l_Nat_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11_value:
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
    m_data: [104, 77, 117, 108, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12_value:
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
    m_fun: l_Nat_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13_value:
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
    m_data: [104, 65, 100, 100, 0],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14_value:
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
    m_fun: l_Nat_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0_value:
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
    m_fun: l_Int_ediv___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1_value:
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
    m_fun: l_Int_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2_value:
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
    m_fun: l_Int_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3_value:
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
    m_fun: l_Int_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0_value:
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
    m_data: [72, 77, 111, 100, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        8528684718952576202 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7_value:
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
    m_data: [108, 101, 95, 109, 97, 120, 95, 114, 105, 103, 104, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        4653461862122275003 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11_value)
            as *mut leanh::LeanObject,
        15037249822398505490 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14_value:
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
    m_data: [109, 105, 110, 95, 108, 101, 95, 114, 105, 103, 104, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14_value)
            as *mut leanh::LeanObject,
        970802058389122393 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17_value:
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
    m_data: [104, 77, 111, 100, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        17910073349994400881 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        488667332567600511 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18_value)
            as *mut leanh::LeanObject,
        10638584452205461697 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value:
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
    m_data: [76, 84, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value:
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
    m_data: [108, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value)
            as *mut leanh::LeanObject,
        17878876274162330439 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value)
            as *mut leanh::LeanObject,
        11833570877100518198 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25_value)
            as *mut leanh::LeanObject,
        14651840373392481165 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28_value)
            as *mut leanh::LeanObject,
        14111604343637326856 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value:
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
        111, 102, 78, 97, 116, 95, 112, 111, 115, 95, 111, 102, 95, 112, 111, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        17910073349994400881 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        488667332567600511 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value)
            as *mut leanh::LeanObject,
        13216564244333251368 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value)
            as *mut leanh::LeanObject,
        17157738005422892093 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value:
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
    m_data: [110, 101, 95, 111, 102, 95, 103, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value)
            as *mut leanh::LeanObject,
        11675868500096275836 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value:
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
        101, 109, 111, 100, 95, 108, 116, 95, 111, 102, 95, 112, 111, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value)
            as *mut leanh::LeanObject,
        15154550989551304115 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39: u8 = 0;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value)
            as *mut leanh::LeanObject,
        9626815015619986526 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value)
            as *mut leanh::LeanObject,
        17185717442815859305 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43_value)
            as *mut leanh::LeanObject,
        6362876895233142233 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value)
            as *mut leanh::LeanObject,
        9121383836933346478 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_value:
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
        112, 111, 115, 95, 112, 111, 119, 95, 111, 102, 95, 112, 111, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        17910073349994400881 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        488667332567600511 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_value)
            as *mut leanh::LeanObject,
        8404793396275648913 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value:
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
    m_data: [78, 101, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value)
            as *mut leanh::LeanObject,
        6695605208187598753 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value:
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
        109, 117, 108, 95, 101, 100, 105, 118, 95, 115, 101, 108, 102, 95, 108, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value)
            as *mut leanh::LeanObject,
        15464796390623215100 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value:
    leanh::LeanStringObject<21> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value)
            as *mut leanh::LeanObject,
        17601256755593845854 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        17910073349994400881 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        488667332567600511 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value)
            as *mut leanh::LeanObject,
        13309385938308562393 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value:
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
        110, 97, 116, 67, 97, 115, 116, 95, 110, 111, 110, 110, 101, 103, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value)
            as *mut leanh::LeanObject,
        17750334692303158606 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value:
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
    m_data: [66, 105, 116, 86, 101, 99, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value:
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
    m_data: [105, 115, 76, 116, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value)
            as *mut leanh::LeanObject,
        5394957827732845164 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value)
            as *mut leanh::LeanObject,
        8436147975023434436 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82_value)
            as *mut leanh::LeanObject,
        15815496672699636542 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value)
            as *mut leanh::LeanObject,
        4938441192065111774 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value)
            as *mut leanh::LeanObject,
        6348096724845679194 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88_value:
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
    m_data: [110, 97, 116, 65, 98, 115, 0],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89_value:
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
        111, 102, 78, 97, 116, 95, 115, 117, 98, 95, 100, 105, 99, 104, 111, 116, 111, 109, 121, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        17910073349994400881 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        488667332567600511 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89_value)
            as *mut leanh::LeanObject,
        4345411359602094212 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92_value:
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
        105, 116, 101, 95, 100, 105, 115, 106, 117, 110, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        17910073349994400881 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92_value)
            as *mut leanh::LeanObject,
        7682406714577881933 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0:
    f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__0_value)
                as *mut leanh::LeanObject,
            11366375744198450027 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__2_value)
                as *mut leanh::LeanObject,
            14231257465488249300 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__5_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__7_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(
    mut v___x_2347_: *mut leanh::LeanObject,
    mut v___x_2348_: *mut leanh::LeanObject,
    mut v_m_2349_: *mut leanh::LeanObject,
    mut v_cfg_2350_: *mut leanh::LeanObject,
    mut v___y_2351_: u8,
    mut v___y_2352_: *mut leanh::LeanObject,
    mut v___y_2353_: *mut leanh::LeanObject,
    mut v___y_2354_: *mut leanh::LeanObject,
    mut v___y_2355_: *mut leanh::LeanObject,
    mut v___y_2356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2365_: u8 = 0;
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2358_ = lean_st_mk_ref(v___x_2347_);
                v___x_2359_ = lean_st_mk_ref(v___x_2348_);
                v___x_2360_ = leanh::lean_box((v___y_2351_) as usize);
                leanh::lean_inc(v___y_2356_);
                leanh::lean_inc_ref(v___y_2355_);
                leanh::lean_inc(v___y_2354_);
                leanh::lean_inc_ref(v___y_2353_);
                leanh::lean_inc(v___y_2352_);
                leanh::lean_inc(v___x_2358_);
                leanh::lean_inc(v___x_2359_);
                v___x_2361_ = leanh::lean_apply_10(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2361_) == 0 {
                    v_a_2362_ = leanh::lean_ctor_get(v___x_2361_, 0);
                    v_isSharedCheck_2371_ = (!leanh::lean_is_exclusive(v___x_2361_)) as u8;
                    if v_isSharedCheck_2371_ == 0 {
                        v___x_2364_ = v___x_2361_;
                        v_isShared_2365_ = v_isSharedCheck_2371_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2362_);
                        leanh::lean_dec(v___x_2361_);
                        v___x_2364_ = leanh::lean_box(0);
                        v_isShared_2365_ = v_isSharedCheck_2371_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2359_);
                    leanh::lean_dec(v___x_2358_);
                    return v___x_2361_;
                }
            }
            1 => {
                v___x_2366_ = lean_st_ref_get(v___x_2359_);
                leanh::lean_dec(v___x_2359_);
                leanh::lean_dec(v___x_2366_);
                v___x_2367_ = lean_st_ref_get(v___x_2358_);
                leanh::lean_dec(v___x_2358_);
                leanh::lean_dec(v___x_2367_);
                if v_isShared_2365_ == 0 {
                    v___x_2369_ = v___x_2364_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2370_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2362_);
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
    mut v___x_2372_: *mut leanh::LeanObject,
    mut v___x_2373_: *mut leanh::LeanObject,
    mut v_m_2374_: *mut leanh::LeanObject,
    mut v_cfg_2375_: *mut leanh::LeanObject,
    mut v___y_2376_: *mut leanh::LeanObject,
    mut v___y_2377_: *mut leanh::LeanObject,
    mut v___y_2378_: *mut leanh::LeanObject,
    mut v___y_2379_: *mut leanh::LeanObject,
    mut v___y_2380_: *mut leanh::LeanObject,
    mut v___y_2381_: *mut leanh::LeanObject,
    mut v___y_2382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4823__boxed_2383_: u8 = 0;
    let mut v_res_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_4823__boxed_2383_ = (leanh::lean_unbox(v___y_2376_) as u8);
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
    leanh::lean_dec(v___y_2381_);
    leanh::lean_dec_ref(v___y_2380_);
    leanh::lean_dec(v___y_2379_);
    leanh::lean_dec_ref(v___y_2378_);
    leanh::lean_dec(v___y_2377_);
    return v_res_2384_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2385_ = leanh::lean_box(0);
    v___x_2386_ = leanh::lean_unsigned_to_nat(16);
    v___x_2387_ = lean_mk_array(v___x_2386_, v___x_2385_);
    return v___x_2387_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2388_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0_once),
        _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0,
    );
    v___x_2389_ = leanh::lean_unsigned_to_nat(0);
    v___x_2390_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2390_, 0, v___x_2389_);
    leanh::lean_ctor_set(v___x_2390_, 1, v___x_2388_);
    return v___x_2390_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2391_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once),
        _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1,
    );
    v___x_2392_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2392_, 0, v___x_2391_);
    leanh::lean_ctor_set(v___x_2392_, 1, v___x_2391_);
    return v___x_2392_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(
    mut v_m_2393_: *mut leanh::LeanObject,
    mut v_cfg_2394_: *mut leanh::LeanObject,
    mut v_a_2395_: *mut leanh::LeanObject,
    mut v_a_2396_: *mut leanh::LeanObject,
    mut v_a_2397_: *mut leanh::LeanObject,
    mut v_a_2398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: u8 = 0;
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2400_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once),
        _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1,
    );
    v___f_2401_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed as *mut core::ffi::c_void,
        11,
        4,
    );
    leanh::lean_closure_set(v___f_2401_, 0, v___x_2400_);
    leanh::lean_closure_set(v___f_2401_, 1, v___x_2400_);
    leanh::lean_closure_set(v___f_2401_, 2, v_m_2393_);
    leanh::lean_closure_set(v___f_2401_, 3, v_cfg_2394_);
    v___x_2402_ = 3;
    v___x_2403_ = leanh::lean_obj_once(
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
    mut v_m_2405_: *mut leanh::LeanObject,
    mut v_cfg_2406_: *mut leanh::LeanObject,
    mut v_a_2407_: *mut leanh::LeanObject,
    mut v_a_2408_: *mut leanh::LeanObject,
    mut v_a_2409_: *mut leanh::LeanObject,
    mut v_a_2410_: *mut leanh::LeanObject,
    mut v_a_2411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2412_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(
        v_m_2405_,
        v_cfg_2406_,
        v_a_2407_,
        v_a_2408_,
        v_a_2409_,
        v_a_2410_,
    );
    leanh::lean_dec(v_a_2410_);
    leanh::lean_dec_ref(v_a_2409_);
    leanh::lean_dec(v_a_2408_);
    leanh::lean_dec_ref(v_a_2407_);
    return v_res_2412_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run(
    mut v_00_u03b1_2413_: *mut leanh::LeanObject,
    mut v_m_2414_: *mut leanh::LeanObject,
    mut v_cfg_2415_: *mut leanh::LeanObject,
    mut v_a_2416_: *mut leanh::LeanObject,
    mut v_a_2417_: *mut leanh::LeanObject,
    mut v_a_2418_: *mut leanh::LeanObject,
    mut v_a_2419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2422_: *mut leanh::LeanObject,
    mut v_m_2423_: *mut leanh::LeanObject,
    mut v_cfg_2424_: *mut leanh::LeanObject,
    mut v_a_2425_: *mut leanh::LeanObject,
    mut v_a_2426_: *mut leanh::LeanObject,
    mut v_a_2427_: *mut leanh::LeanObject,
    mut v_a_2428_: *mut leanh::LeanObject,
    mut v_a_2429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2430_ = l_Lean_Elab_Tactic_Omega_OmegaM_run(
        v_00_u03b1_2422_,
        v_m_2423_,
        v_cfg_2424_,
        v_a_2425_,
        v_a_2426_,
        v_a_2427_,
        v_a_2428_,
    );
    leanh::lean_dec(v_a_2428_);
    leanh::lean_dec_ref(v_a_2427_);
    leanh::lean_dec(v_a_2426_);
    leanh::lean_dec_ref(v_a_2425_);
    return v_res_2430_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_cfg___redArg(
    mut v_a_2431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_2431_);
    v___x_2433_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2433_, 0, v_a_2431_);
    return v___x_2433_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_cfg___redArg___boxed(
    mut v_a_2434_: *mut leanh::LeanObject,
    mut v_a_2435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2436_ = l_Lean_Elab_Tactic_Omega_cfg___redArg(v_a_2434_);
    leanh::lean_dec_ref(v_a_2434_);
    return v_res_2436_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_cfg(
    mut v_a_2437_: *mut leanh::LeanObject,
    mut v_a_2438_: *mut leanh::LeanObject,
    mut v_a_2439_: *mut leanh::LeanObject,
    mut v_a_2440_: u8,
    mut v_a_2441_: *mut leanh::LeanObject,
    mut v_a_2442_: *mut leanh::LeanObject,
    mut v_a_2443_: *mut leanh::LeanObject,
    mut v_a_2444_: *mut leanh::LeanObject,
    mut v_a_2445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_2439_);
    v___x_2447_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2447_, 0, v_a_2439_);
    return v___x_2447_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_cfg___boxed(
    mut v_a_2448_: *mut leanh::LeanObject,
    mut v_a_2449_: *mut leanh::LeanObject,
    mut v_a_2450_: *mut leanh::LeanObject,
    mut v_a_2451_: *mut leanh::LeanObject,
    mut v_a_2452_: *mut leanh::LeanObject,
    mut v_a_2453_: *mut leanh::LeanObject,
    mut v_a_2454_: *mut leanh::LeanObject,
    mut v_a_2455_: *mut leanh::LeanObject,
    mut v_a_2456_: *mut leanh::LeanObject,
    mut v_a_2457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2458_: u8 = 0;
    let mut v_res_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2458_ = (leanh::lean_unbox(v_a_2451_) as u8);
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
    leanh::lean_dec(v_a_2456_);
    leanh::lean_dec_ref(v_a_2455_);
    leanh::lean_dec(v_a_2454_);
    leanh::lean_dec_ref(v_a_2453_);
    leanh::lean_dec(v_a_2452_);
    leanh::lean_dec_ref(v_a_2450_);
    leanh::lean_dec(v_a_2449_);
    leanh::lean_dec(v_a_2448_);
    return v_res_2459_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(
    mut v_hi_2460_: *mut leanh::LeanObject,
    mut v_pivot_2461_: *mut leanh::LeanObject,
    mut v_as_2462_: *mut leanh::LeanObject,
    mut v_i_2463_: *mut leanh::LeanObject,
    mut v_k_2464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2465_: u8 = 0;
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: u8 = 0;
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2465_ = lean_nat_dec_lt(v_k_2464_, v_hi_2460_);
                if v___x_2465_ == 0 {
                    leanh::lean_dec(v_k_2464_);
                    v___x_2466_ = lean_array_fswap(v_as_2462_, v_i_2463_, v_hi_2460_);
                    v___x_2467_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2467_, 0, v_i_2463_);
                    leanh::lean_ctor_set(v___x_2467_, 1, v___x_2466_);
                    return v___x_2467_;
                } else {
                    v___x_2468_ = lean_array_fget_borrowed(v_as_2462_, v_k_2464_);
                    v_snd_2469_ = leanh::lean_ctor_get(v___x_2468_, 1);
                    v_snd_2470_ = leanh::lean_ctor_get(v_pivot_2461_, 1);
                    v___x_2471_ = lean_nat_dec_lt(v_snd_2469_, v_snd_2470_);
                    if v___x_2471_ == 0 {
                        v___x_2472_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2473_ = lean_nat_add(v_k_2464_, v___x_2472_);
                        leanh::lean_dec(v_k_2464_);
                        v_k_2464_ = v___x_2473_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2475_ = lean_array_fswap(v_as_2462_, v_i_2463_, v_k_2464_);
                        v___x_2476_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2477_ = lean_nat_add(v_i_2463_, v___x_2476_);
                        leanh::lean_dec(v_i_2463_);
                        v___x_2478_ = lean_nat_add(v_k_2464_, v___x_2476_);
                        leanh::lean_dec(v_k_2464_);
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
    mut v_hi_2480_: *mut leanh::LeanObject,
    mut v_pivot_2481_: *mut leanh::LeanObject,
    mut v_as_2482_: *mut leanh::LeanObject,
    mut v_i_2483_: *mut leanh::LeanObject,
    mut v_k_2484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2485_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_2480_, v_pivot_2481_, v_as_2482_, v_i_2483_, v_k_2484_);
    leanh::lean_dec_ref(v_pivot_2481_);
    leanh::lean_dec(v_hi_2480_);
    return v_res_2485_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(
    mut v_x1_2486_: *mut leanh::LeanObject,
    mut v_x2_2487_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_snd_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: u8 = 0;
    v_snd_2488_ = leanh::lean_ctor_get(v_x1_2486_, 1);
    v_snd_2489_ = leanh::lean_ctor_get(v_x2_2487_, 1);
    v___x_2490_ = lean_nat_dec_lt(v_snd_2488_, v_snd_2489_);
    return v___x_2490_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed(
    mut v_x1_2491_: *mut leanh::LeanObject,
    mut v_x2_2492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2493_: u8 = 0;
    let mut v_r_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2493_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v_x1_2491_, v_x2_2492_);
    leanh::lean_dec_ref(v_x2_2492_);
    leanh::lean_dec_ref(v_x1_2491_);
    v_r_2494_ = leanh::lean_box((v_res_2493_) as usize);
    return v_r_2494_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(
    mut v_n_2495_: *mut leanh::LeanObject,
    mut v_as_2496_: *mut leanh::LeanObject,
    mut v_lo_2497_: *mut leanh::LeanObject,
    mut v_hi_2498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: u8 = 0;
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: u8 = 0;
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: u8 = 0;
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: u8 = 0;
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: u8 = 0;
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2510_ = lean_nat_dec_lt(v_lo_2497_, v_hi_2498_);
                if v___x_2510_ == 0 {
                    leanh::lean_dec(v_lo_2497_);
                    return v_as_2496_;
                } else {
                    v___x_2511_ = lean_nat_add(v_lo_2497_, v_hi_2498_);
                    v___x_2512_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_2513_ = lean_nat_shiftr(v___x_2511_, v___x_2512_);
                    leanh::lean_dec(v___x_2511_);
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
                leanh::lean_inc_n(v_lo_2497_, 2);
                v___x_2502_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_2498_, v_pivot_2501_, v___y_2500_, v_lo_2497_, v_lo_2497_);
                leanh::lean_dec(v_pivot_2501_);
                v_fst_2503_ = leanh::lean_ctor_get(v___x_2502_, 0);
                leanh::lean_inc(v_fst_2503_);
                v_snd_2504_ = leanh::lean_ctor_get(v___x_2502_, 1);
                leanh::lean_inc(v_snd_2504_);
                leanh::lean_dec_ref(v___x_2502_);
                v___x_2505_ = lean_nat_dec_le(v_hi_2498_, v_fst_2503_);
                if v___x_2505_ == 0 {
                    v___x_2506_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_2495_, v_snd_2504_, v_lo_2497_, v_fst_2503_);
                    v___x_2507_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2508_ = lean_nat_add(v_fst_2503_, v___x_2507_);
                    leanh::lean_dec(v_fst_2503_);
                    v_as_2496_ = v___x_2506_;
                    v_lo_2497_ = v___x_2508_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_2503_);
                    leanh::lean_dec(v_lo_2497_);
                    return v_snd_2504_;
                }
            }
            2 => {
                v___x_2516_ = lean_array_fget_borrowed(v___y_2515_, v_mid_2513_);
                v___x_2517_ = lean_array_fget_borrowed(v___y_2515_, v_hi_2498_);
                v___x_2518_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v___x_2516_, v___x_2517_);
                if v___x_2518_ == 0 {
                    leanh::lean_dec(v_mid_2513_);
                    v___y_2500_ = v___y_2515_;
                    state = 1;
                    continue;
                } else {
                    v___x_2519_ = lean_array_fswap(v___y_2515_, v_mid_2513_, v_hi_2498_);
                    leanh::lean_dec(v_mid_2513_);
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
    mut v_n_2530_: *mut leanh::LeanObject,
    mut v_as_2531_: *mut leanh::LeanObject,
    mut v_lo_2532_: *mut leanh::LeanObject,
    mut v_hi_2533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_2530_, v_as_2531_, v_lo_2532_, v_hi_2533_);
    leanh::lean_dec(v_hi_2533_);
    leanh::lean_dec(v_n_2530_);
    return v_res_2534_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(
    mut v_x_2535_: *mut leanh::LeanObject,
    mut v_x_2536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2536_) == 0 {
                    return v_x_2535_;
                } else {
                    v_key_2537_ = leanh::lean_ctor_get(v_x_2536_, 0);
                    v_value_2538_ = leanh::lean_ctor_get(v_x_2536_, 1);
                    v_tail_2539_ = leanh::lean_ctor_get(v_x_2536_, 2);
                    leanh::lean_inc(v_value_2538_);
                    leanh::lean_inc(v_key_2537_);
                    v___x_2540_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2540_, 0, v_key_2537_);
                    leanh::lean_ctor_set(v___x_2540_, 1, v_value_2538_);
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
    mut v_x_2543_: *mut leanh::LeanObject,
    mut v_x_2544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2545_ =
        l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(
            v_x_2543_, v_x_2544_,
        );
    leanh::lean_dec(v_x_2544_);
    return v_res_2545_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(
    mut v_as_2546_: *mut leanh::LeanObject,
    mut v_i_2547_: usize,
    mut v_stop_2548_: usize,
    mut v_b_2549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2550_: u8 = 0;
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_as_2556_: *mut leanh::LeanObject,
    mut v_i_2557_: *mut leanh::LeanObject,
    mut v_stop_2558_: *mut leanh::LeanObject,
    mut v_b_2559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2560_: usize = 0;
    let mut v_stop_boxed_2561_: usize = 0;
    let mut v_res_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2560_ = leanh::lean_unbox_usize(v_i_2557_);
    leanh::lean_dec(v_i_2557_);
    v_stop_boxed_2561_ = leanh::lean_unbox_usize(v_stop_2558_);
    leanh::lean_dec(v_stop_2558_);
    v_res_2562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_as_2556_, v_i_boxed_2560_, v_stop_boxed_2561_, v_b_2559_);
    leanh::lean_dec_ref(v_as_2556_);
    return v_res_2562_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(
    mut v_sz_2563_: usize,
    mut v_i_2564_: usize,
    mut v_bs_2565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2566_: u8 = 0;
    let mut v_v_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: usize = 0;
    let mut v___x_2572_: usize = 0;
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2566_ = lean_usize_dec_lt(v_i_2564_, v_sz_2563_);
                if v___x_2566_ == 0 {
                    return v_bs_2565_;
                } else {
                    v_v_2567_ = lean_array_uget_borrowed(v_bs_2565_, v_i_2564_);
                    v_fst_2568_ = leanh::lean_ctor_get(v_v_2567_, 0);
                    leanh::lean_inc(v_fst_2568_);
                    v___x_2569_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_2575_: *mut leanh::LeanObject,
    mut v_i_2576_: *mut leanh::LeanObject,
    mut v_bs_2577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2578_: usize = 0;
    let mut v_i_boxed_2579_: usize = 0;
    let mut v_res_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2578_ = leanh::lean_unbox_usize(v_sz_2575_);
    leanh::lean_dec(v_sz_2575_);
    v_i_boxed_2579_ = leanh::lean_unbox_usize(v_i_2576_);
    leanh::lean_dec(v_i_2576_);
    v_res_2580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(v_sz_boxed_2578_, v_i_boxed_2579_, v_bs_2577_);
    return v_res_2580_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atoms___redArg(
    mut v_a_2581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2586_: usize = 0;
    let mut v___x_2587_: usize = 0;
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: u8 = 0;
    let mut v___y_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: u8 = 0;
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: u8 = 0;
    let mut v_size_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u8 = 0;
    let mut v___x_2616_: u8 = 0;
    let mut v___x_2617_: usize = 0;
    let mut v___x_2618_: usize = 0;
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: usize = 0;
    let mut v___x_2621_: usize = 0;
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2583_ = lean_st_ref_get(v_a_2581_);
                v_size_2610_ = leanh::lean_ctor_get(v___x_2583_, 0);
                leanh::lean_inc(v_size_2610_);
                v_buckets_2611_ = leanh::lean_ctor_get(v___x_2583_, 1);
                leanh::lean_inc_ref(v_buckets_2611_);
                leanh::lean_dec(v___x_2583_);
                v___x_2612_ = lean_mk_empty_array_with_capacity(v_size_2610_);
                leanh::lean_dec(v_size_2610_);
                v___x_2613_ = leanh::lean_unsigned_to_nat(0);
                v___x_2614_ = lean_array_get_size(v_buckets_2611_);
                v___x_2615_ = lean_nat_dec_lt(v___x_2613_, v___x_2614_);
                if v___x_2615_ == 0 {
                    leanh::lean_dec_ref(v_buckets_2611_);
                    v___y_2603_ = v___x_2612_;
                    state = 4;
                    continue;
                } else {
                    v___x_2616_ = lean_nat_dec_le(v___x_2614_, v___x_2614_);
                    if v___x_2616_ == 0 {
                        if v___x_2615_ == 0 {
                            leanh::lean_dec_ref(v_buckets_2611_);
                            v___y_2603_ = v___x_2612_;
                            state = 4;
                            continue;
                        } else {
                            v___x_2617_ = 0usize;
                            v___x_2618_ = lean_usize_of_nat(v___x_2614_);
                            v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_buckets_2611_, v___x_2617_, v___x_2618_, v___x_2612_);
                            leanh::lean_dec_ref(v_buckets_2611_);
                            v___y_2603_ = v___x_2619_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_2620_ = 0usize;
                        v___x_2621_ = lean_usize_of_nat(v___x_2614_);
                        v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_buckets_2611_, v___x_2620_, v___x_2621_, v___x_2612_);
                        leanh::lean_dec_ref(v_buckets_2611_);
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
                v___x_2589_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2589_, 0, v___x_2588_);
                return v___x_2589_;
            }
            2 => {
                v___x_2595_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v___y_2593_, v___y_2591_, v___y_2592_, v___y_2594_);
                leanh::lean_dec(v___y_2594_);
                leanh::lean_dec(v___y_2593_);
                v___y_2585_ = v___x_2595_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2601_ = lean_nat_dec_le(v___y_2600_, v___y_2598_);
                if v___x_2601_ == 0 {
                    leanh::lean_dec(v___y_2598_);
                    leanh::lean_inc(v___y_2600_);
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
                v___x_2605_ = leanh::lean_unsigned_to_nat(0);
                v___x_2606_ = lean_nat_dec_eq(v___x_2604_, v___x_2605_);
                if v___x_2606_ == 0 {
                    v___x_2607_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2608_ = lean_nat_sub(v___x_2604_, v___x_2607_);
                    v___x_2609_ = lean_nat_dec_le(v___x_2605_, v___x_2608_);
                    if v___x_2609_ == 0 {
                        leanh::lean_inc(v___x_2608_);
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
    mut v_a_2623_: *mut leanh::LeanObject,
    mut v_a_2624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2625_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_2623_);
    leanh::lean_dec(v_a_2623_);
    return v_res_2625_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atoms(
    mut v_a_2626_: *mut leanh::LeanObject,
    mut v_a_2627_: *mut leanh::LeanObject,
    mut v_a_2628_: *mut leanh::LeanObject,
    mut v_a_2629_: u8,
    mut v_a_2630_: *mut leanh::LeanObject,
    mut v_a_2631_: *mut leanh::LeanObject,
    mut v_a_2632_: *mut leanh::LeanObject,
    mut v_a_2633_: *mut leanh::LeanObject,
    mut v_a_2634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2636_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_2627_);
    return v___x_2636_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atoms___boxed(
    mut v_a_2637_: *mut leanh::LeanObject,
    mut v_a_2638_: *mut leanh::LeanObject,
    mut v_a_2639_: *mut leanh::LeanObject,
    mut v_a_2640_: *mut leanh::LeanObject,
    mut v_a_2641_: *mut leanh::LeanObject,
    mut v_a_2642_: *mut leanh::LeanObject,
    mut v_a_2643_: *mut leanh::LeanObject,
    mut v_a_2644_: *mut leanh::LeanObject,
    mut v_a_2645_: *mut leanh::LeanObject,
    mut v_a_2646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2647_: u8 = 0;
    let mut v_res_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2647_ = (leanh::lean_unbox(v_a_2640_) as u8);
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
    leanh::lean_dec(v_a_2645_);
    leanh::lean_dec_ref(v_a_2644_);
    leanh::lean_dec(v_a_2643_);
    leanh::lean_dec_ref(v_a_2642_);
    leanh::lean_dec(v_a_2641_);
    leanh::lean_dec_ref(v_a_2639_);
    leanh::lean_dec(v_a_2638_);
    leanh::lean_dec(v_a_2637_);
    return v_res_2648_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(
    mut v_n_2649_: *mut leanh::LeanObject,
    mut v_as_2650_: *mut leanh::LeanObject,
    mut v_lo_2651_: *mut leanh::LeanObject,
    mut v_hi_2652_: *mut leanh::LeanObject,
    mut v_w_2653_: *mut leanh::LeanObject,
    mut v_hlo_2654_: *mut leanh::LeanObject,
    mut v_hhi_2655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2656_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_2649_, v_as_2650_, v_lo_2651_, v_hi_2652_);
    return v___x_2656_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(
    mut v_n_2657_: *mut leanh::LeanObject,
    mut v_as_2658_: *mut leanh::LeanObject,
    mut v_lo_2659_: *mut leanh::LeanObject,
    mut v_hi_2660_: *mut leanh::LeanObject,
    mut v_w_2661_: *mut leanh::LeanObject,
    mut v_hlo_2662_: *mut leanh::LeanObject,
    mut v_hhi_2663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2664_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(v_n_2657_, v_as_2658_, v_lo_2659_, v_hi_2660_, v_w_2661_, v_hlo_2662_, v_hhi_2663_);
    leanh::lean_dec(v_hi_2660_);
    leanh::lean_dec(v_n_2657_);
    return v_res_2664_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(
    mut v_n_2665_: *mut leanh::LeanObject,
    mut v_lo_2666_: *mut leanh::LeanObject,
    mut v_hi_2667_: *mut leanh::LeanObject,
    mut v_hhi_2668_: *mut leanh::LeanObject,
    mut v_pivot_2669_: *mut leanh::LeanObject,
    mut v_as_2670_: *mut leanh::LeanObject,
    mut v_i_2671_: *mut leanh::LeanObject,
    mut v_k_2672_: *mut leanh::LeanObject,
    mut v_ilo_2673_: *mut leanh::LeanObject,
    mut v_ik_2674_: *mut leanh::LeanObject,
    mut v_w_2675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2676_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_2667_, v_pivot_2669_, v_as_2670_, v_i_2671_, v_k_2672_);
    return v___x_2676_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___boxed(
    mut v_n_2677_: *mut leanh::LeanObject,
    mut v_lo_2678_: *mut leanh::LeanObject,
    mut v_hi_2679_: *mut leanh::LeanObject,
    mut v_hhi_2680_: *mut leanh::LeanObject,
    mut v_pivot_2681_: *mut leanh::LeanObject,
    mut v_as_2682_: *mut leanh::LeanObject,
    mut v_i_2683_: *mut leanh::LeanObject,
    mut v_k_2684_: *mut leanh::LeanObject,
    mut v_ilo_2685_: *mut leanh::LeanObject,
    mut v_ik_2686_: *mut leanh::LeanObject,
    mut v_w_2687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2688_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(v_n_2677_, v_lo_2678_, v_hi_2679_, v_hhi_2680_, v_pivot_2681_, v_as_2682_, v_i_2683_, v_k_2684_, v_ilo_2685_, v_ik_2686_, v_w_2687_);
    leanh::lean_dec_ref(v_pivot_2681_);
    leanh::lean_dec(v_hi_2679_);
    leanh::lean_dec(v_lo_2678_);
    leanh::lean_dec(v_n_2677_);
    return v_res_2688_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2692_ = leanh::lean_box(0);
    v___x_2693_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1;
    v___x_2694_ = l_Lean_Expr_const___override(v___x_2693_, v___x_2692_);
    return v___x_2694_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsList___redArg(
    mut v_a_2695_: *mut leanh::LeanObject,
    mut v_a_2696_: *mut leanh::LeanObject,
    mut v_a_2697_: *mut leanh::LeanObject,
    mut v_a_2698_: *mut leanh::LeanObject,
    mut v_a_2699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2701_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_2695_);
    v_a_2702_ = leanh::lean_ctor_get(v___x_2701_, 0);
    leanh::lean_inc(v_a_2702_);
    leanh::lean_dec_ref(v___x_2701_);
    v___x_2703_ = leanh::lean_obj_once(
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
    mut v_a_2706_: *mut leanh::LeanObject,
    mut v_a_2707_: *mut leanh::LeanObject,
    mut v_a_2708_: *mut leanh::LeanObject,
    mut v_a_2709_: *mut leanh::LeanObject,
    mut v_a_2710_: *mut leanh::LeanObject,
    mut v_a_2711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2712_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(
        v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_,
    );
    leanh::lean_dec(v_a_2710_);
    leanh::lean_dec_ref(v_a_2709_);
    leanh::lean_dec(v_a_2708_);
    leanh::lean_dec_ref(v_a_2707_);
    leanh::lean_dec(v_a_2706_);
    return v_res_2712_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsList(
    mut v_a_2713_: *mut leanh::LeanObject,
    mut v_a_2714_: *mut leanh::LeanObject,
    mut v_a_2715_: *mut leanh::LeanObject,
    mut v_a_2716_: u8,
    mut v_a_2717_: *mut leanh::LeanObject,
    mut v_a_2718_: *mut leanh::LeanObject,
    mut v_a_2719_: *mut leanh::LeanObject,
    mut v_a_2720_: *mut leanh::LeanObject,
    mut v_a_2721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2723_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(
        v_a_2714_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_,
    );
    return v___x_2723_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsList___boxed(
    mut v_a_2724_: *mut leanh::LeanObject,
    mut v_a_2725_: *mut leanh::LeanObject,
    mut v_a_2726_: *mut leanh::LeanObject,
    mut v_a_2727_: *mut leanh::LeanObject,
    mut v_a_2728_: *mut leanh::LeanObject,
    mut v_a_2729_: *mut leanh::LeanObject,
    mut v_a_2730_: *mut leanh::LeanObject,
    mut v_a_2731_: *mut leanh::LeanObject,
    mut v_a_2732_: *mut leanh::LeanObject,
    mut v_a_2733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2734_: u8 = 0;
    let mut v_res_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2734_ = (leanh::lean_unbox(v_a_2727_) as u8);
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
    leanh::lean_dec(v_a_2732_);
    leanh::lean_dec_ref(v_a_2731_);
    leanh::lean_dec(v_a_2730_);
    leanh::lean_dec_ref(v_a_2729_);
    leanh::lean_dec(v_a_2728_);
    leanh::lean_dec_ref(v_a_2726_);
    leanh::lean_dec(v_a_2725_);
    leanh::lean_dec(v_a_2724_);
    return v_res_2735_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2745_ = leanh::lean_box(0);
    v___x_2746_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4;
    v___x_2747_ = l_Lean_Expr_const___override(v___x_2746_, v___x_2745_);
    return v___x_2747_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(
    mut v_a_2748_: *mut leanh::LeanObject,
    mut v_a_2749_: *mut leanh::LeanObject,
    mut v_a_2750_: *mut leanh::LeanObject,
    mut v_a_2751_: *mut leanh::LeanObject,
    mut v_a_2752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2764_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2754_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(
                    v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_,
                );
                if leanh::lean_obj_tag(v___x_2754_) == 0 {
                    v_a_2755_ = leanh::lean_ctor_get(v___x_2754_, 0);
                    v_isSharedCheck_2764_ = (!leanh::lean_is_exclusive(v___x_2754_)) as u8;
                    if v_isSharedCheck_2764_ == 0 {
                        v___x_2757_ = v___x_2754_;
                        v_isShared_2758_ = v_isSharedCheck_2764_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2755_);
                        leanh::lean_dec(v___x_2754_);
                        v___x_2757_ = leanh::lean_box(0);
                        v_isShared_2758_ = v_isSharedCheck_2764_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2754_;
                }
            }
            1 => {
                v___x_2759_ = leanh::lean_obj_once(
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
                    leanh::lean_ctor_set(v___x_2757_, 0, v___x_2760_);
                    v___x_2762_ = v___x_2757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2763_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
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
    mut v_a_2765_: *mut leanh::LeanObject,
    mut v_a_2766_: *mut leanh::LeanObject,
    mut v_a_2767_: *mut leanh::LeanObject,
    mut v_a_2768_: *mut leanh::LeanObject,
    mut v_a_2769_: *mut leanh::LeanObject,
    mut v_a_2770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2771_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(
        v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_,
    );
    leanh::lean_dec(v_a_2769_);
    leanh::lean_dec_ref(v_a_2768_);
    leanh::lean_dec(v_a_2767_);
    leanh::lean_dec_ref(v_a_2766_);
    leanh::lean_dec(v_a_2765_);
    return v_res_2771_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsCoeffs(
    mut v_a_2772_: *mut leanh::LeanObject,
    mut v_a_2773_: *mut leanh::LeanObject,
    mut v_a_2774_: *mut leanh::LeanObject,
    mut v_a_2775_: u8,
    mut v_a_2776_: *mut leanh::LeanObject,
    mut v_a_2777_: *mut leanh::LeanObject,
    mut v_a_2778_: *mut leanh::LeanObject,
    mut v_a_2779_: *mut leanh::LeanObject,
    mut v_a_2780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2782_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(
        v_a_2773_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_,
    );
    return v___x_2782_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(
    mut v_a_2783_: *mut leanh::LeanObject,
    mut v_a_2784_: *mut leanh::LeanObject,
    mut v_a_2785_: *mut leanh::LeanObject,
    mut v_a_2786_: *mut leanh::LeanObject,
    mut v_a_2787_: *mut leanh::LeanObject,
    mut v_a_2788_: *mut leanh::LeanObject,
    mut v_a_2789_: *mut leanh::LeanObject,
    mut v_a_2790_: *mut leanh::LeanObject,
    mut v_a_2791_: *mut leanh::LeanObject,
    mut v_a_2792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2793_: u8 = 0;
    let mut v_res_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2793_ = (leanh::lean_unbox(v_a_2786_) as u8);
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
    leanh::lean_dec(v_a_2791_);
    leanh::lean_dec_ref(v_a_2790_);
    leanh::lean_dec(v_a_2789_);
    leanh::lean_dec_ref(v_a_2788_);
    leanh::lean_dec(v_a_2787_);
    leanh::lean_dec_ref(v_a_2785_);
    leanh::lean_dec(v_a_2784_);
    leanh::lean_dec(v_a_2783_);
    return v_res_2794_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_commitWhen___redArg(
    mut v_t_2795_: *mut leanh::LeanObject,
    mut v_a_2796_: *mut leanh::LeanObject,
    mut v_a_2797_: *mut leanh::LeanObject,
    mut v_a_2798_: *mut leanh::LeanObject,
    mut v_a_2799_: u8,
    mut v_a_2800_: *mut leanh::LeanObject,
    mut v_a_2801_: *mut leanh::LeanObject,
    mut v_a_2802_: *mut leanh::LeanObject,
    mut v_a_2803_: *mut leanh::LeanObject,
    mut v_a_2804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v_snd_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    let mut v_fst_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2828_: u8 = 0;
    let mut v_a_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2832_: u8 = 0;
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2806_ = lean_st_ref_get(v_a_2797_);
                v___x_2807_ = lean_st_ref_get(v_a_2796_);
                v___x_2808_ = leanh::lean_box((v_a_2799_) as usize);
                leanh::lean_inc(v_a_2804_);
                leanh::lean_inc_ref(v_a_2803_);
                leanh::lean_inc(v_a_2802_);
                leanh::lean_inc_ref(v_a_2801_);
                leanh::lean_inc(v_a_2800_);
                leanh::lean_inc_ref(v_a_2798_);
                leanh::lean_inc(v_a_2797_);
                leanh::lean_inc(v_a_2796_);
                v___x_2809_ = leanh::lean_apply_10(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2809_) == 0 {
                    v_a_2810_ = leanh::lean_ctor_get(v___x_2809_, 0);
                    v_isSharedCheck_2828_ = (!leanh::lean_is_exclusive(v___x_2809_)) as u8;
                    if v_isSharedCheck_2828_ == 0 {
                        v___x_2812_ = v___x_2809_;
                        v_isShared_2813_ = v_isSharedCheck_2828_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2810_);
                        leanh::lean_dec(v___x_2809_);
                        v___x_2812_ = leanh::lean_box(0);
                        v_isShared_2813_ = v_isSharedCheck_2828_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2807_);
                    leanh::lean_dec(v___x_2806_);
                    v_a_2829_ = leanh::lean_ctor_get(v___x_2809_, 0);
                    v_isSharedCheck_2836_ = (!leanh::lean_is_exclusive(v___x_2809_)) as u8;
                    if v_isSharedCheck_2836_ == 0 {
                        v___x_2831_ = v___x_2809_;
                        v_isShared_2832_ = v_isSharedCheck_2836_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2829_);
                        leanh::lean_dec(v___x_2809_);
                        v___x_2831_ = leanh::lean_box(0);
                        v_isShared_2832_ = v_isSharedCheck_2836_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2814_ = leanh::lean_ctor_get(v_a_2810_, 1);
                v___x_2815_ = (leanh::lean_unbox(v_snd_2814_) as u8);
                if v___x_2815_ == 0 {
                    v_fst_2816_ = leanh::lean_ctor_get(v_a_2810_, 0);
                    leanh::lean_inc(v_fst_2816_);
                    leanh::lean_dec(v_a_2810_);
                    v___x_2817_ = lean_st_ref_take(v_a_2797_);
                    leanh::lean_dec(v___x_2817_);
                    v___x_2818_ = lean_st_ref_set(v_a_2797_, v___x_2806_);
                    v___x_2819_ = lean_st_ref_take(v_a_2796_);
                    leanh::lean_dec(v___x_2819_);
                    v___x_2820_ = lean_st_ref_set(v_a_2796_, v___x_2807_);
                    if v_isShared_2813_ == 0 {
                        leanh::lean_ctor_set(v___x_2812_, 0, v_fst_2816_);
                        v___x_2822_ = v___x_2812_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2823_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_fst_2816_);
                        v___x_2822_ = v_reuseFailAlloc_2823_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2807_);
                    leanh::lean_dec(v___x_2806_);
                    v_fst_2824_ = leanh::lean_ctor_get(v_a_2810_, 0);
                    leanh::lean_inc(v_fst_2824_);
                    leanh::lean_dec(v_a_2810_);
                    if v_isShared_2813_ == 0 {
                        leanh::lean_ctor_set(v___x_2812_, 0, v_fst_2824_);
                        v___x_2826_ = v___x_2812_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2827_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_fst_2824_);
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
                    v_reuseFailAlloc_2835_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
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
    mut v_t_2837_: *mut leanh::LeanObject,
    mut v_a_2838_: *mut leanh::LeanObject,
    mut v_a_2839_: *mut leanh::LeanObject,
    mut v_a_2840_: *mut leanh::LeanObject,
    mut v_a_2841_: *mut leanh::LeanObject,
    mut v_a_2842_: *mut leanh::LeanObject,
    mut v_a_2843_: *mut leanh::LeanObject,
    mut v_a_2844_: *mut leanh::LeanObject,
    mut v_a_2845_: *mut leanh::LeanObject,
    mut v_a_2846_: *mut leanh::LeanObject,
    mut v_a_2847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2848_: u8 = 0;
    let mut v_res_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2848_ = (leanh::lean_unbox(v_a_2841_) as u8);
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
    leanh::lean_dec(v_a_2846_);
    leanh::lean_dec_ref(v_a_2845_);
    leanh::lean_dec(v_a_2844_);
    leanh::lean_dec_ref(v_a_2843_);
    leanh::lean_dec(v_a_2842_);
    leanh::lean_dec_ref(v_a_2840_);
    leanh::lean_dec(v_a_2839_);
    leanh::lean_dec(v_a_2838_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_commitWhen(
    mut v_00_u03b1_2850_: *mut leanh::LeanObject,
    mut v_t_2851_: *mut leanh::LeanObject,
    mut v_a_2852_: *mut leanh::LeanObject,
    mut v_a_2853_: *mut leanh::LeanObject,
    mut v_a_2854_: *mut leanh::LeanObject,
    mut v_a_2855_: u8,
    mut v_a_2856_: *mut leanh::LeanObject,
    mut v_a_2857_: *mut leanh::LeanObject,
    mut v_a_2858_: *mut leanh::LeanObject,
    mut v_a_2859_: *mut leanh::LeanObject,
    mut v_a_2860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2862_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(
        v_t_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_,
        v_a_2859_, v_a_2860_,
    );
    return v___x_2862_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_commitWhen___boxed(
    mut v_00_u03b1_2863_: *mut leanh::LeanObject,
    mut v_t_2864_: *mut leanh::LeanObject,
    mut v_a_2865_: *mut leanh::LeanObject,
    mut v_a_2866_: *mut leanh::LeanObject,
    mut v_a_2867_: *mut leanh::LeanObject,
    mut v_a_2868_: *mut leanh::LeanObject,
    mut v_a_2869_: *mut leanh::LeanObject,
    mut v_a_2870_: *mut leanh::LeanObject,
    mut v_a_2871_: *mut leanh::LeanObject,
    mut v_a_2872_: *mut leanh::LeanObject,
    mut v_a_2873_: *mut leanh::LeanObject,
    mut v_a_2874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2875_: u8 = 0;
    let mut v_res_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2875_ = (leanh::lean_unbox(v_a_2868_) as u8);
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
    leanh::lean_dec(v_a_2873_);
    leanh::lean_dec_ref(v_a_2872_);
    leanh::lean_dec(v_a_2871_);
    leanh::lean_dec_ref(v_a_2870_);
    leanh::lean_dec(v_a_2869_);
    leanh::lean_dec_ref(v_a_2867_);
    leanh::lean_dec(v_a_2866_);
    leanh::lean_dec(v_a_2865_);
    return v_res_2876_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(
    mut v_t_2877_: *mut leanh::LeanObject,
    mut v___y_2878_: *mut leanh::LeanObject,
    mut v___y_2879_: *mut leanh::LeanObject,
    mut v___y_2880_: *mut leanh::LeanObject,
    mut v___y_2881_: u8,
    mut v___y_2882_: *mut leanh::LeanObject,
    mut v___y_2883_: *mut leanh::LeanObject,
    mut v___y_2884_: *mut leanh::LeanObject,
    mut v___y_2885_: *mut leanh::LeanObject,
    mut v___y_2886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2893_: u8 = 0;
    let mut v___x_2894_: u8 = 0;
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2900_: u8 = 0;
    let mut v_a_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2904_: u8 = 0;
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2888_ = leanh::lean_box((v___y_2881_) as usize);
                leanh::lean_inc(v___y_2886_);
                leanh::lean_inc_ref(v___y_2885_);
                leanh::lean_inc(v___y_2884_);
                leanh::lean_inc_ref(v___y_2883_);
                leanh::lean_inc(v___y_2882_);
                leanh::lean_inc_ref(v___y_2880_);
                leanh::lean_inc(v___y_2879_);
                leanh::lean_inc(v___y_2878_);
                v___x_2889_ = leanh::lean_apply_10(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2889_) == 0 {
                    v_a_2890_ = leanh::lean_ctor_get(v___x_2889_, 0);
                    v_isSharedCheck_2900_ = (!leanh::lean_is_exclusive(v___x_2889_)) as u8;
                    if v_isSharedCheck_2900_ == 0 {
                        v___x_2892_ = v___x_2889_;
                        v_isShared_2893_ = v_isSharedCheck_2900_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2890_);
                        leanh::lean_dec(v___x_2889_);
                        v___x_2892_ = leanh::lean_box(0);
                        v_isShared_2893_ = v_isSharedCheck_2900_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2901_ = leanh::lean_ctor_get(v___x_2889_, 0);
                    v_isSharedCheck_2908_ = (!leanh::lean_is_exclusive(v___x_2889_)) as u8;
                    if v_isSharedCheck_2908_ == 0 {
                        v___x_2903_ = v___x_2889_;
                        v_isShared_2904_ = v_isSharedCheck_2908_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2901_);
                        leanh::lean_dec(v___x_2889_);
                        v___x_2903_ = leanh::lean_box(0);
                        v_isShared_2904_ = v_isSharedCheck_2908_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2894_ = 0;
                v___x_2895_ = leanh::lean_box((v___x_2894_) as usize);
                v___x_2896_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2896_, 0, v_a_2890_);
                leanh::lean_ctor_set(v___x_2896_, 1, v___x_2895_);
                if v_isShared_2893_ == 0 {
                    leanh::lean_ctor_set(v___x_2892_, 0, v___x_2896_);
                    v___x_2898_ = v___x_2892_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2899_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
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
                    v_reuseFailAlloc_2907_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
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
    mut v_t_2909_: *mut leanh::LeanObject,
    mut v___y_2910_: *mut leanh::LeanObject,
    mut v___y_2911_: *mut leanh::LeanObject,
    mut v___y_2912_: *mut leanh::LeanObject,
    mut v___y_2913_: *mut leanh::LeanObject,
    mut v___y_2914_: *mut leanh::LeanObject,
    mut v___y_2915_: *mut leanh::LeanObject,
    mut v___y_2916_: *mut leanh::LeanObject,
    mut v___y_2917_: *mut leanh::LeanObject,
    mut v___y_2918_: *mut leanh::LeanObject,
    mut v___y_2919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_657__boxed_2920_: u8 = 0;
    let mut v_res_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_657__boxed_2920_ = (leanh::lean_unbox(v___y_2913_) as u8);
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
    leanh::lean_dec(v___y_2918_);
    leanh::lean_dec_ref(v___y_2917_);
    leanh::lean_dec(v___y_2916_);
    leanh::lean_dec_ref(v___y_2915_);
    leanh::lean_dec(v___y_2914_);
    leanh::lean_dec_ref(v___y_2912_);
    leanh::lean_dec(v___y_2911_);
    leanh::lean_dec(v___y_2910_);
    return v_res_2921_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(
    mut v_t_2922_: *mut leanh::LeanObject,
    mut v_a_2923_: *mut leanh::LeanObject,
    mut v_a_2924_: *mut leanh::LeanObject,
    mut v_a_2925_: *mut leanh::LeanObject,
    mut v_a_2926_: u8,
    mut v_a_2927_: *mut leanh::LeanObject,
    mut v_a_2928_: *mut leanh::LeanObject,
    mut v_a_2929_: *mut leanh::LeanObject,
    mut v_a_2930_: *mut leanh::LeanObject,
    mut v_a_2931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2933_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        11,
        1,
    );
    leanh::lean_closure_set(v___f_2933_, 0, v_t_2922_);
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
    mut v_t_2935_: *mut leanh::LeanObject,
    mut v_a_2936_: *mut leanh::LeanObject,
    mut v_a_2937_: *mut leanh::LeanObject,
    mut v_a_2938_: *mut leanh::LeanObject,
    mut v_a_2939_: *mut leanh::LeanObject,
    mut v_a_2940_: *mut leanh::LeanObject,
    mut v_a_2941_: *mut leanh::LeanObject,
    mut v_a_2942_: *mut leanh::LeanObject,
    mut v_a_2943_: *mut leanh::LeanObject,
    mut v_a_2944_: *mut leanh::LeanObject,
    mut v_a_2945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2946_: u8 = 0;
    let mut v_res_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2946_ = (leanh::lean_unbox(v_a_2939_) as u8);
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
    leanh::lean_dec(v_a_2944_);
    leanh::lean_dec_ref(v_a_2943_);
    leanh::lean_dec(v_a_2942_);
    leanh::lean_dec_ref(v_a_2941_);
    leanh::lean_dec(v_a_2940_);
    leanh::lean_dec_ref(v_a_2938_);
    leanh::lean_dec(v_a_2937_);
    leanh::lean_dec(v_a_2936_);
    return v_res_2947_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState(
    mut v_00_u03b1_2948_: *mut leanh::LeanObject,
    mut v_t_2949_: *mut leanh::LeanObject,
    mut v_a_2950_: *mut leanh::LeanObject,
    mut v_a_2951_: *mut leanh::LeanObject,
    mut v_a_2952_: *mut leanh::LeanObject,
    mut v_a_2953_: u8,
    mut v_a_2954_: *mut leanh::LeanObject,
    mut v_a_2955_: *mut leanh::LeanObject,
    mut v_a_2956_: *mut leanh::LeanObject,
    mut v_a_2957_: *mut leanh::LeanObject,
    mut v_a_2958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2960_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(
        v_t_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_,
        v_a_2957_, v_a_2958_,
    );
    return v___x_2960_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState___boxed(
    mut v_00_u03b1_2961_: *mut leanh::LeanObject,
    mut v_t_2962_: *mut leanh::LeanObject,
    mut v_a_2963_: *mut leanh::LeanObject,
    mut v_a_2964_: *mut leanh::LeanObject,
    mut v_a_2965_: *mut leanh::LeanObject,
    mut v_a_2966_: *mut leanh::LeanObject,
    mut v_a_2967_: *mut leanh::LeanObject,
    mut v_a_2968_: *mut leanh::LeanObject,
    mut v_a_2969_: *mut leanh::LeanObject,
    mut v_a_2970_: *mut leanh::LeanObject,
    mut v_a_2971_: *mut leanh::LeanObject,
    mut v_a_2972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2973_: u8 = 0;
    let mut v_res_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2973_ = (leanh::lean_unbox(v_a_2966_) as u8);
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
    leanh::lean_dec(v_a_2971_);
    leanh::lean_dec_ref(v_a_2970_);
    leanh::lean_dec(v_a_2969_);
    leanh::lean_dec_ref(v_a_2968_);
    leanh::lean_dec(v_a_2967_);
    leanh::lean_dec_ref(v_a_2965_);
    leanh::lean_dec(v_a_2964_);
    leanh::lean_dec(v_a_2963_);
    return v_res_2974_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_natCast_x3f(
    mut v_n_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_n_2977_);
    v___x_2978_ = l_Lean_Expr_getAppFnArgs(v_n_2977_);
    v_fst_2979_ = leanh::lean_ctor_get(v___x_2978_, 0);
    leanh::lean_inc(v_fst_2979_);
    if leanh::lean_obj_tag(v_fst_2979_) == 1 {
        let mut v_pre_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_2980_ = leanh::lean_ctor_get(v_fst_2979_, 0);
        leanh::lean_inc(v_pre_2980_);
        if leanh::lean_obj_tag(v_pre_2980_) == 1 {
            let mut v_pre_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_2981_ = leanh::lean_ctor_get(v_pre_2980_, 0);
            if leanh::lean_obj_tag(v_pre_2981_) == 0 {
                let mut v_snd_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2986_: u8 = 0;
                v_snd_2982_ = leanh::lean_ctor_get(v___x_2978_, 1);
                leanh::lean_inc(v_snd_2982_);
                leanh::lean_dec_ref(v___x_2978_);
                v_str_2983_ = leanh::lean_ctor_get(v_fst_2979_, 1);
                leanh::lean_inc_ref(v_str_2983_);
                leanh::lean_dec_ref_known(v_fst_2979_, 2);
                v_str_2984_ = leanh::lean_ctor_get(v_pre_2980_, 1);
                leanh::lean_inc_ref(v_str_2984_);
                leanh::lean_dec_ref_known(v_pre_2980_, 2);
                v___x_2985_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
                v___x_2986_ = lean_string_dec_eq(v_str_2984_, v___x_2985_);
                leanh::lean_dec_ref(v_str_2984_);
                if v___x_2986_ == 0 {
                    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec_ref(v_str_2983_);
                    leanh::lean_dec(v_snd_2982_);
                    v___x_2987_ = l_Lean_Expr_nat_x3f(v_n_2977_);
                    return v___x_2987_;
                } else {
                    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2989_: u8 = 0;
                    v___x_2988_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                    v___x_2989_ = lean_string_dec_eq(v_str_2983_, v___x_2988_);
                    leanh::lean_dec_ref(v_str_2983_);
                    if v___x_2989_ == 0 {
                        let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec(v_snd_2982_);
                        v___x_2990_ = l_Lean_Expr_nat_x3f(v_n_2977_);
                        return v___x_2990_;
                    } else {
                        let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2993_: u8 = 0;
                        v___x_2991_ = lean_array_get_size(v_snd_2982_);
                        v___x_2992_ = leanh::lean_unsigned_to_nat(3);
                        v___x_2993_ = lean_nat_dec_eq(v___x_2991_, v___x_2992_);
                        if v___x_2993_ == 0 {
                            let mut v___x_2994_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec(v_snd_2982_);
                            v___x_2994_ = l_Lean_Expr_nat_x3f(v_n_2977_);
                            return v___x_2994_;
                        } else {
                            let mut v___x_2995_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2996_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2997_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec_ref(v_n_2977_);
                            v___x_2995_ = leanh::lean_unsigned_to_nat(2);
                            v___x_2996_ = lean_array_fget(v_snd_2982_, v___x_2995_);
                            leanh::lean_dec(v_snd_2982_);
                            v___x_2997_ = l_Lean_Expr_nat_x3f(v___x_2996_);
                            return v___x_2997_;
                        }
                    }
                }
            } else {
                let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref_known(v_pre_2980_, 2);
                leanh::lean_dec_ref_known(v_fst_2979_, 2);
                leanh::lean_dec_ref(v___x_2978_);
                v___x_2998_ = l_Lean_Expr_nat_x3f(v_n_2977_);
                return v___x_2998_;
            }
        } else {
            let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_pre_2980_);
            leanh::lean_dec_ref_known(v_fst_2979_, 2);
            leanh::lean_dec_ref(v___x_2978_);
            v___x_2999_ = l_Lean_Expr_nat_x3f(v_n_2977_);
            return v___x_2999_;
        }
    } else {
        let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_fst_2979_);
        leanh::lean_dec_ref(v___x_2978_);
        v___x_3000_ = l_Lean_Expr_nat_x3f(v_n_2977_);
        return v___x_3000_;
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Elab_Tactic_Omega_intCast_x3f_spec__0(
    mut v_a_3001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3002_ = lean_nat_to_int(v_a_3001_);
    return v___x_3002_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_intCast_x3f(
    mut v_n_3003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u8 = 0;
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: u8 = 0;
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: u8 = 0;
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3028_: u8 = 0;
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3033_: u8 = 0;
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_n_3003_);
                v___x_3004_ = l_Lean_Expr_getAppFnArgs(v_n_3003_);
                v_fst_3005_ = leanh::lean_ctor_get(v___x_3004_, 0);
                leanh::lean_inc(v_fst_3005_);
                if leanh::lean_obj_tag(v_fst_3005_) == 1 {
                    v_pre_3006_ = leanh::lean_ctor_get(v_fst_3005_, 0);
                    leanh::lean_inc(v_pre_3006_);
                    if leanh::lean_obj_tag(v_pre_3006_) == 1 {
                        v_pre_3007_ = leanh::lean_ctor_get(v_pre_3006_, 0);
                        if leanh::lean_obj_tag(v_pre_3007_) == 0 {
                            v_snd_3008_ = leanh::lean_ctor_get(v___x_3004_, 1);
                            leanh::lean_inc(v_snd_3008_);
                            leanh::lean_dec_ref(v___x_3004_);
                            v_str_3009_ = leanh::lean_ctor_get(v_fst_3005_, 1);
                            leanh::lean_inc_ref(v_str_3009_);
                            leanh::lean_dec_ref_known(v_fst_3005_, 2);
                            v_str_3010_ = leanh::lean_ctor_get(v_pre_3006_, 1);
                            leanh::lean_inc_ref(v_str_3010_);
                            leanh::lean_dec_ref_known(v_pre_3006_, 2);
                            v___x_3011_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
                            v___x_3012_ = lean_string_dec_eq(v_str_3010_, v___x_3011_);
                            leanh::lean_dec_ref(v_str_3010_);
                            if v___x_3012_ == 0 {
                                leanh::lean_dec_ref(v_str_3009_);
                                leanh::lean_dec(v_snd_3008_);
                                v___x_3013_ = l_Lean_Expr_int_x3f(v_n_3003_);
                                return v___x_3013_;
                            } else {
                                v___x_3014_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                                v___x_3015_ = lean_string_dec_eq(v_str_3009_, v___x_3014_);
                                leanh::lean_dec_ref(v_str_3009_);
                                if v___x_3015_ == 0 {
                                    leanh::lean_dec(v_snd_3008_);
                                    v___x_3016_ = l_Lean_Expr_int_x3f(v_n_3003_);
                                    return v___x_3016_;
                                } else {
                                    v___x_3017_ = lean_array_get_size(v_snd_3008_);
                                    v___x_3018_ = leanh::lean_unsigned_to_nat(3);
                                    v___x_3019_ = lean_nat_dec_eq(v___x_3017_, v___x_3018_);
                                    if v___x_3019_ == 0 {
                                        leanh::lean_dec(v_snd_3008_);
                                        v___x_3020_ = l_Lean_Expr_int_x3f(v_n_3003_);
                                        return v___x_3020_;
                                    } else {
                                        leanh::lean_dec_ref(v_n_3003_);
                                        v___x_3021_ = leanh::lean_unsigned_to_nat(2);
                                        v___x_3022_ = lean_array_fget(v_snd_3008_, v___x_3021_);
                                        leanh::lean_dec(v_snd_3008_);
                                        v___x_3023_ = l_Lean_Expr_nat_x3f(v___x_3022_);
                                        if leanh::lean_obj_tag(v___x_3023_) == 0 {
                                            v___x_3024_ = leanh::lean_box(0);
                                            return v___x_3024_;
                                        } else {
                                            v_val_3025_ =
                                                leanh::lean_ctor_get(v___x_3023_, 0);
                                            v_isSharedCheck_3033_ =
                                                (!leanh::lean_is_exclusive(v___x_3023_))
                                                    as u8;
                                            if v_isSharedCheck_3033_ == 0 {
                                                v___x_3027_ = v___x_3023_;
                                                v_isShared_3028_ = v_isSharedCheck_3033_;
                                                state = 1;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_val_3025_);
                                                leanh::lean_dec(v___x_3023_);
                                                v___x_3027_ = leanh::lean_box(0);
                                                v_isShared_3028_ = v_isSharedCheck_3033_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_pre_3006_, 2);
                            leanh::lean_dec_ref_known(v_fst_3005_, 2);
                            leanh::lean_dec_ref(v___x_3004_);
                            v___x_3034_ = l_Lean_Expr_int_x3f(v_n_3003_);
                            return v___x_3034_;
                        }
                    } else {
                        leanh::lean_dec(v_pre_3006_);
                        leanh::lean_dec_ref_known(v_fst_3005_, 2);
                        leanh::lean_dec_ref(v___x_3004_);
                        v___x_3035_ = l_Lean_Expr_int_x3f(v_n_3003_);
                        return v___x_3035_;
                    }
                } else {
                    leanh::lean_dec(v_fst_3005_);
                    leanh::lean_dec_ref(v___x_3004_);
                    v___x_3036_ = l_Lean_Expr_int_x3f(v_n_3003_);
                    return v___x_3036_;
                }
            }
            1 => {
                v___x_3029_ = lean_nat_to_int(v_val_3025_);
                if v_isShared_3028_ == 0 {
                    leanh::lean_ctor_set(v___x_3027_, 0, v___x_3029_);
                    v___x_3031_ = v___x_3027_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3032_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3029_);
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
    mut v_e_3052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: u8 = 0;
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: u8 = 0;
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: u8 = 0;
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: u8 = 0;
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: u8 = 0;
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: u8 = 0;
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: u8 = 0;
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: u8 = 0;
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: u8 = 0;
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: u8 = 0;
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: u8 = 0;
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: u8 = 0;
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: u8 = 0;
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: u8 = 0;
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: u8 = 0;
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: u8 = 0;
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_3052_);
                v___x_3053_ = l_Lean_Expr_getAppFnArgs(v_e_3052_);
                v_fst_3054_ = leanh::lean_ctor_get(v___x_3053_, 0);
                leanh::lean_inc(v_fst_3054_);
                if leanh::lean_obj_tag(v_fst_3054_) == 1 {
                    v_pre_3055_ = leanh::lean_ctor_get(v_fst_3054_, 0);
                    leanh::lean_inc(v_pre_3055_);
                    if leanh::lean_obj_tag(v_pre_3055_) == 1 {
                        v_pre_3056_ = leanh::lean_ctor_get(v_pre_3055_, 0);
                        if leanh::lean_obj_tag(v_pre_3056_) == 0 {
                            v_snd_3057_ = leanh::lean_ctor_get(v___x_3053_, 1);
                            leanh::lean_inc(v_snd_3057_);
                            leanh::lean_dec_ref(v___x_3053_);
                            v_str_3058_ = leanh::lean_ctor_get(v_fst_3054_, 1);
                            leanh::lean_inc_ref(v_str_3058_);
                            leanh::lean_dec_ref_known(v_fst_3054_, 2);
                            v_str_3059_ = leanh::lean_ctor_get(v_pre_3055_, 1);
                            leanh::lean_inc_ref(v_str_3059_);
                            leanh::lean_dec_ref_known(v_pre_3055_, 2);
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
                                                leanh::lean_dec_ref(v_str_3059_);
                                                if v___x_3071_ == 0 {
                                                    leanh::lean_dec_ref(v_str_3058_);
                                                    leanh::lean_dec(v_snd_3057_);
                                                    v___x_3072_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                    return v___x_3072_;
                                                } else {
                                                    v___x_3073_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
                                                    v___x_3074_ = lean_string_dec_eq(
                                                        v_str_3058_,
                                                        v___x_3073_,
                                                    );
                                                    leanh::lean_dec_ref(v_str_3058_);
                                                    if v___x_3074_ == 0 {
                                                        leanh::lean_dec(v_snd_3057_);
                                                        v___x_3075_ =
                                                            l_Lean_Expr_nat_x3f(v_e_3052_);
                                                        return v___x_3075_;
                                                    } else {
                                                        v___x_3076_ =
                                                            lean_array_get_size(v_snd_3057_);
                                                        v___x_3077_ =
                                                            leanh::lean_unsigned_to_nat(6);
                                                        v___x_3078_ = lean_nat_dec_eq(
                                                            v___x_3076_,
                                                            v___x_3077_,
                                                        );
                                                        if v___x_3078_ == 0 {
                                                            leanh::lean_dec(v_snd_3057_);
                                                            v___x_3079_ =
                                                                l_Lean_Expr_nat_x3f(v_e_3052_);
                                                            return v___x_3079_;
                                                        } else {
                                                            leanh::lean_dec_ref(v_e_3052_);
                                                            v___f_3080_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
                                                            v___x_3081_ =
                                                                leanh::lean_unsigned_to_nat(
                                                                    4,
                                                                );
                                                            v___x_3082_ = lean_array_fget(
                                                                v_snd_3057_,
                                                                v___x_3081_,
                                                            );
                                                            v___x_3083_ =
                                                                leanh::lean_unsigned_to_nat(
                                                                    5,
                                                                );
                                                            v___x_3084_ = lean_array_fget(
                                                                v_snd_3057_,
                                                                v___x_3083_,
                                                            );
                                                            leanh::lean_dec(v_snd_3057_);
                                                            v___x_3085_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3080_, v___x_3082_, v___x_3084_);
                                                            return v___x_3085_;
                                                        }
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v_str_3059_);
                                                v___x_3086_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
                                                v___x_3087_ =
                                                    lean_string_dec_eq(v_str_3058_, v___x_3086_);
                                                leanh::lean_dec_ref(v_str_3058_);
                                                if v___x_3087_ == 0 {
                                                    leanh::lean_dec(v_snd_3057_);
                                                    v___x_3088_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                    return v___x_3088_;
                                                } else {
                                                    v___x_3089_ = lean_array_get_size(v_snd_3057_);
                                                    v___x_3090_ =
                                                        leanh::lean_unsigned_to_nat(6);
                                                    v___x_3091_ =
                                                        lean_nat_dec_eq(v___x_3089_, v___x_3090_);
                                                    if v___x_3091_ == 0 {
                                                        leanh::lean_dec(v_snd_3057_);
                                                        v___x_3092_ =
                                                            l_Lean_Expr_nat_x3f(v_e_3052_);
                                                        return v___x_3092_;
                                                    } else {
                                                        leanh::lean_dec_ref(v_e_3052_);
                                                        v___f_3093_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
                                                        v___x_3094_ =
                                                            leanh::lean_unsigned_to_nat(4);
                                                        v___x_3095_ = lean_array_fget(
                                                            v_snd_3057_,
                                                            v___x_3094_,
                                                        );
                                                        v___x_3096_ =
                                                            leanh::lean_unsigned_to_nat(5);
                                                        v___x_3097_ = lean_array_fget(
                                                            v_snd_3057_,
                                                            v___x_3096_,
                                                        );
                                                        leanh::lean_dec(v_snd_3057_);
                                                        v___x_3098_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3093_, v___x_3095_, v___x_3097_);
                                                        return v___x_3098_;
                                                    }
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v_str_3059_);
                                            v___x_3099_ =
                                                l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
                                            v___x_3100_ =
                                                lean_string_dec_eq(v_str_3058_, v___x_3099_);
                                            leanh::lean_dec_ref(v_str_3058_);
                                            if v___x_3100_ == 0 {
                                                leanh::lean_dec(v_snd_3057_);
                                                v___x_3101_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                return v___x_3101_;
                                            } else {
                                                v___x_3102_ = lean_array_get_size(v_snd_3057_);
                                                v___x_3103_ = leanh::lean_unsigned_to_nat(6);
                                                v___x_3104_ =
                                                    lean_nat_dec_eq(v___x_3102_, v___x_3103_);
                                                if v___x_3104_ == 0 {
                                                    leanh::lean_dec(v_snd_3057_);
                                                    v___x_3105_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                    return v___x_3105_;
                                                } else {
                                                    leanh::lean_dec_ref(v_e_3052_);
                                                    v___f_3106_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10;
                                                    v___x_3107_ =
                                                        leanh::lean_unsigned_to_nat(4);
                                                    v___x_3108_ =
                                                        lean_array_fget(v_snd_3057_, v___x_3107_);
                                                    v___x_3109_ =
                                                        leanh::lean_unsigned_to_nat(5);
                                                    v___x_3110_ =
                                                        lean_array_fget(v_snd_3057_, v___x_3109_);
                                                    leanh::lean_dec(v_snd_3057_);
                                                    v___x_3111_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3106_, v___x_3108_, v___x_3110_);
                                                    return v___x_3111_;
                                                }
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_str_3059_);
                                        v___x_3112_ =
                                            l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11;
                                        v___x_3113_ = lean_string_dec_eq(v_str_3058_, v___x_3112_);
                                        leanh::lean_dec_ref(v_str_3058_);
                                        if v___x_3113_ == 0 {
                                            leanh::lean_dec(v_snd_3057_);
                                            v___x_3114_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                            return v___x_3114_;
                                        } else {
                                            v___x_3115_ = lean_array_get_size(v_snd_3057_);
                                            v___x_3116_ = leanh::lean_unsigned_to_nat(6);
                                            v___x_3117_ = lean_nat_dec_eq(v___x_3115_, v___x_3116_);
                                            if v___x_3117_ == 0 {
                                                leanh::lean_dec(v_snd_3057_);
                                                v___x_3118_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                return v___x_3118_;
                                            } else {
                                                leanh::lean_dec_ref(v_e_3052_);
                                                v___f_3119_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12;
                                                v___x_3120_ = leanh::lean_unsigned_to_nat(4);
                                                v___x_3121_ =
                                                    lean_array_fget(v_snd_3057_, v___x_3120_);
                                                v___x_3122_ = leanh::lean_unsigned_to_nat(5);
                                                v___x_3123_ =
                                                    lean_array_fget(v_snd_3057_, v___x_3122_);
                                                leanh::lean_dec(v_snd_3057_);
                                                v___x_3124_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3119_, v___x_3121_, v___x_3123_);
                                                return v___x_3124_;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_str_3059_);
                                    v___x_3125_ =
                                        l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13;
                                    v___x_3126_ = lean_string_dec_eq(v_str_3058_, v___x_3125_);
                                    leanh::lean_dec_ref(v_str_3058_);
                                    if v___x_3126_ == 0 {
                                        leanh::lean_dec(v_snd_3057_);
                                        v___x_3127_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                        return v___x_3127_;
                                    } else {
                                        v___x_3128_ = lean_array_get_size(v_snd_3057_);
                                        v___x_3129_ = leanh::lean_unsigned_to_nat(6);
                                        v___x_3130_ = lean_nat_dec_eq(v___x_3128_, v___x_3129_);
                                        if v___x_3130_ == 0 {
                                            leanh::lean_dec(v_snd_3057_);
                                            v___x_3131_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                            return v___x_3131_;
                                        } else {
                                            leanh::lean_dec_ref(v_e_3052_);
                                            v___f_3132_ =
                                                l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14;
                                            v___x_3133_ = leanh::lean_unsigned_to_nat(4);
                                            v___x_3134_ = lean_array_fget(v_snd_3057_, v___x_3133_);
                                            v___x_3135_ = leanh::lean_unsigned_to_nat(5);
                                            v___x_3136_ = lean_array_fget(v_snd_3057_, v___x_3135_);
                                            leanh::lean_dec(v_snd_3057_);
                                            v___x_3137_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3132_, v___x_3134_, v___x_3136_);
                                            return v___x_3137_;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_str_3059_);
                                v___x_3138_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                                v___x_3139_ = lean_string_dec_eq(v_str_3058_, v___x_3138_);
                                leanh::lean_dec_ref(v_str_3058_);
                                if v___x_3139_ == 0 {
                                    leanh::lean_dec(v_snd_3057_);
                                    v___x_3140_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                    return v___x_3140_;
                                } else {
                                    v___x_3141_ = lean_array_get_size(v_snd_3057_);
                                    v___x_3142_ = leanh::lean_unsigned_to_nat(3);
                                    v___x_3143_ = lean_nat_dec_eq(v___x_3141_, v___x_3142_);
                                    if v___x_3143_ == 0 {
                                        leanh::lean_dec(v_snd_3057_);
                                        v___x_3144_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                        return v___x_3144_;
                                    } else {
                                        leanh::lean_dec_ref(v_e_3052_);
                                        v___x_3145_ = leanh::lean_unsigned_to_nat(2);
                                        v___x_3146_ = lean_array_fget(v_snd_3057_, v___x_3145_);
                                        leanh::lean_dec(v_snd_3057_);
                                        v_e_3052_ = v___x_3146_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_pre_3055_, 2);
                            leanh::lean_dec_ref_known(v_fst_3054_, 2);
                            leanh::lean_dec_ref(v___x_3053_);
                            v___x_3148_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                            return v___x_3148_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_fst_3054_, 2);
                        leanh::lean_dec(v_pre_3055_);
                        leanh::lean_dec_ref(v___x_3053_);
                        v___x_3149_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                        return v___x_3149_;
                    }
                } else {
                    leanh::lean_dec(v_fst_3054_);
                    leanh::lean_dec_ref(v___x_3053_);
                    v___x_3150_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                    return v___x_3150_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(
    mut v_f_3151_: *mut leanh::LeanObject,
    mut v_x_3152_: *mut leanh::LeanObject,
    mut v_y_3153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3160_: u8 = 0;
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3165_: u8 = 0;
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3154_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v_x_3152_);
                if leanh::lean_obj_tag(v___x_3154_) == 1 {
                    v_val_3155_ = leanh::lean_ctor_get(v___x_3154_, 0);
                    leanh::lean_inc(v_val_3155_);
                    leanh::lean_dec_ref_known(v___x_3154_, 1);
                    v___x_3156_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v_y_3153_);
                    if leanh::lean_obj_tag(v___x_3156_) == 1 {
                        v_val_3157_ = leanh::lean_ctor_get(v___x_3156_, 0);
                        v_isSharedCheck_3165_ =
                            (!leanh::lean_is_exclusive(v___x_3156_)) as u8;
                        if v_isSharedCheck_3165_ == 0 {
                            v___x_3159_ = v___x_3156_;
                            v_isShared_3160_ = v_isSharedCheck_3165_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3157_);
                            leanh::lean_dec(v___x_3156_);
                            v___x_3159_ = leanh::lean_box(0);
                            v_isShared_3160_ = v_isSharedCheck_3165_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3156_);
                        leanh::lean_dec(v_val_3155_);
                        leanh::lean_dec_ref(v_f_3151_);
                        v___x_3166_ = leanh::lean_box(0);
                        return v___x_3166_;
                    }
                } else {
                    leanh::lean_dec(v___x_3154_);
                    leanh::lean_dec_ref(v_y_3153_);
                    leanh::lean_dec_ref(v_f_3151_);
                    v___x_3167_ = leanh::lean_box(0);
                    return v___x_3167_;
                }
            }
            1 => {
                v___x_3161_ = leanh::lean_apply_2(v_f_3151_, v_val_3155_, v_val_3157_);
                if v_isShared_3160_ == 0 {
                    leanh::lean_ctor_set(v___x_3159_, 0, v___x_3161_);
                    v___x_3163_ = v___x_3159_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3164_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3161_);
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
    mut v_e_3172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: u8 = 0;
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: u8 = 0;
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: u8 = 0;
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: u8 = 0;
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: u8 = 0;
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: u8 = 0;
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: u8 = 0;
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: u8 = 0;
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3210_: u8 = 0;
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3215_: u8 = 0;
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: u8 = 0;
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: u8 = 0;
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: u8 = 0;
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: u8 = 0;
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: u8 = 0;
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: u8 = 0;
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: u8 = 0;
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3284_: u8 = 0;
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3289_: u8 = 0;
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_3172_);
                v___x_3173_ = l_Lean_Expr_getAppFnArgs(v_e_3172_);
                v_fst_3174_ = leanh::lean_ctor_get(v___x_3173_, 0);
                leanh::lean_inc(v_fst_3174_);
                if leanh::lean_obj_tag(v_fst_3174_) == 1 {
                    v_pre_3175_ = leanh::lean_ctor_get(v_fst_3174_, 0);
                    leanh::lean_inc(v_pre_3175_);
                    if leanh::lean_obj_tag(v_pre_3175_) == 1 {
                        v_pre_3176_ = leanh::lean_ctor_get(v_pre_3175_, 0);
                        if leanh::lean_obj_tag(v_pre_3176_) == 0 {
                            v_snd_3177_ = leanh::lean_ctor_get(v___x_3173_, 1);
                            leanh::lean_inc(v_snd_3177_);
                            leanh::lean_dec_ref(v___x_3173_);
                            v_str_3178_ = leanh::lean_ctor_get(v_fst_3174_, 1);
                            leanh::lean_inc_ref(v_str_3178_);
                            leanh::lean_dec_ref_known(v_fst_3174_, 2);
                            v_str_3179_ = leanh::lean_ctor_get(v_pre_3175_, 1);
                            leanh::lean_inc_ref(v_str_3179_);
                            leanh::lean_dec_ref_known(v_pre_3175_, 2);
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
                                                leanh::lean_dec_ref(v_str_3179_);
                                                if v___x_3191_ == 0 {
                                                    leanh::lean_dec_ref(v_str_3178_);
                                                    leanh::lean_dec(v_snd_3177_);
                                                    v___x_3192_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                    return v___x_3192_;
                                                } else {
                                                    v___x_3193_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
                                                    v___x_3194_ = lean_string_dec_eq(
                                                        v_str_3178_,
                                                        v___x_3193_,
                                                    );
                                                    leanh::lean_dec_ref(v_str_3178_);
                                                    if v___x_3194_ == 0 {
                                                        leanh::lean_dec(v_snd_3177_);
                                                        v___x_3195_ =
                                                            l_Lean_Expr_int_x3f(v_e_3172_);
                                                        return v___x_3195_;
                                                    } else {
                                                        v___x_3196_ =
                                                            lean_array_get_size(v_snd_3177_);
                                                        v___x_3197_ =
                                                            leanh::lean_unsigned_to_nat(6);
                                                        v___x_3198_ = lean_nat_dec_eq(
                                                            v___x_3196_,
                                                            v___x_3197_,
                                                        );
                                                        if v___x_3198_ == 0 {
                                                            leanh::lean_dec(v_snd_3177_);
                                                            v___x_3199_ =
                                                                l_Lean_Expr_int_x3f(v_e_3172_);
                                                            return v___x_3199_;
                                                        } else {
                                                            leanh::lean_dec_ref(v_e_3172_);
                                                            v___x_3200_ =
                                                                leanh::lean_unsigned_to_nat(
                                                                    4,
                                                                );
                                                            v___x_3201_ = lean_array_fget_borrowed(
                                                                v_snd_3177_,
                                                                v___x_3200_,
                                                            );
                                                            leanh::lean_inc(v___x_3201_);
                                                            v___x_3202_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v___x_3201_);
                                                            if leanh::lean_obj_tag(
                                                                v___x_3202_,
                                                            ) == 1
                                                            {
                                                                v_val_3203_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_3202_,
                                                                        0,
                                                                    );
                                                                leanh::lean_inc(v_val_3203_);
                                                                leanh::lean_dec_ref_known(
                                                                    v___x_3202_,
                                                                    1,
                                                                );
                                                                v___x_3204_ = leanh::lean_unsigned_to_nat(5);
                                                                v___x_3205_ = lean_array_fget(
                                                                    v_snd_3177_,
                                                                    v___x_3204_,
                                                                );
                                                                leanh::lean_dec(v_snd_3177_);
                                                                v___x_3206_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v___x_3205_);
                                                                if leanh::lean_obj_tag(
                                                                    v___x_3206_,
                                                                ) == 1
                                                                {
                                                                    v_val_3207_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_3206_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_3215_ = (!leanh::lean_is_exclusive(v___x_3206_)) as u8;
                                                                    if v_isSharedCheck_3215_ == 0 {
                                                                        v___x_3209_ = v___x_3206_;
                                                                        v_isShared_3210_ =
                                                                            v_isSharedCheck_3215_;
                                                                        state = 1;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_val_3207_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_3206_,
                                                                        );
                                                                        v___x_3209_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_3210_ =
                                                                            v_isSharedCheck_3215_;
                                                                        state = 1;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec(
                                                                        v___x_3206_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_val_3203_,
                                                                    );
                                                                    v___x_3216_ =
                                                                        leanh::lean_box(0);
                                                                    return v___x_3216_;
                                                                }
                                                            } else {
                                                                leanh::lean_dec(v___x_3202_);
                                                                leanh::lean_dec(v_snd_3177_);
                                                                v___x_3217_ =
                                                                    leanh::lean_box(0);
                                                                return v___x_3217_;
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v_str_3179_);
                                                v___x_3218_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
                                                v___x_3219_ =
                                                    lean_string_dec_eq(v_str_3178_, v___x_3218_);
                                                leanh::lean_dec_ref(v_str_3178_);
                                                if v___x_3219_ == 0 {
                                                    leanh::lean_dec(v_snd_3177_);
                                                    v___x_3220_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                    return v___x_3220_;
                                                } else {
                                                    v___x_3221_ = lean_array_get_size(v_snd_3177_);
                                                    v___x_3222_ =
                                                        leanh::lean_unsigned_to_nat(6);
                                                    v___x_3223_ =
                                                        lean_nat_dec_eq(v___x_3221_, v___x_3222_);
                                                    if v___x_3223_ == 0 {
                                                        leanh::lean_dec(v_snd_3177_);
                                                        v___x_3224_ =
                                                            l_Lean_Expr_int_x3f(v_e_3172_);
                                                        return v___x_3224_;
                                                    } else {
                                                        leanh::lean_dec_ref(v_e_3172_);
                                                        v___f_3225_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0;
                                                        v___x_3226_ =
                                                            leanh::lean_unsigned_to_nat(4);
                                                        v___x_3227_ = lean_array_fget(
                                                            v_snd_3177_,
                                                            v___x_3226_,
                                                        );
                                                        v___x_3228_ =
                                                            leanh::lean_unsigned_to_nat(5);
                                                        v___x_3229_ = lean_array_fget(
                                                            v_snd_3177_,
                                                            v___x_3228_,
                                                        );
                                                        leanh::lean_dec(v_snd_3177_);
                                                        v___x_3230_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_3225_, v___x_3227_, v___x_3229_);
                                                        return v___x_3230_;
                                                    }
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v_str_3179_);
                                            v___x_3231_ =
                                                l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
                                            v___x_3232_ =
                                                lean_string_dec_eq(v_str_3178_, v___x_3231_);
                                            leanh::lean_dec_ref(v_str_3178_);
                                            if v___x_3232_ == 0 {
                                                leanh::lean_dec(v_snd_3177_);
                                                v___x_3233_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                return v___x_3233_;
                                            } else {
                                                v___x_3234_ = lean_array_get_size(v_snd_3177_);
                                                v___x_3235_ = leanh::lean_unsigned_to_nat(6);
                                                v___x_3236_ =
                                                    lean_nat_dec_eq(v___x_3234_, v___x_3235_);
                                                if v___x_3236_ == 0 {
                                                    leanh::lean_dec(v_snd_3177_);
                                                    v___x_3237_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                    return v___x_3237_;
                                                } else {
                                                    leanh::lean_dec_ref(v_e_3172_);
                                                    v___f_3238_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1;
                                                    v___x_3239_ =
                                                        leanh::lean_unsigned_to_nat(4);
                                                    v___x_3240_ =
                                                        lean_array_fget(v_snd_3177_, v___x_3239_);
                                                    v___x_3241_ =
                                                        leanh::lean_unsigned_to_nat(5);
                                                    v___x_3242_ =
                                                        lean_array_fget(v_snd_3177_, v___x_3241_);
                                                    leanh::lean_dec(v_snd_3177_);
                                                    v___x_3243_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_3238_, v___x_3240_, v___x_3242_);
                                                    return v___x_3243_;
                                                }
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_str_3179_);
                                        v___x_3244_ =
                                            l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11;
                                        v___x_3245_ = lean_string_dec_eq(v_str_3178_, v___x_3244_);
                                        leanh::lean_dec_ref(v_str_3178_);
                                        if v___x_3245_ == 0 {
                                            leanh::lean_dec(v_snd_3177_);
                                            v___x_3246_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                            return v___x_3246_;
                                        } else {
                                            v___x_3247_ = lean_array_get_size(v_snd_3177_);
                                            v___x_3248_ = leanh::lean_unsigned_to_nat(6);
                                            v___x_3249_ = lean_nat_dec_eq(v___x_3247_, v___x_3248_);
                                            if v___x_3249_ == 0 {
                                                leanh::lean_dec(v_snd_3177_);
                                                v___x_3250_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                return v___x_3250_;
                                            } else {
                                                leanh::lean_dec_ref(v_e_3172_);
                                                v___f_3251_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2;
                                                v___x_3252_ = leanh::lean_unsigned_to_nat(4);
                                                v___x_3253_ =
                                                    lean_array_fget(v_snd_3177_, v___x_3252_);
                                                v___x_3254_ = leanh::lean_unsigned_to_nat(5);
                                                v___x_3255_ =
                                                    lean_array_fget(v_snd_3177_, v___x_3254_);
                                                leanh::lean_dec(v_snd_3177_);
                                                v___x_3256_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_3251_, v___x_3253_, v___x_3255_);
                                                return v___x_3256_;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_str_3179_);
                                    v___x_3257_ =
                                        l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13;
                                    v___x_3258_ = lean_string_dec_eq(v_str_3178_, v___x_3257_);
                                    leanh::lean_dec_ref(v_str_3178_);
                                    if v___x_3258_ == 0 {
                                        leanh::lean_dec(v_snd_3177_);
                                        v___x_3259_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                        return v___x_3259_;
                                    } else {
                                        v___x_3260_ = lean_array_get_size(v_snd_3177_);
                                        v___x_3261_ = leanh::lean_unsigned_to_nat(6);
                                        v___x_3262_ = lean_nat_dec_eq(v___x_3260_, v___x_3261_);
                                        if v___x_3262_ == 0 {
                                            leanh::lean_dec(v_snd_3177_);
                                            v___x_3263_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                            return v___x_3263_;
                                        } else {
                                            leanh::lean_dec_ref(v_e_3172_);
                                            v___f_3264_ =
                                                l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3;
                                            v___x_3265_ = leanh::lean_unsigned_to_nat(4);
                                            v___x_3266_ = lean_array_fget(v_snd_3177_, v___x_3265_);
                                            v___x_3267_ = leanh::lean_unsigned_to_nat(5);
                                            v___x_3268_ = lean_array_fget(v_snd_3177_, v___x_3267_);
                                            leanh::lean_dec(v_snd_3177_);
                                            v___x_3269_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_3264_, v___x_3266_, v___x_3268_);
                                            return v___x_3269_;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_str_3179_);
                                v___x_3270_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                                v___x_3271_ = lean_string_dec_eq(v_str_3178_, v___x_3270_);
                                leanh::lean_dec_ref(v_str_3178_);
                                if v___x_3271_ == 0 {
                                    leanh::lean_dec(v_snd_3177_);
                                    v___x_3272_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                    return v___x_3272_;
                                } else {
                                    v___x_3273_ = lean_array_get_size(v_snd_3177_);
                                    v___x_3274_ = leanh::lean_unsigned_to_nat(3);
                                    v___x_3275_ = lean_nat_dec_eq(v___x_3273_, v___x_3274_);
                                    if v___x_3275_ == 0 {
                                        leanh::lean_dec(v_snd_3177_);
                                        v___x_3276_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                        return v___x_3276_;
                                    } else {
                                        leanh::lean_dec_ref(v_e_3172_);
                                        v___x_3277_ = leanh::lean_unsigned_to_nat(2);
                                        v___x_3278_ = lean_array_fget(v_snd_3177_, v___x_3277_);
                                        leanh::lean_dec(v_snd_3177_);
                                        v___x_3279_ =
                                            l_Lean_Elab_Tactic_Omega_groundNat_x3f(v___x_3278_);
                                        if leanh::lean_obj_tag(v___x_3279_) == 0 {
                                            v___x_3280_ = leanh::lean_box(0);
                                            return v___x_3280_;
                                        } else {
                                            v_val_3281_ =
                                                leanh::lean_ctor_get(v___x_3279_, 0);
                                            v_isSharedCheck_3289_ =
                                                (!leanh::lean_is_exclusive(v___x_3279_))
                                                    as u8;
                                            if v_isSharedCheck_3289_ == 0 {
                                                v___x_3283_ = v___x_3279_;
                                                v_isShared_3284_ = v_isSharedCheck_3289_;
                                                state = 3;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_val_3281_);
                                                leanh::lean_dec(v___x_3279_);
                                                v___x_3283_ = leanh::lean_box(0);
                                                v_isShared_3284_ = v_isSharedCheck_3289_;
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_pre_3175_, 2);
                            leanh::lean_dec_ref_known(v_fst_3174_, 2);
                            leanh::lean_dec_ref(v___x_3173_);
                            v___x_3290_ = l_Lean_Expr_int_x3f(v_e_3172_);
                            return v___x_3290_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_fst_3174_, 2);
                        leanh::lean_dec(v_pre_3175_);
                        leanh::lean_dec_ref(v___x_3173_);
                        v___x_3291_ = l_Lean_Expr_int_x3f(v_e_3172_);
                        return v___x_3291_;
                    }
                } else {
                    leanh::lean_dec(v_fst_3174_);
                    leanh::lean_dec_ref(v___x_3173_);
                    v___x_3292_ = l_Lean_Expr_int_x3f(v_e_3172_);
                    return v___x_3292_;
                }
            }
            1 => {
                v___x_3211_ = l_Int_pow(v_val_3203_, v_val_3207_);
                leanh::lean_dec(v_val_3207_);
                leanh::lean_dec(v_val_3203_);
                if v_isShared_3210_ == 0 {
                    leanh::lean_ctor_set(v___x_3209_, 0, v___x_3211_);
                    v___x_3213_ = v___x_3209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3214_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
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
                    leanh::lean_ctor_set(v___x_3283_, 0, v___x_3285_);
                    v___x_3287_ = v___x_3283_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3288_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3285_);
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
    mut v_f_3293_: *mut leanh::LeanObject,
    mut v_x_3294_: *mut leanh::LeanObject,
    mut v_y_3295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3302_: u8 = 0;
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3307_: u8 = 0;
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3296_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v_x_3294_);
                if leanh::lean_obj_tag(v___x_3296_) == 1 {
                    v_val_3297_ = leanh::lean_ctor_get(v___x_3296_, 0);
                    leanh::lean_inc(v_val_3297_);
                    leanh::lean_dec_ref_known(v___x_3296_, 1);
                    v___x_3298_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v_y_3295_);
                    if leanh::lean_obj_tag(v___x_3298_) == 1 {
                        v_val_3299_ = leanh::lean_ctor_get(v___x_3298_, 0);
                        v_isSharedCheck_3307_ =
                            (!leanh::lean_is_exclusive(v___x_3298_)) as u8;
                        if v_isSharedCheck_3307_ == 0 {
                            v___x_3301_ = v___x_3298_;
                            v_isShared_3302_ = v_isSharedCheck_3307_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3299_);
                            leanh::lean_dec(v___x_3298_);
                            v___x_3301_ = leanh::lean_box(0);
                            v_isShared_3302_ = v_isSharedCheck_3307_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3298_);
                        leanh::lean_dec(v_val_3297_);
                        leanh::lean_dec_ref(v_f_3293_);
                        v___x_3308_ = leanh::lean_box(0);
                        return v___x_3308_;
                    }
                } else {
                    leanh::lean_dec(v___x_3296_);
                    leanh::lean_dec_ref(v_y_3295_);
                    leanh::lean_dec_ref(v_f_3293_);
                    v___x_3309_ = leanh::lean_box(0);
                    return v___x_3309_;
                }
            }
            1 => {
                v___x_3303_ = leanh::lean_apply_2(v_f_3293_, v_val_3297_, v_val_3299_);
                if v_isShared_3302_ == 0 {
                    leanh::lean_ctor_set(v___x_3301_, 0, v___x_3303_);
                    v___x_3305_ = v___x_3301_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3306_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
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
    mut v_a_3310_: *mut leanh::LeanObject,
    mut v_b_3311_: *mut leanh::LeanObject,
    mut v_a_3312_: *mut leanh::LeanObject,
    mut v_a_3313_: *mut leanh::LeanObject,
    mut v_a_3314_: *mut leanh::LeanObject,
    mut v_a_3315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3323_: u8 = 0;
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_a_3310_);
                v___x_3317_ =
                    l_Lean_Meta_mkEqRefl(v_a_3310_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
                if leanh::lean_obj_tag(v___x_3317_) == 0 {
                    v_a_3318_ = leanh::lean_ctor_get(v___x_3317_, 0);
                    leanh::lean_inc(v_a_3318_);
                    leanh::lean_dec_ref_known(v___x_3317_, 1);
                    v___x_3319_ = l_Lean_Meta_mkEq(
                        v_a_3310_, v_b_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_,
                    );
                    if leanh::lean_obj_tag(v___x_3319_) == 0 {
                        v_a_3320_ = leanh::lean_ctor_get(v___x_3319_, 0);
                        v_isSharedCheck_3328_ =
                            (!leanh::lean_is_exclusive(v___x_3319_)) as u8;
                        if v_isSharedCheck_3328_ == 0 {
                            v___x_3322_ = v___x_3319_;
                            v_isShared_3323_ = v_isSharedCheck_3328_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3320_);
                            leanh::lean_dec(v___x_3319_);
                            v___x_3322_ = leanh::lean_box(0);
                            v_isShared_3323_ = v_isSharedCheck_3328_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3318_);
                        return v___x_3319_;
                    }
                } else {
                    leanh::lean_dec_ref(v_b_3311_);
                    leanh::lean_dec_ref(v_a_3310_);
                    return v___x_3317_;
                }
            }
            1 => {
                v___x_3324_ = l_Lean_Meta_mkExpectedPropHint(v_a_3318_, v_a_3320_);
                if v_isShared_3323_ == 0 {
                    leanh::lean_ctor_set(v___x_3322_, 0, v___x_3324_);
                    v___x_3326_ = v___x_3322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3327_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
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
    mut v_a_3329_: *mut leanh::LeanObject,
    mut v_b_3330_: *mut leanh::LeanObject,
    mut v_a_3331_: *mut leanh::LeanObject,
    mut v_a_3332_: *mut leanh::LeanObject,
    mut v_a_3333_: *mut leanh::LeanObject,
    mut v_a_3334_: *mut leanh::LeanObject,
    mut v_a_3335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(
        v_a_3329_, v_b_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_,
    );
    leanh::lean_dec(v_a_3334_);
    leanh::lean_dec_ref(v_a_3333_);
    leanh::lean_dec(v_a_3332_);
    leanh::lean_dec_ref(v_a_3331_);
    return v_res_3336_;
}
pub unsafe fn l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(
    mut v_a_3337_: *mut leanh::LeanObject,
    mut v_x_3338_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3339_: u8 = 0;
    let mut v_head_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3338_) == 0 {
                    v___x_3339_ = 0;
                    return v___x_3339_;
                } else {
                    v_head_3340_ = leanh::lean_ctor_get(v_x_3338_, 0);
                    v_tail_3341_ = leanh::lean_ctor_get(v_x_3338_, 1);
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
    mut v_a_3344_: *mut leanh::LeanObject,
    mut v_x_3345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3346_: u8 = 0;
    let mut v_r_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3346_ =
        l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v_a_3344_, v_x_3345_);
    leanh::lean_dec(v_x_3345_);
    leanh::lean_dec_ref(v_a_3344_);
    v_r_3347_ = leanh::lean_box((v_res_3346_) as usize);
    return v_r_3347_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3356_ = leanh::lean_box(0);
    v___x_3357_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5;
    v___x_3358_ = l_Lean_Expr_const___override(v___x_3357_, v___x_3356_);
    return v___x_3358_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3363_ = leanh::lean_box(0);
    v___x_3364_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
    v___x_3365_ = l_Lean_Expr_const___override(v___x_3364_, v___x_3363_);
    return v___x_3365_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3371_ = leanh::lean_box(0);
    v___x_3372_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12;
    v___x_3373_ = l_Lean_Expr_const___override(v___x_3372_, v___x_3371_);
    return v___x_3373_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3378_ = leanh::lean_box(0);
    v___x_3379_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15;
    v___x_3380_ = l_Lean_Expr_const___override(v___x_3379_, v___x_3378_);
    return v___x_3380_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3393_ = leanh::lean_unsigned_to_nat(0);
    v___x_3394_ = l_Lean_Level_ofNat(v___x_3393_);
    return v___x_3394_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3400_ = leanh::lean_unsigned_to_nat(0);
    v___x_3401_ = l_Lean_mkNatLit(v___x_3400_);
    return v___x_3401_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38()
-> *mut leanh::LeanObject {
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3424_ = leanh::lean_unsigned_to_nat(0);
    v___x_3425_ = lean_nat_to_int(v___x_3424_);
    return v___x_3425_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39() -> u8 {
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: u8 = 0;
    v___x_3426_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38,
    );
    v___x_3427_ = lean_int_dec_le(v___x_3426_, v___x_3426_);
    return v___x_3427_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45()
-> *mut leanh::LeanObject {
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3437_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38,
    );
    v___x_3438_ = lean_int_neg(v___x_3437_);
    return v___x_3438_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46()
-> *mut leanh::LeanObject {
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3439_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45,
    );
    v___x_3440_ = l_Int_toNat(v___x_3439_);
    return v___x_3440_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47()
-> *mut leanh::LeanObject {
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3441_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46,
    );
    v___x_3442_ = l_Lean_instToExprInt_mkNat(v___x_3441_);
    return v___x_3442_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48()
-> *mut leanh::LeanObject {
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3443_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38,
    );
    v___x_3444_ = l_Int_toNat(v___x_3443_);
    return v___x_3444_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49()
-> *mut leanh::LeanObject {
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3445_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48,
    );
    v___x_3446_ = l_Lean_instToExprInt_mkNat(v___x_3445_);
    return v___x_3446_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50()
-> *mut leanh::LeanObject {
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3447_ = leanh::lean_box(0);
    v___x_3448_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23,
    );
    v___x_3449_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3449_, 0, v___x_3448_);
    leanh::lean_ctor_set(v___x_3449_, 1, v___x_3447_);
    return v___x_3449_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51()
-> *mut leanh::LeanObject {
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3450_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50,
    );
    v___x_3451_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22;
    v___x_3452_ = l_Lean_Expr_const___override(v___x_3451_, v___x_3450_);
    return v___x_3452_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54()
-> *mut leanh::LeanObject {
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3457_ = leanh::lean_box(0);
    v___x_3458_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53;
    v___x_3459_ = l_Lean_Expr_const___override(v___x_3458_, v___x_3457_);
    return v___x_3459_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57()
-> *mut leanh::LeanObject {
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3466_ = leanh::lean_box(0);
    v___x_3467_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56;
    v___x_3468_ = l_Lean_Expr_const___override(v___x_3467_, v___x_3466_);
    return v___x_3468_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58()
-> *mut leanh::LeanObject {
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3469_ = leanh::lean_box(0);
    v___x_3470_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33;
    v___x_3471_ = l_Lean_Expr_const___override(v___x_3470_, v___x_3469_);
    return v___x_3471_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59()
-> *mut leanh::LeanObject {
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3472_ = leanh::lean_box(0);
    v___x_3473_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35;
    v___x_3474_ = l_Lean_Expr_const___override(v___x_3473_, v___x_3472_);
    return v___x_3474_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60()
-> *mut leanh::LeanObject {
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3475_ = leanh::lean_box(0);
    v___x_3476_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37;
    v___x_3477_ = l_Lean_Expr_const___override(v___x_3476_, v___x_3475_);
    return v___x_3477_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61()
-> *mut leanh::LeanObject {
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3478_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50,
    );
    v___x_3479_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42;
    v___x_3480_ = l_Lean_Expr_const___override(v___x_3479_, v___x_3478_);
    return v___x_3480_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62()
-> *mut leanh::LeanObject {
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3481_ = leanh::lean_box(0);
    v___x_3482_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44;
    v___x_3483_ = l_Lean_Expr_const___override(v___x_3482_, v___x_3481_);
    return v___x_3483_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63()
-> *mut leanh::LeanObject {
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3484_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47,
    );
    v___x_3485_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62,
    );
    v___x_3486_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once),
        _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2,
    );
    v___x_3487_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61,
    );
    v___x_3488_ = l_Lean_mkApp3(v___x_3487_, v___x_3486_, v___x_3485_, v___x_3484_);
    return v___x_3488_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66()
-> *mut leanh::LeanObject {
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3492_ = leanh::lean_unsigned_to_nat(1);
    v___x_3493_ = l_Lean_Level_ofNat(v___x_3492_);
    return v___x_3493_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67()
-> *mut leanh::LeanObject {
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3494_ = leanh::lean_box(0);
    v___x_3495_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66,
    );
    v___x_3496_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3496_, 0, v___x_3495_);
    leanh::lean_ctor_set(v___x_3496_, 1, v___x_3494_);
    return v___x_3496_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68()
-> *mut leanh::LeanObject {
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3497_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67,
    );
    v___x_3498_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65;
    v___x_3499_ = l_Lean_Expr_const___override(v___x_3498_, v___x_3497_);
    return v___x_3499_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71()
-> *mut leanh::LeanObject {
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3504_ = leanh::lean_box(0);
    v___x_3505_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70;
    v___x_3506_ = l_Lean_Expr_const___override(v___x_3505_, v___x_3504_);
    return v___x_3506_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74()
-> *mut leanh::LeanObject {
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3511_ = leanh::lean_box(0);
    v___x_3512_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73;
    v___x_3513_ = l_Lean_Expr_const___override(v___x_3512_, v___x_3511_);
    return v___x_3513_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94()
-> *mut leanh::LeanObject {
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3552_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50,
    );
    v___x_3553_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93;
    v___x_3554_ = l_Lean_Expr_const___override(v___x_3553_, v___x_3552_);
    return v___x_3554_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(
    mut v_e_3555_: *mut leanh::LeanObject,
    mut v_a_3556_: *mut leanh::LeanObject,
    mut v_a_3557_: *mut leanh::LeanObject,
    mut v_a_3558_: *mut leanh::LeanObject,
    mut v_a_3559_: *mut leanh::LeanObject,
    mut v_a_3560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3587_: u8 = 0;
    let mut v_str_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: u8 = 0;
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: u8 = 0;
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: u8 = 0;
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: u8 = 0;
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: u8 = 0;
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: u8 = 0;
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: u8 = 0;
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: u8 = 0;
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: u8 = 0;
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: u8 = 0;
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: u8 = 0;
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3652_: u8 = 0;
    let mut v_str_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v_str_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: u8 = 0;
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: u8 = 0;
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: u8 = 0;
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: u8 = 0;
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3692_: u8 = 0;
    let mut v_unused_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: u8 = 0;
    let mut v___x_3696_: u8 = 0;
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: u8 = 0;
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: u8 = 0;
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: u8 = 0;
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3719_: u8 = 0;
    let mut v_str_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: u8 = 0;
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: u8 = 0;
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u8 = 0;
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: u8 = 0;
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b__pos_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3746_: u8 = 0;
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: u8 = 0;
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_a_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3789_: u8 = 0;
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3793_: u8 = 0;
    let mut v_reuseFailAlloc_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut v_unused_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: u8 = 0;
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: u8 = 0;
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b__pos_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3818_: u8 = 0;
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3836_: u8 = 0;
    let mut v_a_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3840_: u8 = 0;
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3844_: u8 = 0;
    let mut v___x_3845_: u8 = 0;
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3848_: u8 = 0;
    let mut v_unused_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: u8 = 0;
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: u8 = 0;
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: u8 = 0;
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ne__zero_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3878_: u8 = 0;
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3890_: u8 = 0;
    let mut v_a_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3894_: u8 = 0;
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3898_: u8 = 0;
    let mut v_a_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3902_: u8 = 0;
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut v___x_3907_: u8 = 0;
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: u8 = 0;
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: u8 = 0;
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: u8 = 0;
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v_splitNatSub_3935_: u8 = 0;
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: u8 = 0;
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: u8 = 0;
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3977_: u8 = 0;
    let mut v_str_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: u8 = 0;
    let mut v___x_3982_: u8 = 0;
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: u8 = 0;
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: u8 = 0;
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: u8 = 0;
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: u8 = 0;
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: u8 = 0;
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: u8 = 0;
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: u8 = 0;
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: u8 = 0;
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: u8 = 0;
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4034_: u8 = 0;
    let mut v_unused_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: u8 = 0;
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: u8 = 0;
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: u8 = 0;
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: u8 = 0;
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: u8 = 0;
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: u8 = 0;
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: u8 = 0;
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: u8 = 0;
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: u8 = 0;
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4081_: u8 = 0;
    let mut v_unused_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4086_: u8 = 0;
    let mut v_str_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: u8 = 0;
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4113_: u8 = 0;
    let mut v_unused_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3580_ = l_Lean_Expr_getAppFnArgs(v_e_3555_);
                v_fst_3581_ = leanh::lean_ctor_get(v___x_3580_, 0);
                leanh::lean_inc(v_fst_3581_);
                if leanh::lean_obj_tag(v_fst_3581_) == 1 {
                    v_pre_3582_ = leanh::lean_ctor_get(v_fst_3581_, 0);
                    match leanh::lean_obj_tag(v_pre_3582_) {
                        1 => {
                            leanh::lean_inc_ref(v_pre_3582_);
                            v_pre_3583_ = leanh::lean_ctor_get(v_pre_3582_, 0);
                            if leanh::lean_obj_tag(v_pre_3583_) == 0 {
                                v_snd_3584_ = leanh::lean_ctor_get(v___x_3580_, 1);
                                v_isSharedCheck_4081_ =
                                    (!leanh::lean_is_exclusive(v___x_3580_)) as u8;
                                if v_isSharedCheck_4081_ == 0 {
                                    v_unused_4082_ = leanh::lean_ctor_get(v___x_3580_, 0);
                                    leanh::lean_dec(v_unused_4082_);
                                    v___x_3586_ = v___x_3580_;
                                    v_isShared_3587_ = v_isSharedCheck_4081_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_snd_3584_);
                                    leanh::lean_dec(v___x_3580_);
                                    v___x_3586_ = leanh::lean_box(0);
                                    v_isShared_3587_ = v_isSharedCheck_4081_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_pre_3582_, 2);
                                leanh::lean_dec_ref_known(v_fst_3581_, 2);
                                leanh::lean_dec_ref(v___x_3580_);
                                state = 3;
                                continue;
                            }
                        }
                        0 => {
                            v_snd_4083_ = leanh::lean_ctor_get(v___x_3580_, 1);
                            v_isSharedCheck_4113_ =
                                (!leanh::lean_is_exclusive(v___x_3580_)) as u8;
                            if v_isSharedCheck_4113_ == 0 {
                                v_unused_4114_ = leanh::lean_ctor_get(v___x_3580_, 0);
                                leanh::lean_dec(v_unused_4114_);
                                v___x_4085_ = v___x_3580_;
                                v_isShared_4086_ = v_isSharedCheck_4113_;
                                state = 45;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_4083_);
                                leanh::lean_dec(v___x_3580_);
                                v___x_4085_ = leanh::lean_box(0);
                                v_isShared_4086_ = v_isSharedCheck_4113_;
                                state = 45;
                                continue;
                            }
                        }
                        _ => {
                            leanh::lean_dec_ref_known(v_fst_3581_, 2);
                            leanh::lean_dec_ref(v___x_3580_);
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_3581_);
                    leanh::lean_dec_ref(v___x_3580_);
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_3563_ = leanh::lean_box(0);
                v___x_3564_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3564_, 0, v___x_3563_);
                return v___x_3564_;
            }
            2 => {
                v___x_3566_ = leanh::lean_box(0);
                v___x_3567_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3567_, 0, v___x_3566_);
                return v___x_3567_;
            }
            3 => {
                v___x_3569_ = leanh::lean_box(0);
                v___x_3570_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3570_, 0, v___x_3569_);
                return v___x_3570_;
            }
            4 => {
                v___x_3572_ = leanh::lean_box(0);
                v___x_3573_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3573_, 0, v___x_3572_);
                return v___x_3573_;
            }
            5 => {
                v___x_3575_ = leanh::lean_box(0);
                v___x_3576_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3576_, 0, v___x_3575_);
                return v___x_3576_;
            }
            6 => {
                v___x_3578_ = leanh::lean_box(0);
                v___x_3579_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3579_, 0, v___x_3578_);
                return v___x_3579_;
            }
            7 => {
                v_str_3588_ = leanh::lean_ctor_get(v_fst_3581_, 1);
                leanh::lean_inc_ref(v_str_3588_);
                leanh::lean_dec_ref_known(v_fst_3581_, 2);
                v_str_3589_ = leanh::lean_ctor_get(v_pre_3582_, 1);
                leanh::lean_inc_ref(v_str_3589_);
                leanh::lean_dec_ref_known(v_pre_3582_, 2);
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
                                leanh::lean_dec_ref(v_str_3589_);
                                if v___x_3599_ == 0 {
                                    leanh::lean_dec_ref(v_str_3588_);
                                    leanh::lean_del_object(v___x_3586_);
                                    leanh::lean_dec(v_snd_3584_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3600_ =
                                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3;
                                    v___x_3601_ = lean_string_dec_eq(v_str_3588_, v___x_3600_);
                                    leanh::lean_dec_ref(v_str_3588_);
                                    if v___x_3601_ == 0 {
                                        leanh::lean_del_object(v___x_3586_);
                                        leanh::lean_dec(v_snd_3584_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_3602_ = lean_array_get_size(v_snd_3584_);
                                        v___x_3603_ = leanh::lean_unsigned_to_nat(4);
                                        v___x_3604_ = lean_nat_dec_eq(v___x_3602_, v___x_3603_);
                                        if v___x_3604_ == 0 {
                                            leanh::lean_del_object(v___x_3586_);
                                            leanh::lean_dec(v_snd_3584_);
                                            state = 3;
                                            continue;
                                        } else {
                                            v___x_3605_ = leanh::lean_unsigned_to_nat(2);
                                            v___x_3606_ = lean_array_fget(v_snd_3584_, v___x_3605_);
                                            v___x_3607_ = leanh::lean_unsigned_to_nat(3);
                                            v___x_3608_ = lean_array_fget(v_snd_3584_, v___x_3607_);
                                            leanh::lean_dec(v_snd_3584_);
                                            v___x_3609_ = leanh::lean_box(0);
                                            v___x_3610_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6);
                                            leanh::lean_inc(v___x_3608_);
                                            leanh::lean_inc(v___x_3606_);
                                            v___x_3611_ = l_Lean_mkAppB(
                                                v___x_3610_,
                                                v___x_3606_,
                                                v___x_3608_,
                                            );
                                            v___x_3612_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9);
                                            v___x_3613_ = l_Lean_mkAppB(
                                                v___x_3612_,
                                                v___x_3606_,
                                                v___x_3608_,
                                            );
                                            if v_isShared_3587_ == 0 {
                                                leanh::lean_ctor_set_tag(v___x_3586_, 1);
                                                leanh::lean_ctor_set(
                                                    v___x_3586_,
                                                    1,
                                                    v___x_3609_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_3586_,
                                                    0,
                                                    v___x_3613_,
                                                );
                                                v___x_3615_ = v___x_3586_;
                                                state = 8;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_3618_ =
                                                    leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v_reuseFailAlloc_3618_,
                                                    0,
                                                    v___x_3613_,
                                                );
                                                leanh::lean_ctor_set(
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
                                leanh::lean_dec_ref(v_str_3589_);
                                v___x_3619_ =
                                    l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
                                v___x_3620_ = lean_string_dec_eq(v_str_3588_, v___x_3619_);
                                leanh::lean_dec_ref(v_str_3588_);
                                if v___x_3620_ == 0 {
                                    leanh::lean_del_object(v___x_3586_);
                                    leanh::lean_dec(v_snd_3584_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3621_ = lean_array_get_size(v_snd_3584_);
                                    v___x_3622_ = leanh::lean_unsigned_to_nat(4);
                                    v___x_3623_ = lean_nat_dec_eq(v___x_3621_, v___x_3622_);
                                    if v___x_3623_ == 0 {
                                        leanh::lean_del_object(v___x_3586_);
                                        leanh::lean_dec(v_snd_3584_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_3624_ = leanh::lean_unsigned_to_nat(2);
                                        v___x_3625_ = lean_array_fget(v_snd_3584_, v___x_3624_);
                                        v___x_3626_ = leanh::lean_unsigned_to_nat(3);
                                        v___x_3627_ = lean_array_fget(v_snd_3584_, v___x_3626_);
                                        leanh::lean_dec(v_snd_3584_);
                                        v___x_3628_ = leanh::lean_box(0);
                                        v___x_3629_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13);
                                        leanh::lean_inc(v___x_3627_);
                                        leanh::lean_inc(v___x_3625_);
                                        v___x_3630_ =
                                            l_Lean_mkAppB(v___x_3629_, v___x_3625_, v___x_3627_);
                                        v___x_3631_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16);
                                        v___x_3632_ =
                                            l_Lean_mkAppB(v___x_3631_, v___x_3625_, v___x_3627_);
                                        if v_isShared_3587_ == 0 {
                                            leanh::lean_ctor_set_tag(v___x_3586_, 1);
                                            leanh::lean_ctor_set(
                                                v___x_3586_,
                                                1,
                                                v___x_3628_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_3586_,
                                                0,
                                                v___x_3632_,
                                            );
                                            v___x_3634_ = v___x_3586_;
                                            state = 9;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3637_ =
                                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3637_,
                                                0,
                                                v___x_3632_,
                                            );
                                            leanh::lean_ctor_set(
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
                            leanh::lean_dec_ref(v_str_3589_);
                            v___x_3638_ =
                                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17;
                            v___x_3639_ = lean_string_dec_eq(v_str_3588_, v___x_3638_);
                            leanh::lean_dec_ref(v_str_3588_);
                            if v___x_3639_ == 0 {
                                leanh::lean_del_object(v___x_3586_);
                                leanh::lean_dec(v_snd_3584_);
                                state = 3;
                                continue;
                            } else {
                                v___x_3640_ = lean_array_get_size(v_snd_3584_);
                                v___x_3641_ = leanh::lean_unsigned_to_nat(6);
                                v___x_3642_ = lean_nat_dec_eq(v___x_3640_, v___x_3641_);
                                if v___x_3642_ == 0 {
                                    leanh::lean_del_object(v___x_3586_);
                                    leanh::lean_dec(v_snd_3584_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3643_ = leanh::lean_unsigned_to_nat(5);
                                    v___x_3644_ = lean_array_fget(v_snd_3584_, v___x_3643_);
                                    leanh::lean_inc(v___x_3644_);
                                    v___x_3645_ = l_Lean_Expr_getAppFnArgs(v___x_3644_);
                                    v_fst_3646_ = leanh::lean_ctor_get(v___x_3645_, 0);
                                    leanh::lean_inc(v_fst_3646_);
                                    if leanh::lean_obj_tag(v_fst_3646_) == 1 {
                                        v_pre_3647_ = leanh::lean_ctor_get(v_fst_3646_, 0);
                                        leanh::lean_inc(v_pre_3647_);
                                        if leanh::lean_obj_tag(v_pre_3647_) == 1 {
                                            v_pre_3648_ =
                                                leanh::lean_ctor_get(v_pre_3647_, 0);
                                            if leanh::lean_obj_tag(v_pre_3648_) == 0 {
                                                v_snd_3649_ =
                                                    leanh::lean_ctor_get(v___x_3645_, 1);
                                                v_isSharedCheck_3848_ =
                                                    (!leanh::lean_is_exclusive(v___x_3645_))
                                                        as u8;
                                                if v_isSharedCheck_3848_ == 0 {
                                                    v_unused_3849_ =
                                                        leanh::lean_ctor_get(v___x_3645_, 0);
                                                    leanh::lean_dec(v_unused_3849_);
                                                    v___x_3651_ = v___x_3645_;
                                                    v_isShared_3652_ = v_isSharedCheck_3848_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_snd_3649_);
                                                    leanh::lean_dec(v___x_3645_);
                                                    v___x_3651_ = leanh::lean_box(0);
                                                    v_isShared_3652_ = v_isSharedCheck_3848_;
                                                    state = 10;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec_ref_known(v_pre_3647_, 2);
                                                leanh::lean_dec_ref_known(v_fst_3646_, 2);
                                                leanh::lean_dec_ref(v___x_3645_);
                                                leanh::lean_dec(v___x_3644_);
                                                leanh::lean_del_object(v___x_3586_);
                                                leanh::lean_dec(v_snd_3584_);
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref_known(v_fst_3646_, 2);
                                            leanh::lean_dec(v_pre_3647_);
                                            leanh::lean_dec_ref(v___x_3645_);
                                            leanh::lean_dec(v___x_3644_);
                                            leanh::lean_del_object(v___x_3586_);
                                            leanh::lean_dec(v_snd_3584_);
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_fst_3646_);
                                        leanh::lean_dec_ref(v___x_3645_);
                                        leanh::lean_dec(v___x_3644_);
                                        leanh::lean_del_object(v___x_3586_);
                                        leanh::lean_dec(v_snd_3584_);
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_str_3589_);
                        v___x_3850_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
                        v___x_3851_ = lean_string_dec_eq(v_str_3588_, v___x_3850_);
                        leanh::lean_dec_ref(v_str_3588_);
                        if v___x_3851_ == 0 {
                            leanh::lean_del_object(v___x_3586_);
                            leanh::lean_dec(v_snd_3584_);
                            state = 3;
                            continue;
                        } else {
                            v___x_3852_ = lean_array_get_size(v_snd_3584_);
                            v___x_3853_ = leanh::lean_unsigned_to_nat(6);
                            v___x_3854_ = lean_nat_dec_eq(v___x_3852_, v___x_3853_);
                            if v___x_3854_ == 0 {
                                leanh::lean_del_object(v___x_3586_);
                                leanh::lean_dec(v_snd_3584_);
                                state = 3;
                                continue;
                            } else {
                                v___x_3855_ = leanh::lean_unsigned_to_nat(5);
                                v___x_3856_ = lean_array_fget(v_snd_3584_, v___x_3855_);
                                leanh::lean_inc(v___x_3856_);
                                v___x_3857_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_3856_);
                                if leanh::lean_obj_tag(v___x_3857_) == 0 {
                                    leanh::lean_dec(v___x_3856_);
                                    leanh::lean_del_object(v___x_3586_);
                                    leanh::lean_dec(v_snd_3584_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_3858_ = leanh::lean_ctor_get(v___x_3857_, 0);
                                    leanh::lean_inc(v_val_3858_);
                                    leanh::lean_dec_ref_known(v___x_3857_, 1);
                                    v___x_3859_ = leanh::lean_unsigned_to_nat(0);
                                    v___x_3860_ = lean_nat_dec_eq(v_val_3858_, v___x_3859_);
                                    leanh::lean_dec(v_val_3858_);
                                    if v___x_3860_ == 0 {
                                        v___x_3861_ = leanh::lean_unsigned_to_nat(4);
                                        v___x_3862_ = lean_array_fget(v_snd_3584_, v___x_3861_);
                                        leanh::lean_dec(v_snd_3584_);
                                        v___x_3863_ = leanh::lean_box(0);
                                        v___x_3864_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68);
                                        v___x_3865_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once), _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
                                        v___x_3907_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
                                        if v___x_3907_ == 0 {
                                            v___x_3908_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
                                            v___y_3867_ = v___x_3908_;
                                            state = 30;
                                            continue;
                                        } else {
                                            v___x_3909_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
                                            v___y_3867_ = v___x_3909_;
                                            state = 30;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v___x_3856_);
                                        leanh::lean_del_object(v___x_3586_);
                                        leanh::lean_dec(v_snd_3584_);
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_str_3589_);
                    v___x_3910_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                    v___x_3911_ = lean_string_dec_eq(v_str_3588_, v___x_3910_);
                    leanh::lean_dec_ref(v_str_3588_);
                    if v___x_3911_ == 0 {
                        leanh::lean_del_object(v___x_3586_);
                        leanh::lean_dec(v_snd_3584_);
                        state = 3;
                        continue;
                    } else {
                        v___x_3912_ = lean_array_get_size(v_snd_3584_);
                        v___x_3913_ = leanh::lean_unsigned_to_nat(3);
                        v___x_3914_ = lean_nat_dec_eq(v___x_3912_, v___x_3913_);
                        if v___x_3914_ == 0 {
                            leanh::lean_del_object(v___x_3586_);
                            leanh::lean_dec(v_snd_3584_);
                            state = 3;
                            continue;
                        } else {
                            v___x_3915_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3916_ = lean_array_fget_borrowed(v_snd_3584_, v___x_3915_);
                            if leanh::lean_obj_tag(v___x_3916_) == 4 {
                                v_declName_3917_ = leanh::lean_ctor_get(v___x_3916_, 0);
                                if leanh::lean_obj_tag(v_declName_3917_) == 1 {
                                    v_pre_3918_ = leanh::lean_ctor_get(v_declName_3917_, 0);
                                    if leanh::lean_obj_tag(v_pre_3918_) == 0 {
                                        v_us_3919_ = leanh::lean_ctor_get(v___x_3916_, 1);
                                        leanh::lean_inc(v_us_3919_);
                                        v_str_3920_ =
                                            leanh::lean_ctor_get(v_declName_3917_, 1);
                                        v___x_3921_ =
                                            l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
                                        v___x_3934_ = lean_string_dec_eq(v_str_3920_, v___x_3921_);
                                        if v___x_3934_ == 0 {
                                            leanh::lean_dec(v_us_3919_);
                                            leanh::lean_del_object(v___x_3586_);
                                            leanh::lean_dec(v_snd_3584_);
                                            state = 3;
                                            continue;
                                        } else {
                                            if leanh::lean_obj_tag(v_us_3919_) == 0 {
                                                v_splitNatSub_3935_ =
                                                    leanh::lean_ctor_get_uint8(
                                                        v_a_3556_, 1 as u32,
                                                    );
                                                v___x_3936_ = leanh::lean_unsigned_to_nat(2);
                                                v___x_3937_ =
                                                    lean_array_fget(v_snd_3584_, v___x_3936_);
                                                leanh::lean_dec(v_snd_3584_);
                                                v___x_3938_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78;
                                                v___x_3939_ = l_Lean_Expr_const___override(
                                                    v___x_3938_,
                                                    v_us_3919_,
                                                );
                                                leanh::lean_inc(v___x_3937_);
                                                v___x_3940_ = l_Lean_Expr_app___override(
                                                    v___x_3939_,
                                                    v___x_3937_,
                                                );
                                                v___x_3941_ = leanh::lean_box(0);
                                                v_r_3942_ =
                                                    leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v_r_3942_,
                                                    0,
                                                    v___x_3940_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v_r_3942_,
                                                    1,
                                                    v___x_3941_,
                                                );
                                                if v_splitNatSub_3935_ == 1 {
                                                    v___x_3970_ =
                                                        l_Lean_Expr_getAppFnArgs(v___x_3937_);
                                                    v_fst_3971_ =
                                                        leanh::lean_ctor_get(v___x_3970_, 0);
                                                    leanh::lean_inc(v_fst_3971_);
                                                    if leanh::lean_obj_tag(v_fst_3971_) == 1
                                                    {
                                                        v_pre_3972_ = leanh::lean_ctor_get(
                                                            v_fst_3971_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_pre_3972_);
                                                        if leanh::lean_obj_tag(v_pre_3972_)
                                                            == 1
                                                        {
                                                            v_pre_3973_ =
                                                                leanh::lean_ctor_get(
                                                                    v_pre_3972_,
                                                                    0,
                                                                );
                                                            if leanh::lean_obj_tag(
                                                                v_pre_3973_,
                                                            ) == 0
                                                            {
                                                                v_snd_3974_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_3970_,
                                                                        1,
                                                                    );
                                                                v_isSharedCheck_4034_ = (!leanh::lean_is_exclusive(v___x_3970_)) as u8;
                                                                if v_isSharedCheck_4034_ == 0 {
                                                                    v_unused_4035_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_3970_,
                                                                            0,
                                                                        );
                                                                    leanh::lean_dec(
                                                                        v_unused_4035_,
                                                                    );
                                                                    v___x_3976_ = v___x_3970_;
                                                                    v_isShared_3977_ =
                                                                        v_isSharedCheck_4034_;
                                                                    state = 43;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_snd_3974_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_3970_,
                                                                    );
                                                                    v___x_3976_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_3977_ =
                                                                        v_isSharedCheck_4034_;
                                                                    state = 43;
                                                                    continue;
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref_known(
                                                                    v_pre_3972_,
                                                                    2,
                                                                );
                                                                leanh::lean_dec_ref_known(
                                                                    v_fst_3971_,
                                                                    2,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v___x_3970_,
                                                                );
                                                                leanh::lean_del_object(
                                                                    v___x_3586_,
                                                                );
                                                                v___x_4036_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
                                                                    v___x_4036_,
                                                                    0,
                                                                    v_r_3942_,
                                                                );
                                                                return v___x_4036_;
                                                            }
                                                        } else {
                                                            leanh::lean_dec_ref_known(
                                                                v_fst_3971_,
                                                                2,
                                                            );
                                                            leanh::lean_dec(v_pre_3972_);
                                                            leanh::lean_dec_ref(v___x_3970_);
                                                            leanh::lean_del_object(
                                                                v___x_3586_,
                                                            );
                                                            v___x_4037_ =
                                                                leanh::lean_alloc_ctor(
                                                                    0,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v___x_4037_,
                                                                0,
                                                                v_r_3942_,
                                                            );
                                                            return v___x_4037_;
                                                        }
                                                    } else {
                                                        leanh::lean_dec(v_fst_3971_);
                                                        leanh::lean_dec_ref(v___x_3970_);
                                                        leanh::lean_del_object(v___x_3586_);
                                                        v___x_4038_ = leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
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
                                                        leanh::lean_ctor_get(v___x_4039_, 0);
                                                    leanh::lean_inc(v_fst_4040_);
                                                    if leanh::lean_obj_tag(v_fst_4040_) == 1
                                                    {
                                                        v_pre_4041_ = leanh::lean_ctor_get(
                                                            v_fst_4040_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_pre_4041_);
                                                        if leanh::lean_obj_tag(v_pre_4041_)
                                                            == 1
                                                        {
                                                            v_pre_4042_ =
                                                                leanh::lean_ctor_get(
                                                                    v_pre_4041_,
                                                                    0,
                                                                );
                                                            if leanh::lean_obj_tag(
                                                                v_pre_4042_,
                                                            ) == 0
                                                            {
                                                                v_snd_4043_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_4039_,
                                                                        1,
                                                                    );
                                                                leanh::lean_inc(v_snd_4043_);
                                                                leanh::lean_dec_ref(
                                                                    v___x_4039_,
                                                                );
                                                                v_str_4044_ =
                                                                    leanh::lean_ctor_get(
                                                                        v_fst_4040_,
                                                                        1,
                                                                    );
                                                                leanh::lean_inc_ref(
                                                                    v_str_4044_,
                                                                );
                                                                leanh::lean_dec_ref_known(
                                                                    v_fst_4040_,
                                                                    2,
                                                                );
                                                                v_str_4045_ =
                                                                    leanh::lean_ctor_get(
                                                                        v_pre_4041_,
                                                                        1,
                                                                    );
                                                                leanh::lean_inc_ref(
                                                                    v_str_4045_,
                                                                );
                                                                leanh::lean_dec_ref_known(
                                                                    v_pre_4041_,
                                                                    2,
                                                                );
                                                                v___x_4046_ = lean_string_dec_eq(
                                                                    v_str_4045_,
                                                                    v___x_3921_,
                                                                );
                                                                if v___x_4046_ == 0 {
                                                                    leanh::lean_del_object(
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
                                                                        leanh::lean_dec_ref(
                                                                            v_str_4045_,
                                                                        );
                                                                        if v___x_4050_ == 0 {
                                                                            leanh::lean_dec_ref(v_str_4044_);
                                                                            leanh::lean_dec(
                                                                                v_snd_4043_,
                                                                            );
                                                                            v___x_4051_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                            leanh::lean_ctor_set(v___x_4051_, 0, v_r_3942_);
                                                                            return v___x_4051_;
                                                                        } else {
                                                                            v___x_4052_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86;
                                                                            v___x_4053_ =
                                                                                lean_string_dec_eq(
                                                                                    v_str_4044_,
                                                                                    v___x_4052_,
                                                                                );
                                                                            leanh::lean_dec_ref(v_str_4044_);
                                                                            if v___x_4053_ == 0 {
                                                                                leanh::lean_dec(v_snd_4043_);
                                                                                v___x_4054_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                                leanh::lean_ctor_set(v___x_4054_, 0, v_r_3942_);
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
                                                                                    leanh::lean_dec(v_snd_4043_);
                                                                                    v___x_4057_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                                    leanh::lean_ctor_set(v___x_4057_, 0, v_r_3942_);
                                                                                    return v___x_4057_;
                                                                                } else {
                                                                                    v___x_4058_ = lean_array_fget(v_snd_4043_, v___x_3915_);
                                                                                    v___x_4059_ = leanh::lean_unsigned_to_nat(1);
                                                                                    v___x_4060_ = lean_array_fget(v_snd_4043_, v___x_4059_);
                                                                                    leanh::lean_dec(v_snd_4043_);
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
                                                                        leanh::lean_dec_ref(
                                                                            v_str_4045_,
                                                                        );
                                                                        v___x_4061_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87;
                                                                        v___x_4062_ =
                                                                            lean_string_dec_eq(
                                                                                v_str_4044_,
                                                                                v___x_4061_,
                                                                            );
                                                                        leanh::lean_dec_ref(
                                                                            v_str_4044_,
                                                                        );
                                                                        if v___x_4062_ == 0 {
                                                                            leanh::lean_dec(
                                                                                v_snd_4043_,
                                                                            );
                                                                            v___x_4063_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                            leanh::lean_ctor_set(v___x_4063_, 0, v_r_3942_);
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
                                                                                leanh::lean_dec(v_snd_4043_);
                                                                                v___x_4066_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                                leanh::lean_ctor_set(v___x_4066_, 0, v_r_3942_);
                                                                                return v___x_4066_;
                                                                            } else {
                                                                                v___x_4067_ =
                                                                                    lean_array_fget(
                                                                                        v_snd_4043_,
                                                                                        v___x_3915_,
                                                                                    );
                                                                                v___x_4068_ = leanh::lean_unsigned_to_nat(1);
                                                                                v___x_4069_ =
                                                                                    lean_array_fget(
                                                                                        v_snd_4043_,
                                                                                        v___x_4068_,
                                                                                    );
                                                                                leanh::lean_dec(v_snd_4043_);
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
                                                                    leanh::lean_dec_ref(
                                                                        v_str_4045_,
                                                                    );
                                                                    v___x_4070_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88;
                                                                    v___x_4071_ =
                                                                        lean_string_dec_eq(
                                                                            v_str_4044_,
                                                                            v___x_4070_,
                                                                        );
                                                                    leanh::lean_dec_ref(
                                                                        v_str_4044_,
                                                                    );
                                                                    if v___x_4071_ == 0 {
                                                                        leanh::lean_dec(
                                                                            v_snd_4043_,
                                                                        );
                                                                        leanh::lean_del_object(v___x_3586_);
                                                                        v___x_4072_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                        leanh::lean_ctor_set(
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
                                                                        v___x_4074_ = leanh::lean_unsigned_to_nat(1);
                                                                        v___x_4075_ =
                                                                            lean_nat_dec_eq(
                                                                                v___x_4073_,
                                                                                v___x_4074_,
                                                                            );
                                                                        if v___x_4075_ == 0 {
                                                                            leanh::lean_dec(
                                                                                v_snd_4043_,
                                                                            );
                                                                            leanh::lean_del_object(v___x_3586_);
                                                                            v___x_4076_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                            leanh::lean_ctor_set(v___x_4076_, 0, v_r_3942_);
                                                                            return v___x_4076_;
                                                                        } else {
                                                                            v___x_4077_ =
                                                                                lean_array_fget(
                                                                                    v_snd_4043_,
                                                                                    v___x_3915_,
                                                                                );
                                                                            leanh::lean_dec(
                                                                                v_snd_4043_,
                                                                            );
                                                                            v_x_3964_ = v___x_4077_;
                                                                            state = 42;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref_known(
                                                                    v_pre_4041_,
                                                                    2,
                                                                );
                                                                leanh::lean_dec_ref_known(
                                                                    v_fst_4040_,
                                                                    2,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v___x_4039_,
                                                                );
                                                                leanh::lean_del_object(
                                                                    v___x_3586_,
                                                                );
                                                                v___x_4078_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
                                                                    v___x_4078_,
                                                                    0,
                                                                    v_r_3942_,
                                                                );
                                                                return v___x_4078_;
                                                            }
                                                        } else {
                                                            leanh::lean_dec_ref_known(
                                                                v_fst_4040_,
                                                                2,
                                                            );
                                                            leanh::lean_dec(v_pre_4041_);
                                                            leanh::lean_dec_ref(v___x_4039_);
                                                            leanh::lean_del_object(
                                                                v___x_3586_,
                                                            );
                                                            v___x_4079_ =
                                                                leanh::lean_alloc_ctor(
                                                                    0,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v___x_4079_,
                                                                0,
                                                                v_r_3942_,
                                                            );
                                                            return v___x_4079_;
                                                        }
                                                    } else {
                                                        leanh::lean_dec(v_fst_4040_);
                                                        leanh::lean_dec_ref(v___x_4039_);
                                                        leanh::lean_del_object(v___x_3586_);
                                                        v___x_4080_ = leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_4080_,
                                                            0,
                                                            v_r_3942_,
                                                        );
                                                        return v___x_4080_;
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec(v_us_3919_);
                                                leanh::lean_del_object(v___x_3586_);
                                                leanh::lean_dec(v_snd_3584_);
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_del_object(v___x_3586_);
                                        leanh::lean_dec(v_snd_3584_);
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_3586_);
                                    leanh::lean_dec(v_snd_3584_);
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_del_object(v___x_3586_);
                                leanh::lean_dec(v_snd_3584_);
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            8 => {
                v___x_3616_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3616_, 0, v___x_3611_);
                leanh::lean_ctor_set(v___x_3616_, 1, v___x_3615_);
                v___x_3617_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3617_, 0, v___x_3616_);
                return v___x_3617_;
            }
            9 => {
                v___x_3635_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3635_, 0, v___x_3630_);
                leanh::lean_ctor_set(v___x_3635_, 1, v___x_3634_);
                v___x_3636_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3636_, 0, v___x_3635_);
                return v___x_3636_;
            }
            10 => {
                v_str_3653_ = leanh::lean_ctor_get(v_fst_3646_, 1);
                leanh::lean_inc_ref(v_str_3653_);
                leanh::lean_dec_ref_known(v_fst_3646_, 2);
                v_str_3654_ = leanh::lean_ctor_get(v_pre_3647_, 1);
                leanh::lean_inc_ref(v_str_3654_);
                leanh::lean_dec_ref_known(v_pre_3647_, 2);
                v___x_3655_ = leanh::lean_unsigned_to_nat(4);
                v___x_3656_ = lean_array_fget(v_snd_3584_, v___x_3655_);
                leanh::lean_dec(v_snd_3584_);
                v___x_3694_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
                v___x_3695_ = lean_string_dec_eq(v_str_3654_, v___x_3694_);
                if v___x_3695_ == 0 {
                    v___x_3696_ = lean_string_dec_eq(v_str_3654_, v___x_3590_);
                    leanh::lean_dec_ref(v_str_3654_);
                    if v___x_3696_ == 0 {
                        leanh::lean_dec(v___x_3656_);
                        leanh::lean_dec_ref(v_str_3653_);
                        leanh::lean_del_object(v___x_3651_);
                        leanh::lean_dec(v_snd_3649_);
                        leanh::lean_dec(v___x_3644_);
                        leanh::lean_del_object(v___x_3586_);
                        state = 4;
                        continue;
                    } else {
                        v___x_3697_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                        v___x_3698_ = lean_string_dec_eq(v_str_3653_, v___x_3697_);
                        leanh::lean_dec_ref(v_str_3653_);
                        if v___x_3698_ == 0 {
                            leanh::lean_dec(v___x_3656_);
                            leanh::lean_del_object(v___x_3651_);
                            leanh::lean_dec(v_snd_3649_);
                            leanh::lean_dec(v___x_3644_);
                            leanh::lean_del_object(v___x_3586_);
                            state = 4;
                            continue;
                        } else {
                            v___x_3699_ = lean_array_get_size(v_snd_3649_);
                            v___x_3700_ = leanh::lean_unsigned_to_nat(3);
                            v___x_3701_ = lean_nat_dec_eq(v___x_3699_, v___x_3700_);
                            if v___x_3701_ == 0 {
                                leanh::lean_dec(v___x_3656_);
                                leanh::lean_del_object(v___x_3651_);
                                leanh::lean_dec(v_snd_3649_);
                                leanh::lean_dec(v___x_3644_);
                                leanh::lean_del_object(v___x_3586_);
                                state = 4;
                                continue;
                            } else {
                                v___x_3702_ = leanh::lean_unsigned_to_nat(0);
                                v___x_3703_ = lean_array_fget_borrowed(v_snd_3649_, v___x_3702_);
                                if leanh::lean_obj_tag(v___x_3703_) == 4 {
                                    v_declName_3704_ = leanh::lean_ctor_get(v___x_3703_, 0);
                                    if leanh::lean_obj_tag(v_declName_3704_) == 1 {
                                        v_pre_3705_ =
                                            leanh::lean_ctor_get(v_declName_3704_, 0);
                                        if leanh::lean_obj_tag(v_pre_3705_) == 0 {
                                            v_us_3706_ =
                                                leanh::lean_ctor_get(v___x_3703_, 1);
                                            leanh::lean_inc(v_us_3706_);
                                            v_str_3707_ =
                                                leanh::lean_ctor_get(v_declName_3704_, 1);
                                            v___x_3708_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
                                            v___x_3709_ =
                                                lean_string_dec_eq(v_str_3707_, v___x_3708_);
                                            if v___x_3709_ == 0 {
                                                leanh::lean_dec(v_us_3706_);
                                                leanh::lean_dec(v___x_3656_);
                                                leanh::lean_del_object(v___x_3651_);
                                                leanh::lean_dec(v_snd_3649_);
                                                leanh::lean_dec(v___x_3644_);
                                                leanh::lean_del_object(v___x_3586_);
                                                state = 4;
                                                continue;
                                            } else {
                                                if leanh::lean_obj_tag(v_us_3706_) == 0 {
                                                    v___x_3710_ =
                                                        leanh::lean_unsigned_to_nat(2);
                                                    v___x_3711_ =
                                                        lean_array_fget(v_snd_3649_, v___x_3710_);
                                                    leanh::lean_dec(v_snd_3649_);
                                                    leanh::lean_inc(v___x_3711_);
                                                    v___x_3712_ =
                                                        l_Lean_Expr_getAppFnArgs(v___x_3711_);
                                                    v_fst_3713_ =
                                                        leanh::lean_ctor_get(v___x_3712_, 0);
                                                    leanh::lean_inc(v_fst_3713_);
                                                    if leanh::lean_obj_tag(v_fst_3713_) == 1
                                                    {
                                                        v_pre_3714_ = leanh::lean_ctor_get(
                                                            v_fst_3713_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_pre_3714_);
                                                        if leanh::lean_obj_tag(v_pre_3714_)
                                                            == 1
                                                        {
                                                            v_pre_3715_ =
                                                                leanh::lean_ctor_get(
                                                                    v_pre_3714_,
                                                                    0,
                                                                );
                                                            if leanh::lean_obj_tag(
                                                                v_pre_3715_,
                                                            ) == 0
                                                            {
                                                                v_snd_3716_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_3712_,
                                                                        1,
                                                                    );
                                                                v_isSharedCheck_3795_ = (!leanh::lean_is_exclusive(v___x_3712_)) as u8;
                                                                if v_isSharedCheck_3795_ == 0 {
                                                                    v_unused_3796_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_3712_,
                                                                            0,
                                                                        );
                                                                    leanh::lean_dec(
                                                                        v_unused_3796_,
                                                                    );
                                                                    v___x_3718_ = v___x_3712_;
                                                                    v_isShared_3719_ =
                                                                        v_isSharedCheck_3795_;
                                                                    state = 14;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_snd_3716_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_3712_,
                                                                    );
                                                                    v___x_3718_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_3719_ =
                                                                        v_isSharedCheck_3795_;
                                                                    state = 14;
                                                                    continue;
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref_known(
                                                                    v_pre_3714_,
                                                                    2,
                                                                );
                                                                leanh::lean_dec_ref_known(
                                                                    v_fst_3713_,
                                                                    2,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v___x_3712_,
                                                                );
                                                                leanh::lean_dec(v___x_3711_);
                                                                leanh::lean_del_object(
                                                                    v___x_3651_,
                                                                );
                                                                leanh::lean_del_object(
                                                                    v___x_3586_,
                                                                );
                                                                state = 11;
                                                                continue;
                                                            }
                                                        } else {
                                                            leanh::lean_dec(v_pre_3714_);
                                                            leanh::lean_dec_ref_known(
                                                                v_fst_3713_,
                                                                2,
                                                            );
                                                            leanh::lean_dec_ref(v___x_3712_);
                                                            leanh::lean_dec(v___x_3711_);
                                                            leanh::lean_del_object(
                                                                v___x_3651_,
                                                            );
                                                            leanh::lean_del_object(
                                                                v___x_3586_,
                                                            );
                                                            state = 11;
                                                            continue;
                                                        }
                                                    } else {
                                                        leanh::lean_dec(v_fst_3713_);
                                                        leanh::lean_dec_ref(v___x_3712_);
                                                        leanh::lean_dec(v___x_3711_);
                                                        leanh::lean_del_object(v___x_3651_);
                                                        leanh::lean_del_object(v___x_3586_);
                                                        state = 11;
                                                        continue;
                                                    }
                                                } else {
                                                    leanh::lean_dec(v_us_3706_);
                                                    leanh::lean_dec(v___x_3656_);
                                                    leanh::lean_del_object(v___x_3651_);
                                                    leanh::lean_dec(v_snd_3649_);
                                                    leanh::lean_dec(v___x_3644_);
                                                    leanh::lean_del_object(v___x_3586_);
                                                    state = 4;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec(v___x_3656_);
                                            leanh::lean_del_object(v___x_3651_);
                                            leanh::lean_dec(v_snd_3649_);
                                            leanh::lean_dec(v___x_3644_);
                                            leanh::lean_del_object(v___x_3586_);
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v___x_3656_);
                                        leanh::lean_del_object(v___x_3651_);
                                        leanh::lean_dec(v_snd_3649_);
                                        leanh::lean_dec(v___x_3644_);
                                        leanh::lean_del_object(v___x_3586_);
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___x_3656_);
                                    leanh::lean_del_object(v___x_3651_);
                                    leanh::lean_dec(v_snd_3649_);
                                    leanh::lean_dec(v___x_3644_);
                                    leanh::lean_del_object(v___x_3586_);
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_str_3654_);
                    v___x_3797_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
                    v___x_3798_ = lean_string_dec_eq(v_str_3653_, v___x_3797_);
                    leanh::lean_dec_ref(v_str_3653_);
                    if v___x_3798_ == 0 {
                        leanh::lean_dec(v___x_3656_);
                        leanh::lean_del_object(v___x_3651_);
                        leanh::lean_dec(v_snd_3649_);
                        leanh::lean_dec(v___x_3644_);
                        leanh::lean_del_object(v___x_3586_);
                        state = 4;
                        continue;
                    } else {
                        v___x_3799_ = lean_array_get_size(v_snd_3649_);
                        v___x_3800_ = lean_nat_dec_eq(v___x_3799_, v___x_3641_);
                        if v___x_3800_ == 0 {
                            leanh::lean_dec(v___x_3656_);
                            leanh::lean_del_object(v___x_3651_);
                            leanh::lean_dec(v_snd_3649_);
                            leanh::lean_dec(v___x_3644_);
                            leanh::lean_del_object(v___x_3586_);
                            state = 4;
                            continue;
                        } else {
                            v___x_3801_ = lean_array_fget(v_snd_3649_, v___x_3655_);
                            leanh::lean_inc(v___x_3801_);
                            v___x_3802_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_3801_);
                            if leanh::lean_obj_tag(v___x_3802_) == 0 {
                                leanh::lean_dec(v___x_3801_);
                                leanh::lean_dec(v___x_3656_);
                                leanh::lean_del_object(v___x_3651_);
                                leanh::lean_dec(v_snd_3649_);
                                leanh::lean_dec(v___x_3644_);
                                leanh::lean_del_object(v___x_3586_);
                                state = 2;
                                continue;
                            } else {
                                v_val_3803_ = leanh::lean_ctor_get(v___x_3802_, 0);
                                leanh::lean_inc(v_val_3803_);
                                leanh::lean_dec_ref_known(v___x_3802_, 1);
                                v___x_3804_ = leanh::lean_unsigned_to_nat(0);
                                v___x_3805_ = lean_nat_dec_eq(v_val_3803_, v___x_3804_);
                                leanh::lean_dec(v_val_3803_);
                                if v___x_3805_ == 0 {
                                    v___x_3806_ = lean_array_fget(v_snd_3649_, v___x_3643_);
                                    leanh::lean_dec(v_snd_3649_);
                                    v___x_3807_ = leanh::lean_box(0);
                                    v___x_3808_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51);
                                    v___x_3809_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once), _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
                                    v___x_3810_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54);
                                    v___x_3845_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
                                    if v___x_3845_ == 0 {
                                        v___x_3846_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
                                        v___y_3812_ = v___x_3846_;
                                        state = 23;
                                        continue;
                                    } else {
                                        v___x_3847_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
                                        v___y_3812_ = v___x_3847_;
                                        state = 23;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___x_3801_);
                                    leanh::lean_dec(v___x_3656_);
                                    leanh::lean_del_object(v___x_3651_);
                                    leanh::lean_dec(v_snd_3649_);
                                    leanh::lean_dec(v___x_3644_);
                                    leanh::lean_del_object(v___x_3586_);
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
                v_fst_3659_ = leanh::lean_ctor_get(v___x_3658_, 0);
                leanh::lean_inc(v_fst_3659_);
                if leanh::lean_obj_tag(v_fst_3659_) == 1 {
                    v_pre_3660_ = leanh::lean_ctor_get(v_fst_3659_, 0);
                    leanh::lean_inc(v_pre_3660_);
                    if leanh::lean_obj_tag(v_pre_3660_) == 1 {
                        v_pre_3661_ = leanh::lean_ctor_get(v_pre_3660_, 0);
                        if leanh::lean_obj_tag(v_pre_3661_) == 0 {
                            v_snd_3662_ = leanh::lean_ctor_get(v___x_3658_, 1);
                            v_isSharedCheck_3692_ =
                                (!leanh::lean_is_exclusive(v___x_3658_)) as u8;
                            if v_isSharedCheck_3692_ == 0 {
                                v_unused_3693_ = leanh::lean_ctor_get(v___x_3658_, 0);
                                leanh::lean_dec(v_unused_3693_);
                                v___x_3664_ = v___x_3658_;
                                v_isShared_3665_ = v_isSharedCheck_3692_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_3662_);
                                leanh::lean_dec(v___x_3658_);
                                v___x_3664_ = leanh::lean_box(0);
                                v_isShared_3665_ = v_isSharedCheck_3692_;
                                state = 12;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_pre_3660_, 2);
                            leanh::lean_dec_ref_known(v_fst_3659_, 2);
                            leanh::lean_dec_ref(v___x_3658_);
                            leanh::lean_dec(v___x_3644_);
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_fst_3659_, 2);
                        leanh::lean_dec(v_pre_3660_);
                        leanh::lean_dec_ref(v___x_3658_);
                        leanh::lean_dec(v___x_3644_);
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_3659_);
                    leanh::lean_dec_ref(v___x_3658_);
                    leanh::lean_dec(v___x_3644_);
                    state = 5;
                    continue;
                }
            }
            12 => {
                v_str_3666_ = leanh::lean_ctor_get(v_fst_3659_, 1);
                leanh::lean_inc_ref(v_str_3666_);
                leanh::lean_dec_ref_known(v_fst_3659_, 2);
                v_str_3667_ = leanh::lean_ctor_get(v_pre_3660_, 1);
                leanh::lean_inc_ref(v_str_3667_);
                leanh::lean_dec_ref_known(v_pre_3660_, 2);
                v___x_3668_ = lean_string_dec_eq(v_str_3667_, v___x_3590_);
                leanh::lean_dec_ref(v_str_3667_);
                if v___x_3668_ == 0 {
                    leanh::lean_dec_ref(v_str_3666_);
                    leanh::lean_del_object(v___x_3664_);
                    leanh::lean_dec(v_snd_3662_);
                    leanh::lean_dec(v___x_3644_);
                    state = 5;
                    continue;
                } else {
                    v___x_3669_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                    v___x_3670_ = lean_string_dec_eq(v_str_3666_, v___x_3669_);
                    leanh::lean_dec_ref(v_str_3666_);
                    if v___x_3670_ == 0 {
                        leanh::lean_del_object(v___x_3664_);
                        leanh::lean_dec(v_snd_3662_);
                        leanh::lean_dec(v___x_3644_);
                        state = 5;
                        continue;
                    } else {
                        v___x_3671_ = lean_array_get_size(v_snd_3662_);
                        v___x_3672_ = leanh::lean_unsigned_to_nat(3);
                        v___x_3673_ = lean_nat_dec_eq(v___x_3671_, v___x_3672_);
                        if v___x_3673_ == 0 {
                            leanh::lean_del_object(v___x_3664_);
                            leanh::lean_dec(v_snd_3662_);
                            leanh::lean_dec(v___x_3644_);
                            state = 5;
                            continue;
                        } else {
                            v___x_3674_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3675_ = lean_array_fget_borrowed(v_snd_3662_, v___x_3674_);
                            if leanh::lean_obj_tag(v___x_3675_) == 4 {
                                v_declName_3676_ = leanh::lean_ctor_get(v___x_3675_, 0);
                                if leanh::lean_obj_tag(v_declName_3676_) == 1 {
                                    v_pre_3677_ = leanh::lean_ctor_get(v_declName_3676_, 0);
                                    if leanh::lean_obj_tag(v_pre_3677_) == 0 {
                                        v_us_3678_ = leanh::lean_ctor_get(v___x_3675_, 1);
                                        leanh::lean_inc(v_us_3678_);
                                        v_str_3679_ =
                                            leanh::lean_ctor_get(v_declName_3676_, 1);
                                        v___x_3680_ =
                                            l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
                                        v___x_3681_ = lean_string_dec_eq(v_str_3679_, v___x_3680_);
                                        if v___x_3681_ == 0 {
                                            leanh::lean_dec(v_us_3678_);
                                            leanh::lean_del_object(v___x_3664_);
                                            leanh::lean_dec(v_snd_3662_);
                                            leanh::lean_dec(v___x_3644_);
                                            state = 5;
                                            continue;
                                        } else {
                                            if leanh::lean_obj_tag(v_us_3678_) == 0 {
                                                v___x_3682_ = leanh::lean_unsigned_to_nat(2);
                                                v___x_3683_ =
                                                    lean_array_fget(v_snd_3662_, v___x_3682_);
                                                leanh::lean_dec(v_snd_3662_);
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
                                                v___x_3687_ = leanh::lean_box(0);
                                                if v_isShared_3665_ == 0 {
                                                    leanh::lean_ctor_set_tag(v___x_3664_, 1);
                                                    leanh::lean_ctor_set(
                                                        v___x_3664_,
                                                        1,
                                                        v___x_3687_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3664_,
                                                        0,
                                                        v___x_3686_,
                                                    );
                                                    v___x_3689_ = v___x_3664_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3691_ =
                                                        leanh::lean_alloc_ctor(
                                                            1,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                    leanh::lean_ctor_set(
                                                        v_reuseFailAlloc_3691_,
                                                        0,
                                                        v___x_3686_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v_reuseFailAlloc_3691_,
                                                        1,
                                                        v___x_3687_,
                                                    );
                                                    v___x_3689_ = v_reuseFailAlloc_3691_;
                                                    state = 13;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec(v_us_3678_);
                                                leanh::lean_del_object(v___x_3664_);
                                                leanh::lean_dec(v_snd_3662_);
                                                leanh::lean_dec(v___x_3644_);
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_del_object(v___x_3664_);
                                        leanh::lean_dec(v_snd_3662_);
                                        leanh::lean_dec(v___x_3644_);
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_3664_);
                                    leanh::lean_dec(v_snd_3662_);
                                    leanh::lean_dec(v___x_3644_);
                                    state = 5;
                                    continue;
                                }
                            } else {
                                leanh::lean_del_object(v___x_3664_);
                                leanh::lean_dec(v_snd_3662_);
                                leanh::lean_dec(v___x_3644_);
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            13 => {
                v___x_3690_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3690_, 0, v___x_3689_);
                return v___x_3690_;
            }
            14 => {
                v_str_3720_ = leanh::lean_ctor_get(v_fst_3713_, 1);
                leanh::lean_inc_ref(v_str_3720_);
                leanh::lean_dec_ref_known(v_fst_3713_, 2);
                v_str_3721_ = leanh::lean_ctor_get(v_pre_3714_, 1);
                leanh::lean_inc_ref(v_str_3721_);
                leanh::lean_dec_ref_known(v_pre_3714_, 2);
                v___x_3722_ = lean_string_dec_eq(v_str_3721_, v___x_3694_);
                leanh::lean_dec_ref(v_str_3721_);
                if v___x_3722_ == 0 {
                    leanh::lean_dec_ref(v_str_3720_);
                    leanh::lean_del_object(v___x_3718_);
                    leanh::lean_dec(v_snd_3716_);
                    leanh::lean_dec(v___x_3711_);
                    leanh::lean_del_object(v___x_3651_);
                    leanh::lean_del_object(v___x_3586_);
                    state = 11;
                    continue;
                } else {
                    v___x_3723_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
                    v___x_3724_ = lean_string_dec_eq(v_str_3720_, v___x_3723_);
                    leanh::lean_dec_ref(v_str_3720_);
                    if v___x_3724_ == 0 {
                        leanh::lean_del_object(v___x_3718_);
                        leanh::lean_dec(v_snd_3716_);
                        leanh::lean_dec(v___x_3711_);
                        leanh::lean_del_object(v___x_3651_);
                        leanh::lean_del_object(v___x_3586_);
                        state = 11;
                        continue;
                    } else {
                        v___x_3725_ = lean_array_get_size(v_snd_3716_);
                        v___x_3726_ = lean_nat_dec_eq(v___x_3725_, v___x_3641_);
                        if v___x_3726_ == 0 {
                            leanh::lean_del_object(v___x_3718_);
                            leanh::lean_dec(v_snd_3716_);
                            leanh::lean_dec(v___x_3711_);
                            leanh::lean_del_object(v___x_3651_);
                            leanh::lean_del_object(v___x_3586_);
                            state = 11;
                            continue;
                        } else {
                            v___x_3727_ = lean_array_fget(v_snd_3716_, v___x_3655_);
                            leanh::lean_inc(v___x_3727_);
                            v___x_3728_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_3727_);
                            if leanh::lean_obj_tag(v___x_3728_) == 0 {
                                leanh::lean_dec(v___x_3727_);
                                leanh::lean_del_object(v___x_3718_);
                                leanh::lean_dec(v_snd_3716_);
                                leanh::lean_dec(v___x_3711_);
                                leanh::lean_dec(v___x_3656_);
                                leanh::lean_del_object(v___x_3651_);
                                leanh::lean_dec(v___x_3644_);
                                leanh::lean_del_object(v___x_3586_);
                                state = 6;
                                continue;
                            } else {
                                v_val_3729_ = leanh::lean_ctor_get(v___x_3728_, 0);
                                leanh::lean_inc(v_val_3729_);
                                leanh::lean_dec_ref_known(v___x_3728_, 1);
                                v___x_3730_ = lean_nat_dec_eq(v_val_3729_, v___x_3702_);
                                leanh::lean_dec(v_val_3729_);
                                if v___x_3730_ == 0 {
                                    v___x_3731_ =
                                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22;
                                    v___x_3732_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23);
                                    if v_isShared_3719_ == 0 {
                                        leanh::lean_ctor_set_tag(v___x_3718_, 1);
                                        leanh::lean_ctor_set(v___x_3718_, 1, v_us_3706_);
                                        leanh::lean_ctor_set(v___x_3718_, 0, v___x_3732_);
                                        v___x_3734_ = v___x_3718_;
                                        state = 15;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3794_ =
                                            leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3794_,
                                            0,
                                            v___x_3732_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3794_,
                                            1,
                                            v_us_3706_,
                                        );
                                        v___x_3734_ = v_reuseFailAlloc_3794_;
                                        state = 15;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___x_3727_);
                                    leanh::lean_del_object(v___x_3718_);
                                    leanh::lean_dec(v_snd_3716_);
                                    leanh::lean_dec(v___x_3711_);
                                    leanh::lean_dec(v___x_3656_);
                                    leanh::lean_del_object(v___x_3651_);
                                    leanh::lean_dec(v___x_3644_);
                                    leanh::lean_del_object(v___x_3586_);
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            15 => {
                leanh::lean_inc_ref(v___x_3734_);
                v___x_3735_ = l_Lean_Expr_const___override(v___x_3731_, v___x_3734_);
                v___x_3736_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24;
                v___x_3737_ = l_Lean_Expr_const___override(v___x_3736_, v_us_3706_);
                v___x_3738_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26;
                v___x_3739_ = l_Lean_Expr_const___override(v___x_3738_, v_us_3706_);
                v___x_3740_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27,
                );
                leanh::lean_inc(v___x_3727_);
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
                if leanh::lean_obj_tag(v___x_3742_) == 0 {
                    v_a_3743_ = leanh::lean_ctor_get(v___x_3742_, 0);
                    v_isSharedCheck_3785_ = (!leanh::lean_is_exclusive(v___x_3742_)) as u8;
                    if v_isSharedCheck_3785_ == 0 {
                        v___x_3745_ = v___x_3742_;
                        v_isShared_3746_ = v_isSharedCheck_3785_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3743_);
                        leanh::lean_dec(v___x_3742_);
                        v___x_3745_ = leanh::lean_box(0);
                        v_isShared_3746_ = v_isSharedCheck_3785_;
                        state = 16;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3734_);
                    leanh::lean_dec(v___x_3727_);
                    leanh::lean_dec(v_snd_3716_);
                    leanh::lean_dec(v___x_3711_);
                    leanh::lean_dec(v___x_3656_);
                    leanh::lean_del_object(v___x_3651_);
                    leanh::lean_dec(v___x_3644_);
                    leanh::lean_del_object(v___x_3586_);
                    v_a_3786_ = leanh::lean_ctor_get(v___x_3742_, 0);
                    v_isSharedCheck_3793_ = (!leanh::lean_is_exclusive(v___x_3742_)) as u8;
                    if v_isSharedCheck_3793_ == 0 {
                        v___x_3788_ = v___x_3742_;
                        v_isShared_3789_ = v_isSharedCheck_3793_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3786_);
                        leanh::lean_dec(v___x_3742_);
                        v___x_3788_ = leanh::lean_box(0);
                        v_isShared_3789_ = v_isSharedCheck_3793_;
                        state = 21;
                        continue;
                    }
                }
            }
            16 => {
                v___x_3747_ = lean_array_fget(v_snd_3716_, v___x_3643_);
                leanh::lean_dec(v_snd_3716_);
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
                v___x_3775_ = leanh::lean_uint8_once(
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
                    v___x_3782_ = leanh::lean_obj_once(
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
                    leanh::lean_dec_ref(v___x_3734_);
                    v___x_3784_ = leanh::lean_obj_once(
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
                leanh::lean_inc_ref(v___x_3753_);
                leanh::lean_inc_n(v___x_3644_, 2);
                v___x_3760_ = l_Lean_mkApp3(v___x_3757_, v___x_3644_, v___y_3759_, v___x_3753_);
                leanh::lean_inc(v___x_3656_);
                v___x_3761_ = l_Lean_mkApp3(v___x_3755_, v___x_3656_, v___x_3644_, v___x_3760_);
                v___x_3762_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37;
                v___x_3763_ = l_Lean_Expr_const___override(v___x_3762_, v_us_3706_);
                v___x_3764_ = l_Lean_mkApp3(v___x_3763_, v___x_3656_, v___x_3644_, v___x_3753_);
                v___x_3765_ = leanh::lean_box(0);
                if v_isShared_3652_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3651_, 1);
                    leanh::lean_ctor_set(v___x_3651_, 1, v___x_3765_);
                    leanh::lean_ctor_set(v___x_3651_, 0, v___x_3764_);
                    v___x_3767_ = v___x_3651_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3774_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3764_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 1, v___x_3765_);
                    v___x_3767_ = v_reuseFailAlloc_3774_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3587_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3586_, 1);
                    leanh::lean_ctor_set(v___x_3586_, 1, v___x_3767_);
                    leanh::lean_ctor_set(v___x_3586_, 0, v___x_3761_);
                    v___x_3769_ = v___x_3586_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3773_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3761_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3773_, 1, v___x_3767_);
                    v___x_3769_ = v_reuseFailAlloc_3773_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3746_ == 0 {
                    leanh::lean_ctor_set(v___x_3745_, 0, v___x_3769_);
                    v___x_3771_ = v___x_3745_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3772_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3769_);
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
                    v_reuseFailAlloc_3792_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
                    v___x_3791_ = v_reuseFailAlloc_3792_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3791_;
            }
            23 => {
                leanh::lean_inc(v___x_3801_);
                leanh::lean_inc_ref(v___y_3812_);
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
                if leanh::lean_obj_tag(v___x_3814_) == 0 {
                    v_a_3815_ = leanh::lean_ctor_get(v___x_3814_, 0);
                    v_isSharedCheck_3836_ = (!leanh::lean_is_exclusive(v___x_3814_)) as u8;
                    if v_isSharedCheck_3836_ == 0 {
                        v___x_3817_ = v___x_3814_;
                        v_isShared_3818_ = v_isSharedCheck_3836_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3815_);
                        leanh::lean_dec(v___x_3814_);
                        v___x_3817_ = leanh::lean_box(0);
                        v_isShared_3818_ = v_isSharedCheck_3836_;
                        state = 24;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3806_);
                    leanh::lean_dec(v___x_3801_);
                    leanh::lean_dec(v___x_3656_);
                    leanh::lean_del_object(v___x_3651_);
                    leanh::lean_dec(v___x_3644_);
                    leanh::lean_del_object(v___x_3586_);
                    v_a_3837_ = leanh::lean_ctor_get(v___x_3814_, 0);
                    v_isSharedCheck_3844_ = (!leanh::lean_is_exclusive(v___x_3814_)) as u8;
                    if v_isSharedCheck_3844_ == 0 {
                        v___x_3839_ = v___x_3814_;
                        v_isShared_3840_ = v_isSharedCheck_3844_;
                        state = 28;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3837_);
                        leanh::lean_dec(v___x_3814_);
                        v___x_3839_ = leanh::lean_box(0);
                        v_isShared_3840_ = v_isSharedCheck_3844_;
                        state = 28;
                        continue;
                    }
                }
            }
            24 => {
                v___x_3819_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57,
                );
                v___x_3820_ = l_Lean_mkApp3(v___x_3819_, v___x_3801_, v___x_3806_, v_a_3815_);
                v___x_3821_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58,
                );
                v___x_3822_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59,
                );
                leanh::lean_inc_ref(v___x_3820_);
                leanh::lean_inc_ref(v___y_3812_);
                leanh::lean_inc_n(v___x_3644_, 2);
                v___x_3823_ = l_Lean_mkApp3(v___x_3822_, v___x_3644_, v___y_3812_, v___x_3820_);
                leanh::lean_inc(v___x_3656_);
                v___x_3824_ = l_Lean_mkApp3(v___x_3821_, v___x_3656_, v___x_3644_, v___x_3823_);
                v___x_3825_ = leanh::lean_obj_once(
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
                    leanh::lean_ctor_set_tag(v___x_3651_, 1);
                    leanh::lean_ctor_set(v___x_3651_, 1, v___x_3807_);
                    leanh::lean_ctor_set(v___x_3651_, 0, v___x_3826_);
                    v___x_3828_ = v___x_3651_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3835_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3826_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3835_, 1, v___x_3807_);
                    v___x_3828_ = v_reuseFailAlloc_3835_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_3587_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3586_, 1);
                    leanh::lean_ctor_set(v___x_3586_, 1, v___x_3828_);
                    leanh::lean_ctor_set(v___x_3586_, 0, v___x_3824_);
                    v___x_3830_ = v___x_3586_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3834_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3824_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 1, v___x_3828_);
                    v___x_3830_ = v_reuseFailAlloc_3834_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_3818_ == 0 {
                    leanh::lean_ctor_set(v___x_3817_, 0, v___x_3830_);
                    v___x_3832_ = v___x_3817_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3833_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3830_);
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
                    v_reuseFailAlloc_3843_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
                    v___x_3842_ = v_reuseFailAlloc_3843_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3842_;
            }
            30 => {
                leanh::lean_inc_ref(v___y_3867_);
                leanh::lean_inc(v___x_3856_);
                v_ne__zero_3868_ =
                    l_Lean_mkApp3(v___x_3864_, v___x_3865_, v___x_3856_, v___y_3867_);
                v___x_3869_ = l_Lean_Meta_mkDecideProof(
                    v_ne__zero_3868_,
                    v_a_3557_,
                    v_a_3558_,
                    v_a_3559_,
                    v_a_3560_,
                );
                if leanh::lean_obj_tag(v___x_3869_) == 0 {
                    v_a_3870_ = leanh::lean_ctor_get(v___x_3869_, 0);
                    leanh::lean_inc(v_a_3870_);
                    leanh::lean_dec_ref_known(v___x_3869_, 1);
                    v___x_3871_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once
                        ),
                        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51,
                    );
                    v___x_3872_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once
                        ),
                        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54,
                    );
                    leanh::lean_inc(v___x_3856_);
                    leanh::lean_inc_ref(v___y_3867_);
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
                    if leanh::lean_obj_tag(v___x_3874_) == 0 {
                        v_a_3875_ = leanh::lean_ctor_get(v___x_3874_, 0);
                        v_isSharedCheck_3890_ =
                            (!leanh::lean_is_exclusive(v___x_3874_)) as u8;
                        if v_isSharedCheck_3890_ == 0 {
                            v___x_3877_ = v___x_3874_;
                            v_isShared_3878_ = v_isSharedCheck_3890_;
                            state = 31;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3875_);
                            leanh::lean_dec(v___x_3874_);
                            v___x_3877_ = leanh::lean_box(0);
                            v_isShared_3878_ = v_isSharedCheck_3890_;
                            state = 31;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3870_);
                        leanh::lean_dec(v___x_3862_);
                        leanh::lean_dec(v___x_3856_);
                        leanh::lean_del_object(v___x_3586_);
                        v_a_3891_ = leanh::lean_ctor_get(v___x_3874_, 0);
                        v_isSharedCheck_3898_ =
                            (!leanh::lean_is_exclusive(v___x_3874_)) as u8;
                        if v_isSharedCheck_3898_ == 0 {
                            v___x_3893_ = v___x_3874_;
                            v_isShared_3894_ = v_isSharedCheck_3898_;
                            state = 34;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3891_);
                            leanh::lean_dec(v___x_3874_);
                            v___x_3893_ = leanh::lean_box(0);
                            v_isShared_3894_ = v_isSharedCheck_3898_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_3862_);
                    leanh::lean_dec(v___x_3856_);
                    leanh::lean_del_object(v___x_3586_);
                    v_a_3899_ = leanh::lean_ctor_get(v___x_3869_, 0);
                    v_isSharedCheck_3906_ = (!leanh::lean_is_exclusive(v___x_3869_)) as u8;
                    if v_isSharedCheck_3906_ == 0 {
                        v___x_3901_ = v___x_3869_;
                        v_isShared_3902_ = v_isSharedCheck_3906_;
                        state = 36;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3899_);
                        leanh::lean_dec(v___x_3869_);
                        v___x_3901_ = leanh::lean_box(0);
                        v_isShared_3902_ = v_isSharedCheck_3906_;
                        state = 36;
                        continue;
                    }
                }
            }
            31 => {
                v___x_3879_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71,
                );
                leanh::lean_inc(v___x_3856_);
                leanh::lean_inc(v___x_3862_);
                v___x_3880_ = l_Lean_mkApp3(v___x_3879_, v___x_3862_, v___x_3856_, v_a_3870_);
                v___x_3881_ = leanh::lean_obj_once(
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
                    leanh::lean_ctor_set_tag(v___x_3586_, 1);
                    leanh::lean_ctor_set(v___x_3586_, 1, v___x_3863_);
                    leanh::lean_ctor_set(v___x_3586_, 0, v___x_3882_);
                    v___x_3884_ = v___x_3586_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3889_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3882_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3889_, 1, v___x_3863_);
                    v___x_3884_ = v_reuseFailAlloc_3889_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_3885_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3885_, 0, v___x_3880_);
                leanh::lean_ctor_set(v___x_3885_, 1, v___x_3884_);
                if v_isShared_3878_ == 0 {
                    leanh::lean_ctor_set(v___x_3877_, 0, v___x_3885_);
                    v___x_3887_ = v___x_3877_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3888_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3885_);
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
                    v_reuseFailAlloc_3897_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
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
                    v_reuseFailAlloc_3905_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
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
                        leanh::lean_ctor_set_tag(v___x_3586_, 1);
                        leanh::lean_ctor_set(v___x_3586_, 1, v___y_3924_);
                        leanh::lean_ctor_set(v___x_3586_, 0, v___x_3927_);
                        v___x_3930_ = v___x_3586_;
                        state = 39;
                        continue;
                    } else {
                        v_reuseFailAlloc_3932_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3927_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 1, v___y_3924_);
                        v___x_3930_ = v_reuseFailAlloc_3932_;
                        state = 39;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3927_);
                    leanh::lean_del_object(v___x_3586_);
                    v___x_3933_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3933_, 0, v___y_3924_);
                    return v___x_3933_;
                }
            }
            39 => {
                v___x_3931_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3931_, 0, v___x_3930_);
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
                    v___x_3950_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3950_, 0, v___x_3948_);
                    leanh::lean_ctor_set(v___x_3950_, 1, v_r_3942_);
                    v___x_3951_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3951_, 0, v___x_3950_);
                    return v___x_3951_;
                } else {
                    leanh::lean_dec_ref(v___x_3948_);
                    v___x_3952_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3952_, 0, v_r_3942_);
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
                    v___x_3960_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3960_, 0, v___x_3958_);
                    leanh::lean_ctor_set(v___x_3960_, 1, v_r_3942_);
                    v___x_3961_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_3960_);
                    return v___x_3961_;
                } else {
                    leanh::lean_dec_ref(v___x_3958_);
                    v___x_3962_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3962_, 0, v_r_3942_);
                    return v___x_3962_;
                }
            }
            42 => {
                v___x_3965_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85;
                v___x_3966_ = l_Lean_Expr_const___override(v___x_3965_, v_us_3919_);
                leanh::lean_inc_ref(v_x_3964_);
                v___x_3967_ = l_Lean_Expr_app___override(v___x_3966_, v_x_3964_);
                v___x_3968_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(
                    v___x_3967_,
                    v_r_3942_,
                );
                if v___x_3968_ == 0 {
                    v___x_3969_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3969_, 0, v___x_3967_);
                    leanh::lean_ctor_set(v___x_3969_, 1, v_r_3942_);
                    v___y_3923_ = v_x_3964_;
                    v___y_3924_ = v___x_3969_;
                    state = 38;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___x_3967_);
                    v___y_3923_ = v_x_3964_;
                    v___y_3924_ = v_r_3942_;
                    state = 38;
                    continue;
                }
            }
            43 => {
                v_str_3978_ = leanh::lean_ctor_get(v_fst_3971_, 1);
                leanh::lean_inc_ref(v_str_3978_);
                leanh::lean_dec_ref_known(v_fst_3971_, 2);
                v_str_3979_ = leanh::lean_ctor_get(v_pre_3972_, 1);
                leanh::lean_inc_ref(v_str_3979_);
                leanh::lean_dec_ref_known(v_pre_3972_, 2);
                v___x_3980_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
                v___x_3981_ = lean_string_dec_eq(v_str_3979_, v___x_3980_);
                if v___x_3981_ == 0 {
                    leanh::lean_del_object(v___x_3976_);
                    v___x_3982_ = lean_string_dec_eq(v_str_3979_, v___x_3921_);
                    if v___x_3982_ == 0 {
                        leanh::lean_del_object(v___x_3586_);
                        v___x_3983_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82;
                        v___x_3984_ = lean_string_dec_eq(v_str_3979_, v___x_3983_);
                        if v___x_3984_ == 0 {
                            v___x_3985_ =
                                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79;
                            v___x_3986_ = lean_string_dec_eq(v_str_3979_, v___x_3985_);
                            leanh::lean_dec_ref(v_str_3979_);
                            if v___x_3986_ == 0 {
                                leanh::lean_dec_ref(v_str_3978_);
                                leanh::lean_dec(v_snd_3974_);
                                v___x_3987_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3987_, 0, v_r_3942_);
                                return v___x_3987_;
                            } else {
                                v___x_3988_ =
                                    l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86;
                                v___x_3989_ = lean_string_dec_eq(v_str_3978_, v___x_3988_);
                                leanh::lean_dec_ref(v_str_3978_);
                                if v___x_3989_ == 0 {
                                    leanh::lean_dec(v_snd_3974_);
                                    v___x_3990_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3990_, 0, v_r_3942_);
                                    return v___x_3990_;
                                } else {
                                    v___x_3991_ = lean_array_get_size(v_snd_3974_);
                                    v___x_3992_ = lean_nat_dec_eq(v___x_3991_, v___x_3936_);
                                    if v___x_3992_ == 0 {
                                        leanh::lean_dec(v_snd_3974_);
                                        v___x_3993_ =
                                            leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3993_, 0, v_r_3942_);
                                        return v___x_3993_;
                                    } else {
                                        v___x_3994_ = lean_array_fget(v_snd_3974_, v___x_3915_);
                                        v___x_3995_ = leanh::lean_unsigned_to_nat(1);
                                        v___x_3996_ = lean_array_fget(v_snd_3974_, v___x_3995_);
                                        leanh::lean_dec(v_snd_3974_);
                                        v_n_3944_ = v___x_3994_;
                                        v_x_3945_ = v___x_3996_;
                                        state = 40;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_str_3979_);
                            v___x_3997_ =
                                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87;
                            v___x_3998_ = lean_string_dec_eq(v_str_3978_, v___x_3997_);
                            leanh::lean_dec_ref(v_str_3978_);
                            if v___x_3998_ == 0 {
                                leanh::lean_dec(v_snd_3974_);
                                v___x_3999_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3999_, 0, v_r_3942_);
                                return v___x_3999_;
                            } else {
                                v___x_4000_ = lean_array_get_size(v_snd_3974_);
                                v___x_4001_ = lean_nat_dec_eq(v___x_4000_, v___x_3936_);
                                if v___x_4001_ == 0 {
                                    leanh::lean_dec(v_snd_3974_);
                                    v___x_4002_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4002_, 0, v_r_3942_);
                                    return v___x_4002_;
                                } else {
                                    v___x_4003_ = lean_array_fget(v_snd_3974_, v___x_3915_);
                                    v___x_4004_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_4005_ = lean_array_fget(v_snd_3974_, v___x_4004_);
                                    leanh::lean_dec(v_snd_3974_);
                                    v_n_3954_ = v___x_4003_;
                                    v_i_3955_ = v___x_4005_;
                                    state = 41;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_str_3979_);
                        v___x_4006_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88;
                        v___x_4007_ = lean_string_dec_eq(v_str_3978_, v___x_4006_);
                        leanh::lean_dec_ref(v_str_3978_);
                        if v___x_4007_ == 0 {
                            leanh::lean_dec(v_snd_3974_);
                            leanh::lean_del_object(v___x_3586_);
                            v___x_4008_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4008_, 0, v_r_3942_);
                            return v___x_4008_;
                        } else {
                            v___x_4009_ = lean_array_get_size(v_snd_3974_);
                            v___x_4010_ = leanh::lean_unsigned_to_nat(1);
                            v___x_4011_ = lean_nat_dec_eq(v___x_4009_, v___x_4010_);
                            if v___x_4011_ == 0 {
                                leanh::lean_dec(v_snd_3974_);
                                leanh::lean_del_object(v___x_3586_);
                                v___x_4012_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4012_, 0, v_r_3942_);
                                return v___x_4012_;
                            } else {
                                v___x_4013_ = lean_array_fget(v_snd_3974_, v___x_3915_);
                                leanh::lean_dec(v_snd_3974_);
                                v_x_3964_ = v___x_4013_;
                                state = 42;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_str_3979_);
                    leanh::lean_del_object(v___x_3586_);
                    v___x_4014_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
                    v___x_4015_ = lean_string_dec_eq(v_str_3978_, v___x_4014_);
                    leanh::lean_dec_ref(v_str_3978_);
                    if v___x_4015_ == 0 {
                        leanh::lean_del_object(v___x_3976_);
                        leanh::lean_dec(v_snd_3974_);
                        v___x_4016_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4016_, 0, v_r_3942_);
                        return v___x_4016_;
                    } else {
                        v___x_4017_ = lean_array_get_size(v_snd_3974_);
                        v___x_4018_ = leanh::lean_unsigned_to_nat(6);
                        v___x_4019_ = lean_nat_dec_eq(v___x_4017_, v___x_4018_);
                        if v___x_4019_ == 0 {
                            leanh::lean_del_object(v___x_3976_);
                            leanh::lean_dec(v_snd_3974_);
                            v___x_4020_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4020_, 0, v_r_3942_);
                            return v___x_4020_;
                        } else {
                            v___x_4021_ = leanh::lean_unsigned_to_nat(4);
                            v___x_4022_ = lean_array_fget(v_snd_3974_, v___x_4021_);
                            v___x_4023_ = leanh::lean_unsigned_to_nat(5);
                            v___x_4024_ = lean_array_fget(v_snd_3974_, v___x_4023_);
                            leanh::lean_dec(v_snd_3974_);
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
                                    leanh::lean_ctor_set_tag(v___x_3976_, 1);
                                    leanh::lean_ctor_set(v___x_3976_, 1, v_r_3942_);
                                    leanh::lean_ctor_set(v___x_3976_, 0, v___x_4027_);
                                    v___x_4030_ = v___x_3976_;
                                    state = 44;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4032_ =
                                        leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4032_,
                                        0,
                                        v___x_4027_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4032_,
                                        1,
                                        v_r_3942_,
                                    );
                                    v___x_4030_ = v_reuseFailAlloc_4032_;
                                    state = 44;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_4027_);
                                leanh::lean_del_object(v___x_3976_);
                                v___x_4033_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4033_, 0, v_r_3942_);
                                return v___x_4033_;
                            }
                        }
                    }
                }
            }
            44 => {
                v___x_4031_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4031_, 0, v___x_4030_);
                return v___x_4031_;
            }
            45 => {
                v_str_4087_ = leanh::lean_ctor_get(v_fst_3581_, 1);
                leanh::lean_inc_ref(v_str_4087_);
                leanh::lean_dec_ref_known(v_fst_3581_, 2);
                v___x_4088_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91;
                v___x_4089_ = lean_string_dec_eq(v_str_4087_, v___x_4088_);
                leanh::lean_dec_ref(v_str_4087_);
                if v___x_4089_ == 0 {
                    leanh::lean_del_object(v___x_4085_);
                    leanh::lean_dec(v_snd_4083_);
                    state = 3;
                    continue;
                } else {
                    v___x_4090_ = lean_array_get_size(v_snd_4083_);
                    v___x_4091_ = leanh::lean_unsigned_to_nat(5);
                    v___x_4092_ = lean_nat_dec_eq(v___x_4090_, v___x_4091_);
                    if v___x_4092_ == 0 {
                        leanh::lean_del_object(v___x_4085_);
                        leanh::lean_dec(v_snd_4083_);
                        state = 3;
                        continue;
                    } else {
                        v___x_4093_ = leanh::lean_unsigned_to_nat(0);
                        v___x_4094_ = lean_array_fget(v_snd_4083_, v___x_4093_);
                        v___x_4095_ = leanh::lean_box(0);
                        v___x_4096_ = leanh::lean_obj_once(
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
                            leanh::lean_dec(v___x_4094_);
                            leanh::lean_del_object(v___x_4085_);
                            leanh::lean_dec(v_snd_4083_);
                            v___x_4098_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4098_, 0, v___x_4095_);
                            return v___x_4098_;
                        } else {
                            v___x_4099_ = leanh::lean_unsigned_to_nat(1);
                            v___x_4100_ = lean_array_fget(v_snd_4083_, v___x_4099_);
                            v___x_4101_ = leanh::lean_unsigned_to_nat(2);
                            v___x_4102_ = lean_array_fget(v_snd_4083_, v___x_4101_);
                            v___x_4103_ = leanh::lean_unsigned_to_nat(3);
                            v___x_4104_ = lean_array_fget(v_snd_4083_, v___x_4103_);
                            v___x_4105_ = leanh::lean_unsigned_to_nat(4);
                            v___x_4106_ = lean_array_fget(v_snd_4083_, v___x_4105_);
                            leanh::lean_dec(v_snd_4083_);
                            v___x_4107_ = leanh::lean_obj_once(
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
                                leanh::lean_ctor_set_tag(v___x_4085_, 1);
                                leanh::lean_ctor_set(v___x_4085_, 1, v___x_4095_);
                                leanh::lean_ctor_set(v___x_4085_, 0, v___x_4108_);
                                v___x_4110_ = v___x_4085_;
                                state = 46;
                                continue;
                            } else {
                                v_reuseFailAlloc_4112_ =
                                    leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4108_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 1, v___x_4095_);
                                v___x_4110_ = v_reuseFailAlloc_4112_;
                                state = 46;
                                continue;
                            }
                        }
                    }
                }
            }
            46 => {
                v___x_4111_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4111_, 0, v___x_4110_);
                return v___x_4111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___boxed(
    mut v_e_4115_: *mut leanh::LeanObject,
    mut v_a_4116_: *mut leanh::LeanObject,
    mut v_a_4117_: *mut leanh::LeanObject,
    mut v_a_4118_: *mut leanh::LeanObject,
    mut v_a_4119_: *mut leanh::LeanObject,
    mut v_a_4120_: *mut leanh::LeanObject,
    mut v_a_4121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4122_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(
        v_e_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_,
    );
    leanh::lean_dec(v_a_4120_);
    leanh::lean_dec_ref(v_a_4119_);
    leanh::lean_dec(v_a_4118_);
    leanh::lean_dec_ref(v_a_4117_);
    leanh::lean_dec_ref(v_a_4116_);
    return v_res_4122_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_analyzeAtom(
    mut v_e_4123_: *mut leanh::LeanObject,
    mut v_a_4124_: *mut leanh::LeanObject,
    mut v_a_4125_: *mut leanh::LeanObject,
    mut v_a_4126_: *mut leanh::LeanObject,
    mut v_a_4127_: u8,
    mut v_a_4128_: *mut leanh::LeanObject,
    mut v_a_4129_: *mut leanh::LeanObject,
    mut v_a_4130_: *mut leanh::LeanObject,
    mut v_a_4131_: *mut leanh::LeanObject,
    mut v_a_4132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4134_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(
        v_e_4123_, v_a_4126_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_,
    );
    return v___x_4134_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(
    mut v_e_4135_: *mut leanh::LeanObject,
    mut v_a_4136_: *mut leanh::LeanObject,
    mut v_a_4137_: *mut leanh::LeanObject,
    mut v_a_4138_: *mut leanh::LeanObject,
    mut v_a_4139_: *mut leanh::LeanObject,
    mut v_a_4140_: *mut leanh::LeanObject,
    mut v_a_4141_: *mut leanh::LeanObject,
    mut v_a_4142_: *mut leanh::LeanObject,
    mut v_a_4143_: *mut leanh::LeanObject,
    mut v_a_4144_: *mut leanh::LeanObject,
    mut v_a_4145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_4146_: u8 = 0;
    let mut v_res_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4146_ = (leanh::lean_unbox(v_a_4139_) as u8);
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
    leanh::lean_dec(v_a_4144_);
    leanh::lean_dec_ref(v_a_4143_);
    leanh::lean_dec(v_a_4142_);
    leanh::lean_dec_ref(v_a_4141_);
    leanh::lean_dec(v_a_4140_);
    leanh::lean_dec_ref(v_a_4138_);
    leanh::lean_dec(v_a_4137_);
    leanh::lean_dec(v_a_4136_);
    return v_res_4147_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(
    mut v_a_4148_: *mut leanh::LeanObject,
    mut v_x_4149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: u8 = 0;
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4149_) == 0 {
                    v___x_4150_ = leanh::lean_box(0);
                    return v___x_4150_;
                } else {
                    v_key_4151_ = leanh::lean_ctor_get(v_x_4149_, 0);
                    v_value_4152_ = leanh::lean_ctor_get(v_x_4149_, 1);
                    v_tail_4153_ = leanh::lean_ctor_get(v_x_4149_, 2);
                    v___x_4154_ = lean_expr_eqv(v_key_4151_, v_a_4148_);
                    if v___x_4154_ == 0 {
                        v_x_4149_ = v_tail_4153_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_4152_);
                        v___x_4156_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4156_, 0, v_value_4152_);
                        return v___x_4156_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg___boxed(
    mut v_a_4157_: *mut leanh::LeanObject,
    mut v_x_4158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4159_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_4157_, v_x_4158_);
    leanh::lean_dec(v_x_4158_);
    leanh::lean_dec_ref(v_a_4157_);
    return v_res_4159_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(
    mut v_m_4160_: *mut leanh::LeanObject,
    mut v_a_4161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4162_ = leanh::lean_ctor_get(v_m_4160_, 1);
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
    mut v_m_4178_: *mut leanh::LeanObject,
    mut v_a_4179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4180_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_4178_, v_a_4179_);
    leanh::lean_dec_ref(v_a_4179_);
    leanh::lean_dec_ref(v_m_4178_);
    return v_res_4180_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(
    mut v_a_4181_: *mut leanh::LeanObject,
    mut v_x_4182_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4183_: u8 = 0;
    let mut v_key_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4182_) == 0 {
                    v___x_4183_ = 0;
                    return v___x_4183_;
                } else {
                    v_key_4184_ = leanh::lean_ctor_get(v_x_4182_, 0);
                    v_tail_4185_ = leanh::lean_ctor_get(v_x_4182_, 2);
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
    mut v_a_4188_: *mut leanh::LeanObject,
    mut v_x_4189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4190_: u8 = 0;
    let mut v_r_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_4188_, v_x_4189_);
    leanh::lean_dec(v_x_4189_);
    leanh::lean_dec_ref(v_a_4188_);
    v_r_4191_ = leanh::lean_box((v_res_4190_) as usize);
    return v_r_4191_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(
    mut v_x_4192_: *mut leanh::LeanObject,
    mut v_x_4193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4219_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4193_) == 0 {
                    return v_x_4192_;
                } else {
                    v_key_4194_ = leanh::lean_ctor_get(v_x_4193_, 0);
                    v_value_4195_ = leanh::lean_ctor_get(v_x_4193_, 1);
                    v_tail_4196_ = leanh::lean_ctor_get(v_x_4193_, 2);
                    v_isSharedCheck_4219_ = (!leanh::lean_is_exclusive(v_x_4193_)) as u8;
                    if v_isSharedCheck_4219_ == 0 {
                        v___x_4198_ = v_x_4193_;
                        v_isShared_4199_ = v_isSharedCheck_4219_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4196_);
                        leanh::lean_inc(v_value_4195_);
                        leanh::lean_inc(v_key_4194_);
                        leanh::lean_dec(v_x_4193_);
                        v___x_4198_ = leanh::lean_box(0);
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
                leanh::lean_inc(v___x_4213_);
                if v_isShared_4199_ == 0 {
                    leanh::lean_ctor_set(v___x_4198_, 2, v___x_4213_);
                    v___x_4215_ = v___x_4198_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4218_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_key_4194_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 1, v_value_4195_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 2, v___x_4213_);
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
    mut v_i_4220_: *mut leanh::LeanObject,
    mut v_source_4221_: *mut leanh::LeanObject,
    mut v_target_4222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: u8 = 0;
    let mut v_es_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4223_ = lean_array_get_size(v_source_4221_);
                v___x_4224_ = lean_nat_dec_lt(v_i_4220_, v___x_4223_);
                if v___x_4224_ == 0 {
                    leanh::lean_dec_ref(v_source_4221_);
                    leanh::lean_dec(v_i_4220_);
                    return v_target_4222_;
                } else {
                    v_es_4225_ = lean_array_fget(v_source_4221_, v_i_4220_);
                    v___x_4226_ = leanh::lean_box(0);
                    v_source_4227_ = lean_array_fset(v_source_4221_, v_i_4220_, v___x_4226_);
                    v_target_4228_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(v_target_4222_, v_es_4225_);
                    v___x_4229_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4230_ = lean_nat_add(v_i_4220_, v___x_4229_);
                    leanh::lean_dec(v_i_4220_);
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
    mut v_data_4232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4233_ = lean_array_get_size(v_data_4232_);
    v___x_4234_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4235_ = lean_nat_mul(v___x_4233_, v___x_4234_);
    v___x_4236_ = leanh::lean_unsigned_to_nat(0);
    v___x_4237_ = leanh::lean_box(0);
    v___x_4238_ = lean_mk_array(v_nbuckets_4235_, v___x_4237_);
    v___x_4239_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(v___x_4236_, v_data_4232_, v___x_4238_);
    return v___x_4239_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(
    mut v_a_4240_: *mut leanh::LeanObject,
    mut v_b_4241_: *mut leanh::LeanObject,
    mut v_x_4242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v___x_4249_: u8 = 0;
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4242_) == 0 {
                    leanh::lean_dec(v_b_4241_);
                    leanh::lean_dec_ref(v_a_4240_);
                    return v_x_4242_;
                } else {
                    v_key_4243_ = leanh::lean_ctor_get(v_x_4242_, 0);
                    v_value_4244_ = leanh::lean_ctor_get(v_x_4242_, 1);
                    v_tail_4245_ = leanh::lean_ctor_get(v_x_4242_, 2);
                    v_isSharedCheck_4257_ = (!leanh::lean_is_exclusive(v_x_4242_)) as u8;
                    if v_isSharedCheck_4257_ == 0 {
                        v___x_4247_ = v_x_4242_;
                        v_isShared_4248_ = v_isSharedCheck_4257_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4245_);
                        leanh::lean_inc(v_value_4244_);
                        leanh::lean_inc(v_key_4243_);
                        leanh::lean_dec(v_x_4242_);
                        v___x_4247_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_4247_, 2, v___x_4250_);
                        v___x_4252_ = v___x_4247_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4253_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_key_4243_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4253_, 1, v_value_4244_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4253_, 2, v___x_4250_);
                        v___x_4252_ = v_reuseFailAlloc_4253_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_4244_);
                    leanh::lean_dec(v_key_4243_);
                    if v_isShared_4248_ == 0 {
                        leanh::lean_ctor_set(v___x_4247_, 1, v_b_4241_);
                        leanh::lean_ctor_set(v___x_4247_, 0, v_a_4240_);
                        v___x_4255_ = v___x_4247_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4256_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4240_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 1, v_b_4241_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 2, v_tail_4245_);
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
    mut v_m_4258_: *mut leanh::LeanObject,
    mut v_a_4259_: *mut leanh::LeanObject,
    mut v_b_4260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4265_: u8 = 0;
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: u8 = 0;
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: u8 = 0;
    let mut v_val_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4261_ = leanh::lean_ctor_get(v_m_4258_, 0);
                v_buckets_4262_ = leanh::lean_ctor_get(v_m_4258_, 1);
                v_isSharedCheck_4305_ = (!leanh::lean_is_exclusive(v_m_4258_)) as u8;
                if v_isSharedCheck_4305_ == 0 {
                    v___x_4264_ = v_m_4258_;
                    v_isShared_4265_ = v_isSharedCheck_4305_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_4262_);
                    leanh::lean_inc(v_size_4261_);
                    leanh::lean_dec(v_m_4258_);
                    v___x_4264_ = leanh::lean_box(0);
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
                    v___x_4281_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4282_ = lean_nat_add(v_size_4261_, v___x_4281_);
                    leanh::lean_dec(v_size_4261_);
                    leanh::lean_inc(v_bkt_4279_);
                    v___x_4283_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_4283_, 0, v_a_4259_);
                    leanh::lean_ctor_set(v___x_4283_, 1, v_b_4260_);
                    leanh::lean_ctor_set(v___x_4283_, 2, v_bkt_4279_);
                    v_buckets_x27_4284_ =
                        lean_array_uset(v_buckets_4262_, v___x_4278_, v___x_4283_);
                    v___x_4285_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4286_ = lean_nat_mul(v_size_x27_4282_, v___x_4285_);
                    v___x_4287_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4288_ = lean_nat_div(v___x_4286_, v___x_4287_);
                    leanh::lean_dec(v___x_4286_);
                    v___x_4289_ = lean_array_get_size(v_buckets_x27_4284_);
                    v___x_4290_ = lean_nat_dec_le(v___x_4288_, v___x_4289_);
                    leanh::lean_dec(v___x_4288_);
                    if v___x_4290_ == 0 {
                        v_val_4291_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(v_buckets_x27_4284_);
                        if v_isShared_4265_ == 0 {
                            leanh::lean_ctor_set(v___x_4264_, 1, v_val_4291_);
                            leanh::lean_ctor_set(v___x_4264_, 0, v_size_x27_4282_);
                            v___x_4293_ = v___x_4264_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4294_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4294_,
                                0,
                                v_size_x27_4282_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_4294_, 1, v_val_4291_);
                            v___x_4293_ = v_reuseFailAlloc_4294_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_4265_ == 0 {
                            leanh::lean_ctor_set(v___x_4264_, 1, v_buckets_x27_4284_);
                            leanh::lean_ctor_set(v___x_4264_, 0, v_size_x27_4282_);
                            v___x_4296_ = v___x_4264_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4297_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4297_,
                                0,
                                v_size_x27_4282_,
                            );
                            leanh::lean_ctor_set(
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
                    leanh::lean_inc(v_bkt_4279_);
                    v___x_4298_ = leanh::lean_box(0);
                    v_buckets_x27_4299_ =
                        lean_array_uset(v_buckets_4262_, v___x_4278_, v___x_4298_);
                    v___x_4300_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_4259_, v_b_4260_, v_bkt_4279_);
                    v___x_4301_ = lean_array_uset(v_buckets_x27_4299_, v___x_4278_, v___x_4300_);
                    if v_isShared_4265_ == 0 {
                        leanh::lean_ctor_set(v___x_4264_, 1, v___x_4301_);
                        v___x_4303_ = v___x_4264_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4304_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_size_4261_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4304_, 1, v___x_4301_);
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
    mut v_msgData_4306_: *mut leanh::LeanObject,
    mut v___y_4307_: *mut leanh::LeanObject,
    mut v___y_4308_: *mut leanh::LeanObject,
    mut v___y_4309_: *mut leanh::LeanObject,
    mut v___y_4310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4312_ = lean_st_ref_get(v___y_4310_);
    v_env_4313_ = leanh::lean_ctor_get(v___x_4312_, 0);
    leanh::lean_inc_ref(v_env_4313_);
    leanh::lean_dec(v___x_4312_);
    v___x_4314_ = lean_st_ref_get(v___y_4308_);
    v_mctx_4315_ = leanh::lean_ctor_get(v___x_4314_, 0);
    leanh::lean_inc_ref(v_mctx_4315_);
    leanh::lean_dec(v___x_4314_);
    v_lctx_4316_ = leanh::lean_ctor_get(v___y_4307_, 2);
    v_options_4317_ = leanh::lean_ctor_get(v___y_4309_, 2);
    leanh::lean_inc_ref(v_options_4317_);
    leanh::lean_inc_ref(v_lctx_4316_);
    v___x_4318_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4318_, 0, v_env_4313_);
    leanh::lean_ctor_set(v___x_4318_, 1, v_mctx_4315_);
    leanh::lean_ctor_set(v___x_4318_, 2, v_lctx_4316_);
    leanh::lean_ctor_set(v___x_4318_, 3, v_options_4317_);
    v___x_4319_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4319_, 0, v___x_4318_);
    leanh::lean_ctor_set(v___x_4319_, 1, v_msgData_4306_);
    v___x_4320_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4320_, 0, v___x_4319_);
    return v___x_4320_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8___boxed(
    mut v_msgData_4321_: *mut leanh::LeanObject,
    mut v___y_4322_: *mut leanh::LeanObject,
    mut v___y_4323_: *mut leanh::LeanObject,
    mut v___y_4324_: *mut leanh::LeanObject,
    mut v___y_4325_: *mut leanh::LeanObject,
    mut v___y_4326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4327_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(v_msgData_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
    leanh::lean_dec(v___y_4325_);
    leanh::lean_dec_ref(v___y_4324_);
    leanh::lean_dec(v___y_4323_);
    leanh::lean_dec_ref(v___y_4322_);
    return v_res_4327_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0()
-> f64 {
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: f64 = 0.0;
    v___x_4328_ = leanh::lean_unsigned_to_nat(0);
    v___x_4329_ = lean_float_of_nat(v___x_4328_);
    return v___x_4329_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(
    mut v_cls_4333_: *mut leanh::LeanObject,
    mut v_msg_4334_: *mut leanh::LeanObject,
    mut v___y_4335_: *mut leanh::LeanObject,
    mut v___y_4336_: *mut leanh::LeanObject,
    mut v___y_4337_: *mut leanh::LeanObject,
    mut v___y_4338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4345_: u8 = 0;
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v_tid_4359_: u64 = 0;
    let mut v_traces_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4363_: u8 = 0;
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: f64 = 0.0;
    let mut v___x_4366_: u8 = 0;
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4384_: u8 = 0;
    let mut v_isSharedCheck_4385_: u8 = 0;
    let mut v_isSharedCheck_4386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4340_ = leanh::lean_ctor_get(v___y_4337_, 5);
                v___x_4341_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(v_msg_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
                v_a_4342_ = leanh::lean_ctor_get(v___x_4341_, 0);
                v_isSharedCheck_4386_ = (!leanh::lean_is_exclusive(v___x_4341_)) as u8;
                if v_isSharedCheck_4386_ == 0 {
                    v___x_4344_ = v___x_4341_;
                    v_isShared_4345_ = v_isSharedCheck_4386_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4342_);
                    leanh::lean_dec(v___x_4341_);
                    v___x_4344_ = leanh::lean_box(0);
                    v_isShared_4345_ = v_isSharedCheck_4386_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4346_ = lean_st_ref_take(v___y_4338_);
                v_traceState_4347_ = leanh::lean_ctor_get(v___x_4346_, 4);
                v_env_4348_ = leanh::lean_ctor_get(v___x_4346_, 0);
                v_nextMacroScope_4349_ = leanh::lean_ctor_get(v___x_4346_, 1);
                v_ngen_4350_ = leanh::lean_ctor_get(v___x_4346_, 2);
                v_auxDeclNGen_4351_ = leanh::lean_ctor_get(v___x_4346_, 3);
                v_cache_4352_ = leanh::lean_ctor_get(v___x_4346_, 5);
                v_messages_4353_ = leanh::lean_ctor_get(v___x_4346_, 6);
                v_infoState_4354_ = leanh::lean_ctor_get(v___x_4346_, 7);
                v_snapshotTasks_4355_ = leanh::lean_ctor_get(v___x_4346_, 8);
                v_isSharedCheck_4385_ = (!leanh::lean_is_exclusive(v___x_4346_)) as u8;
                if v_isSharedCheck_4385_ == 0 {
                    v___x_4357_ = v___x_4346_;
                    v_isShared_4358_ = v_isSharedCheck_4385_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4355_);
                    leanh::lean_inc(v_infoState_4354_);
                    leanh::lean_inc(v_messages_4353_);
                    leanh::lean_inc(v_cache_4352_);
                    leanh::lean_inc(v_traceState_4347_);
                    leanh::lean_inc(v_auxDeclNGen_4351_);
                    leanh::lean_inc(v_ngen_4350_);
                    leanh::lean_inc(v_nextMacroScope_4349_);
                    leanh::lean_inc(v_env_4348_);
                    leanh::lean_dec(v___x_4346_);
                    v___x_4357_ = leanh::lean_box(0);
                    v_isShared_4358_ = v_isSharedCheck_4385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4359_ = leanh::lean_ctor_get_uint64(
                    v_traceState_4347_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4360_ = leanh::lean_ctor_get(v_traceState_4347_, 0);
                v_isSharedCheck_4384_ =
                    (!leanh::lean_is_exclusive(v_traceState_4347_)) as u8;
                if v_isSharedCheck_4384_ == 0 {
                    v___x_4362_ = v_traceState_4347_;
                    v_isShared_4363_ = v_isSharedCheck_4384_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_4360_);
                    leanh::lean_dec(v_traceState_4347_);
                    v___x_4362_ = leanh::lean_box(0);
                    v_isShared_4363_ = v_isSharedCheck_4384_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4364_ = leanh::lean_box(0);
                v___x_4365_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0);
                v___x_4366_ = 0;
                v___x_4367_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1;
                v___x_4368_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_4368_, 0, v_cls_4333_);
                leanh::lean_ctor_set(v___x_4368_, 1, v___x_4364_);
                leanh::lean_ctor_set(v___x_4368_, 2, v___x_4367_);
                leanh::lean_ctor_set_float(
                    v___x_4368_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4365_,
                );
                leanh::lean_ctor_set_float(
                    v___x_4368_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4365_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4368_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4366_,
                );
                v___x_4369_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2;
                v___x_4370_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4370_, 0, v___x_4368_);
                leanh::lean_ctor_set(v___x_4370_, 1, v_a_4342_);
                leanh::lean_ctor_set(v___x_4370_, 2, v___x_4369_);
                leanh::lean_inc(v_ref_4340_);
                v___x_4371_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4371_, 0, v_ref_4340_);
                leanh::lean_ctor_set(v___x_4371_, 1, v___x_4370_);
                v___x_4372_ = l_Lean_PersistentArray_push___redArg(v_traces_4360_, v___x_4371_);
                if v_isShared_4363_ == 0 {
                    leanh::lean_ctor_set(v___x_4362_, 0, v___x_4372_);
                    v___x_4374_ = v___x_4362_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4383_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4372_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4383_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_4359_,
                    );
                    v___x_4374_ = v_reuseFailAlloc_4383_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4358_ == 0 {
                    leanh::lean_ctor_set(v___x_4357_, 4, v___x_4374_);
                    v___x_4376_ = v___x_4357_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4382_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_env_4348_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_nextMacroScope_4349_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 2, v_ngen_4350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 3, v_auxDeclNGen_4351_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 4, v___x_4374_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 5, v_cache_4352_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 6, v_messages_4353_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 7, v_infoState_4354_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 8, v_snapshotTasks_4355_);
                    v___x_4376_ = v_reuseFailAlloc_4382_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4377_ = lean_st_ref_set(v___y_4338_, v___x_4376_);
                v___x_4378_ = leanh::lean_box(0);
                if v_isShared_4345_ == 0 {
                    leanh::lean_ctor_set(v___x_4344_, 0, v___x_4378_);
                    v___x_4380_ = v___x_4344_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4381_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4378_);
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
    mut v_cls_4387_: *mut leanh::LeanObject,
    mut v_msg_4388_: *mut leanh::LeanObject,
    mut v___y_4389_: *mut leanh::LeanObject,
    mut v___y_4390_: *mut leanh::LeanObject,
    mut v___y_4391_: *mut leanh::LeanObject,
    mut v___y_4392_: *mut leanh::LeanObject,
    mut v___y_4393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4394_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(
        v_cls_4387_,
        v_msg_4388_,
        v___y_4389_,
        v___y_4390_,
        v___y_4391_,
        v___y_4392_,
    );
    leanh::lean_dec(v___y_4392_);
    leanh::lean_dec_ref(v___y_4391_);
    leanh::lean_dec(v___y_4390_);
    leanh::lean_dec_ref(v___y_4389_);
    return v_res_4394_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(
    mut v_x_4395_: *mut leanh::LeanObject,
    mut v_x_4396_: *mut leanh::LeanObject,
    mut v___y_4397_: *mut leanh::LeanObject,
    mut v___y_4398_: *mut leanh::LeanObject,
    mut v___y_4399_: *mut leanh::LeanObject,
    mut v___y_4400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4408_: u8 = 0;
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4418_: u8 = 0;
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4422_: u8 = 0;
    let mut v_isSharedCheck_4423_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4395_) == 0 {
                    v___x_4402_ = l_List_reverse___redArg(v_x_4396_);
                    v___x_4403_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4403_, 0, v___x_4402_);
                    return v___x_4403_;
                } else {
                    v_head_4404_ = leanh::lean_ctor_get(v_x_4395_, 0);
                    v_tail_4405_ = leanh::lean_ctor_get(v_x_4395_, 1);
                    v_isSharedCheck_4423_ = (!leanh::lean_is_exclusive(v_x_4395_)) as u8;
                    if v_isSharedCheck_4423_ == 0 {
                        v___x_4407_ = v_x_4395_;
                        v_isShared_4408_ = v_isSharedCheck_4423_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4405_);
                        leanh::lean_inc(v_head_4404_);
                        leanh::lean_dec(v_x_4395_);
                        v___x_4407_ = leanh::lean_box(0);
                        v_isShared_4408_ = v_isSharedCheck_4423_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_4400_);
                leanh::lean_inc_ref(v___y_4399_);
                leanh::lean_inc(v___y_4398_);
                leanh::lean_inc_ref(v___y_4397_);
                v___x_4409_ = lean_infer_type(
                    v_head_4404_,
                    v___y_4397_,
                    v___y_4398_,
                    v___y_4399_,
                    v___y_4400_,
                );
                if leanh::lean_obj_tag(v___x_4409_) == 0 {
                    v_a_4410_ = leanh::lean_ctor_get(v___x_4409_, 0);
                    leanh::lean_inc(v_a_4410_);
                    leanh::lean_dec_ref_known(v___x_4409_, 1);
                    if v_isShared_4408_ == 0 {
                        leanh::lean_ctor_set(v___x_4407_, 1, v_x_4396_);
                        leanh::lean_ctor_set(v___x_4407_, 0, v_a_4410_);
                        v___x_4412_ = v___x_4407_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4414_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4410_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 1, v_x_4396_);
                        v___x_4412_ = v_reuseFailAlloc_4414_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4407_);
                    leanh::lean_dec(v_tail_4405_);
                    leanh::lean_dec(v_x_4396_);
                    v_a_4415_ = leanh::lean_ctor_get(v___x_4409_, 0);
                    v_isSharedCheck_4422_ = (!leanh::lean_is_exclusive(v___x_4409_)) as u8;
                    if v_isSharedCheck_4422_ == 0 {
                        v___x_4417_ = v___x_4409_;
                        v_isShared_4418_ = v_isSharedCheck_4422_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4415_);
                        leanh::lean_dec(v___x_4409_);
                        v___x_4417_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4421_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
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
    mut v_x_4424_: *mut leanh::LeanObject,
    mut v_x_4425_: *mut leanh::LeanObject,
    mut v___y_4426_: *mut leanh::LeanObject,
    mut v___y_4427_: *mut leanh::LeanObject,
    mut v___y_4428_: *mut leanh::LeanObject,
    mut v___y_4429_: *mut leanh::LeanObject,
    mut v___y_4430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4431_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(
        v_x_4424_,
        v_x_4425_,
        v___y_4426_,
        v___y_4427_,
        v___y_4428_,
        v___y_4429_,
    );
    leanh::lean_dec(v___y_4429_);
    leanh::lean_dec_ref(v___y_4428_);
    leanh::lean_dec(v___y_4427_);
    leanh::lean_dec_ref(v___y_4426_);
    return v_res_4431_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(
    mut v_a_4432_: *mut leanh::LeanObject,
    mut v_a_4433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4439_: u8 = 0;
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4445_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4432_) == 0 {
                    v___x_4434_ = l_List_reverse___redArg(v_a_4433_);
                    return v___x_4434_;
                } else {
                    v_head_4435_ = leanh::lean_ctor_get(v_a_4432_, 0);
                    v_tail_4436_ = leanh::lean_ctor_get(v_a_4432_, 1);
                    v_isSharedCheck_4445_ = (!leanh::lean_is_exclusive(v_a_4432_)) as u8;
                    if v_isSharedCheck_4445_ == 0 {
                        v___x_4438_ = v_a_4432_;
                        v_isShared_4439_ = v_isSharedCheck_4445_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4436_);
                        leanh::lean_inc(v_head_4435_);
                        leanh::lean_dec(v_a_4432_);
                        v___x_4438_ = leanh::lean_box(0);
                        v_isShared_4439_ = v_isSharedCheck_4445_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4440_ = l_Lean_MessageData_ofExpr(v_head_4435_);
                if v_isShared_4439_ == 0 {
                    leanh::lean_ctor_set(v___x_4438_, 1, v_a_4433_);
                    leanh::lean_ctor_set(v___x_4438_, 0, v___x_4440_);
                    v___x_4442_ = v___x_4438_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4444_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4440_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4444_, 1, v_a_4433_);
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
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4452_ = l_Lean_Elab_Tactic_Omega_lookup___closed__1;
    v___x_4453_ = l_Lean_Elab_Tactic_Omega_lookup___closed__3;
    v___x_4454_ = l_Lean_Name_append(v___x_4453_, v___x_4452_);
    return v___x_4454_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4456_ = l_Lean_Elab_Tactic_Omega_lookup___closed__5;
    v___x_4457_ = l_Lean_stringToMessageData(v___x_4456_);
    return v___x_4457_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_lookup___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4459_ = l_Lean_Elab_Tactic_Omega_lookup___closed__7;
    v___x_4460_ = l_Lean_stringToMessageData(v___x_4459_);
    return v___x_4460_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_lookup(
    mut v_e_4461_: *mut leanh::LeanObject,
    mut v_a_4462_: *mut leanh::LeanObject,
    mut v_a_4463_: *mut leanh::LeanObject,
    mut v_a_4464_: *mut leanh::LeanObject,
    mut v_a_4465_: u8,
    mut v_a_4466_: *mut leanh::LeanObject,
    mut v_a_4467_: *mut leanh::LeanObject,
    mut v_a_4468_: *mut leanh::LeanObject,
    mut v_a_4469_: *mut leanh::LeanObject,
    mut v_a_4470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4477_: u8 = 0;
    let mut v___y_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4493_: u8 = 0;
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4499_: u8 = 0;
    let mut v___y_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4507_: u8 = 0;
    let mut v_a_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: u8 = 0;
    let mut v___x_4513_: u8 = 0;
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4525_: u8 = 0;
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4529_: u8 = 0;
    let mut v_a_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4533_: u8 = 0;
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4537_: u8 = 0;
    let mut v_a_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4541_: u8 = 0;
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4545_: u8 = 0;
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: u8 = 0;
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4555_: u8 = 0;
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4559_: u8 = 0;
    let mut v_val_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4563_: u8 = 0;
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4569_: u8 = 0;
    let mut v_isSharedCheck_4570_: u8 = 0;
    let mut v_a_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4574_: u8 = 0;
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4472_ = lean_st_ref_get(v_a_4463_);
                v___x_4473_ = l_Lean_Meta_Canonicalizer_canon(
                    v_e_4461_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_,
                );
                if leanh::lean_obj_tag(v___x_4473_) == 0 {
                    v_a_4474_ = leanh::lean_ctor_get(v___x_4473_, 0);
                    v_isSharedCheck_4570_ = (!leanh::lean_is_exclusive(v___x_4473_)) as u8;
                    if v_isSharedCheck_4570_ == 0 {
                        v___x_4476_ = v___x_4473_;
                        v_isShared_4477_ = v_isSharedCheck_4570_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4474_);
                        leanh::lean_dec(v___x_4473_);
                        v___x_4476_ = leanh::lean_box(0);
                        v_isShared_4477_ = v_isSharedCheck_4570_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4472_);
                    v_a_4571_ = leanh::lean_ctor_get(v___x_4473_, 0);
                    v_isSharedCheck_4578_ = (!leanh::lean_is_exclusive(v___x_4473_)) as u8;
                    if v_isSharedCheck_4578_ == 0 {
                        v___x_4573_ = v___x_4473_;
                        v_isShared_4574_ = v_isSharedCheck_4578_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4571_);
                        leanh::lean_dec(v___x_4473_);
                        v___x_4573_ = leanh::lean_box(0);
                        v_isShared_4574_ = v_isSharedCheck_4578_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v___x_4472_, v_a_4474_);
                leanh::lean_dec(v___x_4472_);
                if leanh::lean_obj_tag(v___x_4490_) == 0 {
                    v_options_4491_ = leanh::lean_ctor_get(v_a_4469_, 2);
                    v_inheritedTraceOptions_4492_ = leanh::lean_ctor_get(v_a_4469_, 13);
                    v_hasTrace_4493_ = leanh::lean_ctor_get_uint8(
                        v_options_4491_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
                        v___x_4546_ = leanh::lean_obj_once(
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
                            v___x_4548_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_Omega_lookup___closed__8
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_Omega_lookup___closed__8_once
                                ),
                                _init_l_Lean_Elab_Tactic_Omega_lookup___closed__8,
                            );
                            leanh::lean_inc(v_a_4474_);
                            v___x_4549_ = l_Lean_MessageData_ofExpr(v_a_4474_);
                            v___x_4550_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4550_, 0, v___x_4548_);
                            leanh::lean_ctor_set(v___x_4550_, 1, v___x_4549_);
                            v___x_4551_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v___x_4494_, v___x_4550_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
                            if leanh::lean_obj_tag(v___x_4551_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4551_, 1);
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
                                leanh::lean_del_object(v___x_4476_);
                                leanh::lean_dec(v_a_4474_);
                                v_a_4552_ = leanh::lean_ctor_get(v___x_4551_, 0);
                                v_isSharedCheck_4559_ =
                                    (!leanh::lean_is_exclusive(v___x_4551_)) as u8;
                                if v_isSharedCheck_4559_ == 0 {
                                    v___x_4554_ = v___x_4551_;
                                    v_isShared_4555_ = v_isSharedCheck_4559_;
                                    state = 11;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4552_);
                                    leanh::lean_dec(v___x_4551_);
                                    v___x_4554_ = leanh::lean_box(0);
                                    v_isShared_4555_ = v_isSharedCheck_4559_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4476_);
                    leanh::lean_dec(v_a_4474_);
                    v_val_4560_ = leanh::lean_ctor_get(v___x_4490_, 0);
                    v_isSharedCheck_4569_ = (!leanh::lean_is_exclusive(v___x_4490_)) as u8;
                    if v_isSharedCheck_4569_ == 0 {
                        v___x_4562_ = v___x_4490_;
                        v_isShared_4563_ = v_isSharedCheck_4569_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4560_);
                        leanh::lean_dec(v___x_4490_);
                        v___x_4562_ = leanh::lean_box(0);
                        v_isShared_4563_ = v_isSharedCheck_4569_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4481_ = lean_st_ref_take(v___y_4480_);
                v_size_4482_ = leanh::lean_ctor_get(v___x_4481_, 0);
                leanh::lean_inc_n(v_size_4482_, 2);
                v___x_4483_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v___x_4481_, v_a_4474_, v_size_4482_);
                v___x_4484_ = lean_st_ref_set(v___y_4480_, v___x_4483_);
                v___x_4485_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4485_, 0, v___y_4479_);
                v___x_4486_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4486_, 0, v_size_4482_);
                leanh::lean_ctor_set(v___x_4486_, 1, v___x_4485_);
                if v_isShared_4477_ == 0 {
                    leanh::lean_ctor_set(v___x_4476_, 0, v___x_4486_);
                    v___x_4488_ = v___x_4476_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4489_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4489_, 0, v___x_4486_);
                    v___x_4488_ = v_reuseFailAlloc_4489_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4488_;
            }
            4 => {
                leanh::lean_inc(v_a_4474_);
                v___x_4505_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(
                    v_a_4474_,
                    v___y_4498_,
                    v___y_4501_,
                    v___y_4502_,
                    v___y_4503_,
                    v___y_4504_,
                );
                if leanh::lean_obj_tag(v___x_4505_) == 0 {
                    v_options_4506_ = leanh::lean_ctor_get(v___y_4503_, 2);
                    v_hasTrace_4507_ = leanh::lean_ctor_get_uint8(
                        v_options_4506_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4507_ == 0 {
                        v_a_4508_ = leanh::lean_ctor_get(v___x_4505_, 0);
                        leanh::lean_inc(v_a_4508_);
                        leanh::lean_dec_ref_known(v___x_4505_, 1);
                        v___y_4479_ = v_a_4508_;
                        v___y_4480_ = v___y_4497_;
                        state = 2;
                        continue;
                    } else {
                        v_a_4509_ = leanh::lean_ctor_get(v___x_4505_, 0);
                        leanh::lean_inc(v_a_4509_);
                        leanh::lean_dec_ref_known(v___x_4505_, 1);
                        v_inheritedTraceOptions_4510_ =
                            leanh::lean_ctor_get(v___y_4503_, 13);
                        v___x_4511_ = leanh::lean_obj_once(
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
                                    v___x_4514_ = leanh::lean_box(0);
                                    leanh::lean_inc(v_a_4509_);
                                    v___x_4515_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_a_4509_, v___x_4514_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
                                    if leanh::lean_obj_tag(v___x_4515_) == 0 {
                                        v_a_4516_ = leanh::lean_ctor_get(v___x_4515_, 0);
                                        leanh::lean_inc(v_a_4516_);
                                        leanh::lean_dec_ref_known(v___x_4515_, 1);
                                        v___x_4517_ = leanh::lean_obj_once(
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
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_4520_, 0, v___x_4517_);
                                        leanh::lean_ctor_set(v___x_4520_, 1, v___x_4519_);
                                        v___x_4521_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v___x_4494_, v___x_4520_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
                                        if leanh::lean_obj_tag(v___x_4521_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_4521_, 1);
                                            v___y_4479_ = v_a_4509_;
                                            v___y_4480_ = v___y_4497_;
                                            state = 2;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v_a_4509_);
                                            leanh::lean_del_object(v___x_4476_);
                                            leanh::lean_dec(v_a_4474_);
                                            v_a_4522_ = leanh::lean_ctor_get(v___x_4521_, 0);
                                            v_isSharedCheck_4529_ =
                                                (!leanh::lean_is_exclusive(v___x_4521_))
                                                    as u8;
                                            if v_isSharedCheck_4529_ == 0 {
                                                v___x_4524_ = v___x_4521_;
                                                v_isShared_4525_ = v_isSharedCheck_4529_;
                                                state = 5;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_4522_);
                                                leanh::lean_dec(v___x_4521_);
                                                v___x_4524_ = leanh::lean_box(0);
                                                v_isShared_4525_ = v_isSharedCheck_4529_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_4509_);
                                        leanh::lean_del_object(v___x_4476_);
                                        leanh::lean_dec(v_a_4474_);
                                        v_a_4530_ = leanh::lean_ctor_get(v___x_4515_, 0);
                                        v_isSharedCheck_4537_ =
                                            (!leanh::lean_is_exclusive(v___x_4515_)) as u8;
                                        if v_isSharedCheck_4537_ == 0 {
                                            v___x_4532_ = v___x_4515_;
                                            v_isShared_4533_ = v_isSharedCheck_4537_;
                                            state = 7;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4530_);
                                            leanh::lean_dec(v___x_4515_);
                                            v___x_4532_ = leanh::lean_box(0);
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
                    leanh::lean_del_object(v___x_4476_);
                    leanh::lean_dec(v_a_4474_);
                    v_a_4538_ = leanh::lean_ctor_get(v___x_4505_, 0);
                    v_isSharedCheck_4545_ = (!leanh::lean_is_exclusive(v___x_4505_)) as u8;
                    if v_isSharedCheck_4545_ == 0 {
                        v___x_4540_ = v___x_4505_;
                        v_isShared_4541_ = v_isSharedCheck_4545_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4538_);
                        leanh::lean_dec(v___x_4505_);
                        v___x_4540_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4528_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
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
                    v_reuseFailAlloc_4536_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4530_);
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
                    v_reuseFailAlloc_4544_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
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
                    v_reuseFailAlloc_4558_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
                    v___x_4557_ = v_reuseFailAlloc_4558_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4557_;
            }
            13 => {
                v___x_4564_ = leanh::lean_box(0);
                v___x_4565_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4565_, 0, v_val_4560_);
                leanh::lean_ctor_set(v___x_4565_, 1, v___x_4564_);
                if v_isShared_4563_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4562_, 0);
                    leanh::lean_ctor_set(v___x_4562_, 0, v___x_4565_);
                    v___x_4567_ = v___x_4562_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4568_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4568_, 0, v___x_4565_);
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
                    v_reuseFailAlloc_4577_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
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
    mut v_e_4579_: *mut leanh::LeanObject,
    mut v_a_4580_: *mut leanh::LeanObject,
    mut v_a_4581_: *mut leanh::LeanObject,
    mut v_a_4582_: *mut leanh::LeanObject,
    mut v_a_4583_: *mut leanh::LeanObject,
    mut v_a_4584_: *mut leanh::LeanObject,
    mut v_a_4585_: *mut leanh::LeanObject,
    mut v_a_4586_: *mut leanh::LeanObject,
    mut v_a_4587_: *mut leanh::LeanObject,
    mut v_a_4588_: *mut leanh::LeanObject,
    mut v_a_4589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_4590_: u8 = 0;
    let mut v_res_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4590_ = (leanh::lean_unbox(v_a_4583_) as u8);
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
    leanh::lean_dec(v_a_4588_);
    leanh::lean_dec_ref(v_a_4587_);
    leanh::lean_dec(v_a_4586_);
    leanh::lean_dec_ref(v_a_4585_);
    leanh::lean_dec(v_a_4584_);
    leanh::lean_dec_ref(v_a_4582_);
    leanh::lean_dec(v_a_4581_);
    leanh::lean_dec(v_a_4580_);
    return v_res_4591_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(
    mut v_00_u03b2_4592_: *mut leanh::LeanObject,
    mut v_m_4593_: *mut leanh::LeanObject,
    mut v_a_4594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4595_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_4593_, v_a_4594_);
    return v___x_4595_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(
    mut v_00_u03b2_4596_: *mut leanh::LeanObject,
    mut v_m_4597_: *mut leanh::LeanObject,
    mut v_a_4598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(v_00_u03b2_4596_, v_m_4597_, v_a_4598_);
    leanh::lean_dec_ref(v_a_4598_);
    leanh::lean_dec_ref(v_m_4597_);
    return v_res_4599_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1(
    mut v_00_u03b2_4600_: *mut leanh::LeanObject,
    mut v_m_4601_: *mut leanh::LeanObject,
    mut v_a_4602_: *mut leanh::LeanObject,
    mut v_b_4603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4604_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v_m_4601_, v_a_4602_, v_b_4603_);
    return v___x_4604_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(
    mut v_x_4605_: *mut leanh::LeanObject,
    mut v_x_4606_: *mut leanh::LeanObject,
    mut v___y_4607_: *mut leanh::LeanObject,
    mut v___y_4608_: *mut leanh::LeanObject,
    mut v___y_4609_: *mut leanh::LeanObject,
    mut v___y_4610_: u8,
    mut v___y_4611_: *mut leanh::LeanObject,
    mut v___y_4612_: *mut leanh::LeanObject,
    mut v___y_4613_: *mut leanh::LeanObject,
    mut v___y_4614_: *mut leanh::LeanObject,
    mut v___y_4615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_4618_: *mut leanh::LeanObject,
    mut v_x_4619_: *mut leanh::LeanObject,
    mut v___y_4620_: *mut leanh::LeanObject,
    mut v___y_4621_: *mut leanh::LeanObject,
    mut v___y_4622_: *mut leanh::LeanObject,
    mut v___y_4623_: *mut leanh::LeanObject,
    mut v___y_4624_: *mut leanh::LeanObject,
    mut v___y_4625_: *mut leanh::LeanObject,
    mut v___y_4626_: *mut leanh::LeanObject,
    mut v___y_4627_: *mut leanh::LeanObject,
    mut v___y_4628_: *mut leanh::LeanObject,
    mut v___y_4629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_42932__boxed_4630_: u8 = 0;
    let mut v_res_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_42932__boxed_4630_ = (leanh::lean_unbox(v___y_4623_) as u8);
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
    leanh::lean_dec(v___y_4628_);
    leanh::lean_dec_ref(v___y_4627_);
    leanh::lean_dec(v___y_4626_);
    leanh::lean_dec_ref(v___y_4625_);
    leanh::lean_dec(v___y_4624_);
    leanh::lean_dec_ref(v___y_4622_);
    leanh::lean_dec(v___y_4621_);
    leanh::lean_dec(v___y_4620_);
    return v_res_4631_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(
    mut v_cls_4632_: *mut leanh::LeanObject,
    mut v_msg_4633_: *mut leanh::LeanObject,
    mut v___y_4634_: *mut leanh::LeanObject,
    mut v___y_4635_: *mut leanh::LeanObject,
    mut v___y_4636_: *mut leanh::LeanObject,
    mut v___y_4637_: u8,
    mut v___y_4638_: *mut leanh::LeanObject,
    mut v___y_4639_: *mut leanh::LeanObject,
    mut v___y_4640_: *mut leanh::LeanObject,
    mut v___y_4641_: *mut leanh::LeanObject,
    mut v___y_4642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_cls_4645_: *mut leanh::LeanObject,
    mut v_msg_4646_: *mut leanh::LeanObject,
    mut v___y_4647_: *mut leanh::LeanObject,
    mut v___y_4648_: *mut leanh::LeanObject,
    mut v___y_4649_: *mut leanh::LeanObject,
    mut v___y_4650_: *mut leanh::LeanObject,
    mut v___y_4651_: *mut leanh::LeanObject,
    mut v___y_4652_: *mut leanh::LeanObject,
    mut v___y_4653_: *mut leanh::LeanObject,
    mut v___y_4654_: *mut leanh::LeanObject,
    mut v___y_4655_: *mut leanh::LeanObject,
    mut v___y_4656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_42968__boxed_4657_: u8 = 0;
    let mut v_res_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_42968__boxed_4657_ = (leanh::lean_unbox(v___y_4650_) as u8);
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
    leanh::lean_dec(v___y_4655_);
    leanh::lean_dec_ref(v___y_4654_);
    leanh::lean_dec(v___y_4653_);
    leanh::lean_dec_ref(v___y_4652_);
    leanh::lean_dec(v___y_4651_);
    leanh::lean_dec_ref(v___y_4649_);
    leanh::lean_dec(v___y_4648_);
    leanh::lean_dec(v___y_4647_);
    return v_res_4658_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(
    mut v_00_u03b2_4659_: *mut leanh::LeanObject,
    mut v_a_4660_: *mut leanh::LeanObject,
    mut v_x_4661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4662_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_4660_, v_x_4661_);
    return v___x_4662_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___boxed(
    mut v_00_u03b2_4663_: *mut leanh::LeanObject,
    mut v_a_4664_: *mut leanh::LeanObject,
    mut v_x_4665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4666_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(v_00_u03b2_4663_, v_a_4664_, v_x_4665_);
    leanh::lean_dec(v_x_4665_);
    leanh::lean_dec_ref(v_a_4664_);
    return v_res_4666_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(
    mut v_00_u03b2_4667_: *mut leanh::LeanObject,
    mut v_a_4668_: *mut leanh::LeanObject,
    mut v_x_4669_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4670_: u8 = 0;
    v___x_4670_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_4668_, v_x_4669_);
    return v___x_4670_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___boxed(
    mut v_00_u03b2_4671_: *mut leanh::LeanObject,
    mut v_a_4672_: *mut leanh::LeanObject,
    mut v_x_4673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4674_: u8 = 0;
    let mut v_r_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4674_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(v_00_u03b2_4671_, v_a_4672_, v_x_4673_);
    leanh::lean_dec(v_x_4673_);
    leanh::lean_dec_ref(v_a_4672_);
    v_r_4675_ = leanh::lean_box((v_res_4674_) as usize);
    return v_r_4675_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3(
    mut v_00_u03b2_4676_: *mut leanh::LeanObject,
    mut v_data_4677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4678_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(v_data_4677_);
    return v___x_4678_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4(
    mut v_00_u03b2_4679_: *mut leanh::LeanObject,
    mut v_a_4680_: *mut leanh::LeanObject,
    mut v_b_4681_: *mut leanh::LeanObject,
    mut v_x_4682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4683_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_4680_, v_b_4681_, v_x_4682_);
    return v___x_4683_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4(
    mut v_00_u03b2_4684_: *mut leanh::LeanObject,
    mut v_i_4685_: *mut leanh::LeanObject,
    mut v_source_4686_: *mut leanh::LeanObject,
    mut v_target_4687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4688_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(v_i_4685_, v_source_4686_, v_target_4687_);
    return v___x_4688_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9(
    mut v_00_u03b2_4689_: *mut leanh::LeanObject,
    mut v_x_4690_: *mut leanh::LeanObject,
    mut v_x_4691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4692_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(v_x_4690_, v_x_4691_);
    return v___x_4692_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Canonicalizer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Omega_OmegaM(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Omega_OmegaM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Canonicalizer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
}