// Lean compiler output
// Module: Lean.Meta.Reduce
// Imports: Lean.Meta.FunInfo Init.Data.Range.Polymorphic.Iterators
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Prelude::l_Lean_maxRecDepthErrorMessage;
use crate::r#gen::Init::System::CancelToken::l_IO_CancelToken_isSet;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Exception::l_Lean_interruptExceptionId;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hash, l_Lean_Expr_isConstOf, l_Lean_Expr_isRawNatLit,
    l_Lean_Expr_rawNatLit_x3f, l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr,
    l_Lean_mkAppN, l_Lean_mkProj, l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp, l_Lean_Meta_ParamInfo_isExplicit,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::FunInfo::{
    initialize_Lean_Meta_FunInfo, l_Lean_Meta_getFunInfoNArgs, runtime_initialize_Lean_Meta_FunInfo,
};
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_isProof, l_Lean_Meta_isType};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_whnf;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2_value:
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
        118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
    ],
};
static mut l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1_value:
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
    m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
};
static mut l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115,
        105, 99, 65, 117, 120, 0,
    ],
};
static mut l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__6_value:
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
    m_data: [115, 117, 99, 99, 0],
};
static mut l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__5_value:
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
    m_data: [78, 97, 116, 0],
};
static mut l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__5_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7_value_aux_0:
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
            l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7_value:
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
            l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        16112798088292836701 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_reduce___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_reduce___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_reduce___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_reduce___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_panic___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__1(
    mut v_msg_950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_951_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_952_ = lean_panic_fn_borrowed(v___x_951_, v_msg_950_);
    return v___x_952_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0(
    mut v_k_953_: *mut crate::leanh::LeanObject,
    mut v___y_954_: *mut crate::leanh::LeanObject,
    mut v_b_955_: *mut crate::leanh::LeanObject,
    mut v_c_956_: *mut crate::leanh::LeanObject,
    mut v___y_957_: *mut crate::leanh::LeanObject,
    mut v___y_958_: *mut crate::leanh::LeanObject,
    mut v___y_959_: *mut crate::leanh::LeanObject,
    mut v___y_960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_960_);
    crate::leanh::lean_inc_ref(v___y_959_);
    crate::leanh::lean_inc(v___y_958_);
    crate::leanh::lean_inc_ref(v___y_957_);
    crate::leanh::lean_inc(v___y_954_);
    v___x_962_ = crate::leanh::lean_apply_8(
        v_k_953_,
        v_b_955_,
        v_c_956_,
        v___y_954_,
        v___y_957_,
        v___y_958_,
        v___y_959_,
        v___y_960_,
        crate::leanh::lean_box(0),
    );
    return v___x_962_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0___boxed(
    mut v_k_963_: *mut crate::leanh::LeanObject,
    mut v___y_964_: *mut crate::leanh::LeanObject,
    mut v_b_965_: *mut crate::leanh::LeanObject,
    mut v_c_966_: *mut crate::leanh::LeanObject,
    mut v___y_967_: *mut crate::leanh::LeanObject,
    mut v___y_968_: *mut crate::leanh::LeanObject,
    mut v___y_969_: *mut crate::leanh::LeanObject,
    mut v___y_970_: *mut crate::leanh::LeanObject,
    mut v___y_971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_972_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0(v_k_963_, v___y_964_, v_b_965_, v_c_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
    crate::leanh::lean_dec(v___y_970_);
    crate::leanh::lean_dec_ref(v___y_969_);
    crate::leanh::lean_dec(v___y_968_);
    crate::leanh::lean_dec_ref(v___y_967_);
    crate::leanh::lean_dec(v___y_964_);
    return v_res_972_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(
    mut v_e_973_: *mut crate::leanh::LeanObject,
    mut v_k_974_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_975_: u8,
    mut v___y_976_: *mut crate::leanh::LeanObject,
    mut v___y_977_: *mut crate::leanh::LeanObject,
    mut v___y_978_: *mut crate::leanh::LeanObject,
    mut v___y_979_: *mut crate::leanh::LeanObject,
    mut v___y_980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: u8 = 0;
    let mut v___x_984_: u8 = 0;
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_976_);
                v___f_982_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                crate::leanh::lean_closure_set(v___f_982_, 0, v_k_974_);
                crate::leanh::lean_closure_set(v___f_982_, 1, v___y_976_);
                v___x_983_ = 1;
                v___x_984_ = 0;
                v___x_985_ = crate::leanh::lean_box(0);
                v___x_986_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    crate::leanh::lean_box(0),
                    v_e_973_,
                    v___x_983_,
                    v___x_984_,
                    v___x_983_,
                    v___x_984_,
                    v___x_985_,
                    v___f_982_,
                    v_cleanupAnnotations_975_,
                    v___y_977_,
                    v___y_978_,
                    v___y_979_,
                    v___y_980_,
                );
                if crate::leanh::lean_obj_tag(v___x_986_) == 0 {
                    return v___x_986_;
                } else {
                    v_a_987_ = crate::leanh::lean_ctor_get(v___x_986_, 0);
                    v_isSharedCheck_994_ = (!crate::leanh::lean_is_exclusive(v___x_986_)) as u8;
                    if v_isSharedCheck_994_ == 0 {
                        v___x_989_ = v___x_986_;
                        v_isShared_990_ = v_isSharedCheck_994_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_987_);
                        crate::leanh::lean_dec(v___x_986_);
                        v___x_989_ = crate::leanh::lean_box(0);
                        v_isShared_990_ = v_isSharedCheck_994_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_990_ == 0 {
                    v___x_992_ = v___x_989_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_993_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
                    v___x_992_ = v_reuseFailAlloc_993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_992_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___boxed(
    mut v_e_995_: *mut crate::leanh::LeanObject,
    mut v_k_996_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_997_: *mut crate::leanh::LeanObject,
    mut v___y_998_: *mut crate::leanh::LeanObject,
    mut v___y_999_: *mut crate::leanh::LeanObject,
    mut v___y_1000_: *mut crate::leanh::LeanObject,
    mut v___y_1001_: *mut crate::leanh::LeanObject,
    mut v___y_1002_: *mut crate::leanh::LeanObject,
    mut v___y_1003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1004_: u8 = 0;
    let mut v_res_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1004_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_997_) as u8);
    v_res_1005_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(v_e_995_, v_k_996_, v_cleanupAnnotations_boxed_1004_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
    crate::leanh::lean_dec(v___y_1002_);
    crate::leanh::lean_dec_ref(v___y_1001_);
    crate::leanh::lean_dec(v___y_1000_);
    crate::leanh::lean_dec_ref(v___y_999_);
    crate::leanh::lean_dec(v___y_998_);
    return v_res_1005_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3(
    mut v_00_u03b1_1006_: *mut crate::leanh::LeanObject,
    mut v_e_1007_: *mut crate::leanh::LeanObject,
    mut v_k_1008_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1009_: u8,
    mut v___y_1010_: *mut crate::leanh::LeanObject,
    mut v___y_1011_: *mut crate::leanh::LeanObject,
    mut v___y_1012_: *mut crate::leanh::LeanObject,
    mut v___y_1013_: *mut crate::leanh::LeanObject,
    mut v___y_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1016_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(v_e_1007_, v_k_1008_, v_cleanupAnnotations_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
    return v___x_1016_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___boxed(
    mut v_00_u03b1_1017_: *mut crate::leanh::LeanObject,
    mut v_e_1018_: *mut crate::leanh::LeanObject,
    mut v_k_1019_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1020_: *mut crate::leanh::LeanObject,
    mut v___y_1021_: *mut crate::leanh::LeanObject,
    mut v___y_1022_: *mut crate::leanh::LeanObject,
    mut v___y_1023_: *mut crate::leanh::LeanObject,
    mut v___y_1024_: *mut crate::leanh::LeanObject,
    mut v___y_1025_: *mut crate::leanh::LeanObject,
    mut v___y_1026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1027_: u8 = 0;
    let mut v_res_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1027_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1020_) as u8);
    v_res_1028_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3(v_00_u03b1_1017_, v_e_1018_, v_k_1019_, v_cleanupAnnotations_boxed_1027_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
    crate::leanh::lean_dec(v___y_1025_);
    crate::leanh::lean_dec_ref(v___y_1024_);
    crate::leanh::lean_dec(v___y_1023_);
    crate::leanh::lean_dec_ref(v___y_1022_);
    crate::leanh::lean_dec(v___y_1021_);
    return v_res_1028_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(
    mut v_type_1029_: *mut crate::leanh::LeanObject,
    mut v_k_1030_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1031_: u8,
    mut v___y_1032_: *mut crate::leanh::LeanObject,
    mut v___y_1033_: *mut crate::leanh::LeanObject,
    mut v___y_1034_: *mut crate::leanh::LeanObject,
    mut v___y_1035_: *mut crate::leanh::LeanObject,
    mut v___y_1036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: u8 = 0;
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1045_: u8 = 0;
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1032_);
                v___f_1038_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                crate::leanh::lean_closure_set(v___f_1038_, 0, v_k_1030_);
                crate::leanh::lean_closure_set(v___f_1038_, 1, v___y_1032_);
                v___x_1039_ = 0;
                v___x_1040_ = crate::leanh::lean_box(0);
                v___x_1041_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        crate::leanh::lean_box(0),
                        v___x_1039_,
                        v___x_1040_,
                        v_type_1029_,
                        v___f_1038_,
                        v_cleanupAnnotations_1031_,
                        v___x_1039_,
                        v___y_1033_,
                        v___y_1034_,
                        v___y_1035_,
                        v___y_1036_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1041_) == 0 {
                    return v___x_1041_;
                } else {
                    v_a_1042_ = crate::leanh::lean_ctor_get(v___x_1041_, 0);
                    v_isSharedCheck_1049_ = (!crate::leanh::lean_is_exclusive(v___x_1041_)) as u8;
                    if v_isSharedCheck_1049_ == 0 {
                        v___x_1044_ = v___x_1041_;
                        v_isShared_1045_ = v_isSharedCheck_1049_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1042_);
                        crate::leanh::lean_dec(v___x_1041_);
                        v___x_1044_ = crate::leanh::lean_box(0);
                        v_isShared_1045_ = v_isSharedCheck_1049_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1045_ == 0 {
                    v___x_1047_ = v___x_1044_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1048_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
                    v___x_1047_ = v_reuseFailAlloc_1048_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg___boxed(
    mut v_type_1050_: *mut crate::leanh::LeanObject,
    mut v_k_1051_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1052_: *mut crate::leanh::LeanObject,
    mut v___y_1053_: *mut crate::leanh::LeanObject,
    mut v___y_1054_: *mut crate::leanh::LeanObject,
    mut v___y_1055_: *mut crate::leanh::LeanObject,
    mut v___y_1056_: *mut crate::leanh::LeanObject,
    mut v___y_1057_: *mut crate::leanh::LeanObject,
    mut v___y_1058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1059_: u8 = 0;
    let mut v_res_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1059_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1052_) as u8);
    v_res_1060_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(v_type_1050_, v_k_1051_, v_cleanupAnnotations_boxed_1059_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
    crate::leanh::lean_dec(v___y_1057_);
    crate::leanh::lean_dec_ref(v___y_1056_);
    crate::leanh::lean_dec(v___y_1055_);
    crate::leanh::lean_dec_ref(v___y_1054_);
    crate::leanh::lean_dec(v___y_1053_);
    return v_res_1060_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4(
    mut v_00_u03b1_1061_: *mut crate::leanh::LeanObject,
    mut v_type_1062_: *mut crate::leanh::LeanObject,
    mut v_k_1063_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1064_: u8,
    mut v___y_1065_: *mut crate::leanh::LeanObject,
    mut v___y_1066_: *mut crate::leanh::LeanObject,
    mut v___y_1067_: *mut crate::leanh::LeanObject,
    mut v___y_1068_: *mut crate::leanh::LeanObject,
    mut v___y_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1071_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(v_type_1062_, v_k_1063_, v_cleanupAnnotations_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
    return v___x_1071_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___boxed(
    mut v_00_u03b1_1072_: *mut crate::leanh::LeanObject,
    mut v_type_1073_: *mut crate::leanh::LeanObject,
    mut v_k_1074_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1075_: *mut crate::leanh::LeanObject,
    mut v___y_1076_: *mut crate::leanh::LeanObject,
    mut v___y_1077_: *mut crate::leanh::LeanObject,
    mut v___y_1078_: *mut crate::leanh::LeanObject,
    mut v___y_1079_: *mut crate::leanh::LeanObject,
    mut v___y_1080_: *mut crate::leanh::LeanObject,
    mut v___y_1081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1082_: u8 = 0;
    let mut v_res_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1082_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1075_) as u8);
    v_res_1083_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4(v_00_u03b1_1072_, v_type_1073_, v_k_1074_, v_cleanupAnnotations_boxed_1082_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
    crate::leanh::lean_dec(v___y_1080_);
    crate::leanh::lean_dec_ref(v___y_1079_);
    crate::leanh::lean_dec(v___y_1078_);
    crate::leanh::lean_dec_ref(v___y_1077_);
    crate::leanh::lean_dec(v___y_1076_);
    return v_res_1083_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(
    mut v_a_1084_: *mut crate::leanh::LeanObject,
    mut v_x_1085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: u8 = 0;
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1085_) == 0 {
                    v___x_1086_ = crate::leanh::lean_box(0);
                    return v___x_1086_;
                } else {
                    v_key_1087_ = crate::leanh::lean_ctor_get(v_x_1085_, 0);
                    v_value_1088_ = crate::leanh::lean_ctor_get(v_x_1085_, 1);
                    v_tail_1089_ = crate::leanh::lean_ctor_get(v_x_1085_, 2);
                    v___x_1090_ = lean_expr_eqv(v_key_1087_, v_a_1084_);
                    if v___x_1090_ == 0 {
                        v_x_1085_ = v_tail_1089_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_1088_);
                        v___x_1092_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1092_, 0, v_value_1088_);
                        return v___x_1092_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg___boxed(
    mut v_a_1093_: *mut crate::leanh::LeanObject,
    mut v_x_1094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1095_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(v_a_1093_, v_x_1094_);
    crate::leanh::lean_dec(v_x_1094_);
    crate::leanh::lean_dec_ref(v_a_1093_);
    return v_res_1095_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(
    mut v_m_1096_: *mut crate::leanh::LeanObject,
    mut v_a_1097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: u64 = 0;
    let mut v___x_1101_: u64 = 0;
    let mut v___x_1102_: u64 = 0;
    let mut v_fold_1103_: u64 = 0;
    let mut v___x_1104_: u64 = 0;
    let mut v___x_1105_: u64 = 0;
    let mut v___x_1106_: u64 = 0;
    let mut v___x_1107_: usize = 0;
    let mut v___x_1108_: usize = 0;
    let mut v___x_1109_: usize = 0;
    let mut v___x_1110_: usize = 0;
    let mut v___x_1111_: usize = 0;
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1098_ = crate::leanh::lean_ctor_get(v_m_1096_, 1);
    v___x_1099_ = lean_array_get_size(v_buckets_1098_);
    v___x_1100_ = l_Lean_Expr_hash(v_a_1097_);
    v___x_1101_ = 32u64;
    v___x_1102_ = lean_uint64_shift_right(v___x_1100_, v___x_1101_);
    v_fold_1103_ = lean_uint64_xor(v___x_1100_, v___x_1102_);
    v___x_1104_ = 16u64;
    v___x_1105_ = lean_uint64_shift_right(v_fold_1103_, v___x_1104_);
    v___x_1106_ = lean_uint64_xor(v_fold_1103_, v___x_1105_);
    v___x_1107_ = lean_uint64_to_usize(v___x_1106_);
    v___x_1108_ = lean_usize_of_nat(v___x_1099_);
    v___x_1109_ = 1usize;
    v___x_1110_ = lean_usize_sub(v___x_1108_, v___x_1109_);
    v___x_1111_ = lean_usize_land(v___x_1107_, v___x_1110_);
    v___x_1112_ = lean_array_uget_borrowed(v_buckets_1098_, v___x_1111_);
    v___x_1113_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(v_a_1097_, v___x_1112_);
    return v___x_1113_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg___boxed(
    mut v_m_1114_: *mut crate::leanh::LeanObject,
    mut v_a_1115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1116_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v_m_1114_, v_a_1115_);
    crate::leanh::lean_dec_ref(v_a_1115_);
    crate::leanh::lean_dec_ref(v_m_1114_);
    return v_res_1116_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11___redArg(
    mut v_a_1117_: *mut crate::leanh::LeanObject,
    mut v_b_1118_: *mut crate::leanh::LeanObject,
    mut v_x_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1125_: u8 = 0;
    let mut v___x_1126_: u8 = 0;
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1134_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1119_) == 0 {
                    crate::leanh::lean_dec(v_b_1118_);
                    crate::leanh::lean_dec_ref(v_a_1117_);
                    return v_x_1119_;
                } else {
                    v_key_1120_ = crate::leanh::lean_ctor_get(v_x_1119_, 0);
                    v_value_1121_ = crate::leanh::lean_ctor_get(v_x_1119_, 1);
                    v_tail_1122_ = crate::leanh::lean_ctor_get(v_x_1119_, 2);
                    v_isSharedCheck_1134_ = (!crate::leanh::lean_is_exclusive(v_x_1119_)) as u8;
                    if v_isSharedCheck_1134_ == 0 {
                        v___x_1124_ = v_x_1119_;
                        v_isShared_1125_ = v_isSharedCheck_1134_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1122_);
                        crate::leanh::lean_inc(v_value_1121_);
                        crate::leanh::lean_inc(v_key_1120_);
                        crate::leanh::lean_dec(v_x_1119_);
                        v___x_1124_ = crate::leanh::lean_box(0);
                        v_isShared_1125_ = v_isSharedCheck_1134_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1126_ = lean_expr_eqv(v_key_1120_, v_a_1117_);
                if v___x_1126_ == 0 {
                    v___x_1127_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11___redArg(v_a_1117_, v_b_1118_, v_tail_1122_);
                    if v_isShared_1125_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1124_, 2, v___x_1127_);
                        v___x_1129_ = v___x_1124_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1130_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_key_1120_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_value_1121_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1130_, 2, v___x_1127_);
                        v___x_1129_ = v_reuseFailAlloc_1130_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1121_);
                    crate::leanh::lean_dec(v_key_1120_);
                    if v_isShared_1125_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1124_, 1, v_b_1118_);
                        crate::leanh::lean_ctor_set(v___x_1124_, 0, v_a_1117_);
                        v___x_1132_ = v___x_1124_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1133_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1117_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_b_1118_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_tail_1122_);
                        v___x_1132_ = v_reuseFailAlloc_1133_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1129_;
            }
            3 => {
                return v___x_1132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(
    mut v_a_1135_: *mut crate::leanh::LeanObject,
    mut v_x_1136_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1137_: u8 = 0;
    let mut v_key_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1136_) == 0 {
                    v___x_1137_ = 0;
                    return v___x_1137_;
                } else {
                    v_key_1138_ = crate::leanh::lean_ctor_get(v_x_1136_, 0);
                    v_tail_1139_ = crate::leanh::lean_ctor_get(v_x_1136_, 2);
                    v___x_1140_ = lean_expr_eqv(v_key_1138_, v_a_1135_);
                    if v___x_1140_ == 0 {
                        v_x_1136_ = v_tail_1139_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1140_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg___boxed(
    mut v_a_1142_: *mut crate::leanh::LeanObject,
    mut v_x_1143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1144_: u8 = 0;
    let mut v_r_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1144_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_a_1142_, v_x_1143_);
    crate::leanh::lean_dec(v_x_1143_);
    crate::leanh::lean_dec_ref(v_a_1142_);
    v_r_1145_ = crate::leanh::lean_box((v_res_1144_) as usize);
    return v_r_1145_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11_spec__12___redArg(
    mut v_x_1146_: *mut crate::leanh::LeanObject,
    mut v_x_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1153_: u8 = 0;
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: u64 = 0;
    let mut v___x_1156_: u64 = 0;
    let mut v___x_1157_: u64 = 0;
    let mut v_fold_1158_: u64 = 0;
    let mut v___x_1159_: u64 = 0;
    let mut v___x_1160_: u64 = 0;
    let mut v___x_1161_: u64 = 0;
    let mut v___x_1162_: usize = 0;
    let mut v___x_1163_: usize = 0;
    let mut v___x_1164_: usize = 0;
    let mut v___x_1165_: usize = 0;
    let mut v___x_1166_: usize = 0;
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1173_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1147_) == 0 {
                    return v_x_1146_;
                } else {
                    v_key_1148_ = crate::leanh::lean_ctor_get(v_x_1147_, 0);
                    v_value_1149_ = crate::leanh::lean_ctor_get(v_x_1147_, 1);
                    v_tail_1150_ = crate::leanh::lean_ctor_get(v_x_1147_, 2);
                    v_isSharedCheck_1173_ = (!crate::leanh::lean_is_exclusive(v_x_1147_)) as u8;
                    if v_isSharedCheck_1173_ == 0 {
                        v___x_1152_ = v_x_1147_;
                        v_isShared_1153_ = v_isSharedCheck_1173_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1150_);
                        crate::leanh::lean_inc(v_value_1149_);
                        crate::leanh::lean_inc(v_key_1148_);
                        crate::leanh::lean_dec(v_x_1147_);
                        v___x_1152_ = crate::leanh::lean_box(0);
                        v_isShared_1153_ = v_isSharedCheck_1173_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1154_ = lean_array_get_size(v_x_1146_);
                v___x_1155_ = l_Lean_Expr_hash(v_key_1148_);
                v___x_1156_ = 32u64;
                v___x_1157_ = lean_uint64_shift_right(v___x_1155_, v___x_1156_);
                v_fold_1158_ = lean_uint64_xor(v___x_1155_, v___x_1157_);
                v___x_1159_ = 16u64;
                v___x_1160_ = lean_uint64_shift_right(v_fold_1158_, v___x_1159_);
                v___x_1161_ = lean_uint64_xor(v_fold_1158_, v___x_1160_);
                v___x_1162_ = lean_uint64_to_usize(v___x_1161_);
                v___x_1163_ = lean_usize_of_nat(v___x_1154_);
                v___x_1164_ = 1usize;
                v___x_1165_ = lean_usize_sub(v___x_1163_, v___x_1164_);
                v___x_1166_ = lean_usize_land(v___x_1162_, v___x_1165_);
                v___x_1167_ = lean_array_uget_borrowed(v_x_1146_, v___x_1166_);
                crate::leanh::lean_inc(v___x_1167_);
                if v_isShared_1153_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1152_, 2, v___x_1167_);
                    v___x_1169_ = v___x_1152_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1172_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_key_1148_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_value_1149_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1172_, 2, v___x_1167_);
                    v___x_1169_ = v_reuseFailAlloc_1172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1170_ = lean_array_uset(v_x_1146_, v___x_1166_, v___x_1169_);
                v_x_1146_ = v___x_1170_;
                v_x_1147_ = v_tail_1150_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11___redArg(
    mut v_i_1174_: *mut crate::leanh::LeanObject,
    mut v_source_1175_: *mut crate::leanh::LeanObject,
    mut v_target_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: u8 = 0;
    let mut v_es_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1177_ = lean_array_get_size(v_source_1175_);
                v___x_1178_ = lean_nat_dec_lt(v_i_1174_, v___x_1177_);
                if v___x_1178_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1175_);
                    crate::leanh::lean_dec(v_i_1174_);
                    return v_target_1176_;
                } else {
                    v_es_1179_ = lean_array_fget(v_source_1175_, v_i_1174_);
                    v___x_1180_ = crate::leanh::lean_box(0);
                    v_source_1181_ = lean_array_fset(v_source_1175_, v_i_1174_, v___x_1180_);
                    v_target_1182_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11_spec__12___redArg(v_target_1176_, v_es_1179_);
                    v___x_1183_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1184_ = lean_nat_add(v_i_1174_, v___x_1183_);
                    crate::leanh::lean_dec(v_i_1174_);
                    v_i_1174_ = v___x_1184_;
                    v_source_1175_ = v_source_1181_;
                    v_target_1176_ = v_target_1182_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(
    mut v_data_1186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1187_ = lean_array_get_size(v_data_1186_);
    v___x_1188_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1189_ = lean_nat_mul(v___x_1187_, v___x_1188_);
    v___x_1190_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1191_ = crate::leanh::lean_box(0);
    v___x_1192_ = lean_mk_array(v_nbuckets_1189_, v___x_1191_);
    v___x_1193_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11___redArg(v___x_1190_, v_data_1186_, v___x_1192_);
    return v___x_1193_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(
    mut v_m_1194_: *mut crate::leanh::LeanObject,
    mut v_a_1195_: *mut crate::leanh::LeanObject,
    mut v_b_1196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1201_: u8 = 0;
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: u64 = 0;
    let mut v___x_1204_: u64 = 0;
    let mut v___x_1205_: u64 = 0;
    let mut v_fold_1206_: u64 = 0;
    let mut v___x_1207_: u64 = 0;
    let mut v___x_1208_: u64 = 0;
    let mut v___x_1209_: u64 = 0;
    let mut v___x_1210_: usize = 0;
    let mut v___x_1211_: usize = 0;
    let mut v___x_1212_: usize = 0;
    let mut v___x_1213_: usize = 0;
    let mut v___x_1214_: usize = 0;
    let mut v_bkt_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: u8 = 0;
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: u8 = 0;
    let mut v_val_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1197_ = crate::leanh::lean_ctor_get(v_m_1194_, 0);
                v_buckets_1198_ = crate::leanh::lean_ctor_get(v_m_1194_, 1);
                v_isSharedCheck_1241_ = (!crate::leanh::lean_is_exclusive(v_m_1194_)) as u8;
                if v_isSharedCheck_1241_ == 0 {
                    v___x_1200_ = v_m_1194_;
                    v_isShared_1201_ = v_isSharedCheck_1241_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1198_);
                    crate::leanh::lean_inc(v_size_1197_);
                    crate::leanh::lean_dec(v_m_1194_);
                    v___x_1200_ = crate::leanh::lean_box(0);
                    v_isShared_1201_ = v_isSharedCheck_1241_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1202_ = lean_array_get_size(v_buckets_1198_);
                v___x_1203_ = l_Lean_Expr_hash(v_a_1195_);
                v___x_1204_ = 32u64;
                v___x_1205_ = lean_uint64_shift_right(v___x_1203_, v___x_1204_);
                v_fold_1206_ = lean_uint64_xor(v___x_1203_, v___x_1205_);
                v___x_1207_ = 16u64;
                v___x_1208_ = lean_uint64_shift_right(v_fold_1206_, v___x_1207_);
                v___x_1209_ = lean_uint64_xor(v_fold_1206_, v___x_1208_);
                v___x_1210_ = lean_uint64_to_usize(v___x_1209_);
                v___x_1211_ = lean_usize_of_nat(v___x_1202_);
                v___x_1212_ = 1usize;
                v___x_1213_ = lean_usize_sub(v___x_1211_, v___x_1212_);
                v___x_1214_ = lean_usize_land(v___x_1210_, v___x_1213_);
                v_bkt_1215_ = lean_array_uget_borrowed(v_buckets_1198_, v___x_1214_);
                v___x_1216_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_a_1195_, v_bkt_1215_);
                if v___x_1216_ == 0 {
                    v___x_1217_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1218_ = lean_nat_add(v_size_1197_, v___x_1217_);
                    crate::leanh::lean_dec(v_size_1197_);
                    crate::leanh::lean_inc(v_bkt_1215_);
                    v___x_1219_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1219_, 0, v_a_1195_);
                    crate::leanh::lean_ctor_set(v___x_1219_, 1, v_b_1196_);
                    crate::leanh::lean_ctor_set(v___x_1219_, 2, v_bkt_1215_);
                    v_buckets_x27_1220_ =
                        lean_array_uset(v_buckets_1198_, v___x_1214_, v___x_1219_);
                    v___x_1221_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1222_ = lean_nat_mul(v_size_x27_1218_, v___x_1221_);
                    v___x_1223_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1224_ = lean_nat_div(v___x_1222_, v___x_1223_);
                    crate::leanh::lean_dec(v___x_1222_);
                    v___x_1225_ = lean_array_get_size(v_buckets_x27_1220_);
                    v___x_1226_ = lean_nat_dec_le(v___x_1224_, v___x_1225_);
                    crate::leanh::lean_dec(v___x_1224_);
                    if v___x_1226_ == 0 {
                        v_val_1227_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(v_buckets_x27_1220_);
                        if v_isShared_1201_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1200_, 1, v_val_1227_);
                            crate::leanh::lean_ctor_set(v___x_1200_, 0, v_size_x27_1218_);
                            v___x_1229_ = v___x_1200_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1230_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1230_,
                                0,
                                v_size_x27_1218_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_val_1227_);
                            v___x_1229_ = v_reuseFailAlloc_1230_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1201_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1200_, 1, v_buckets_x27_1220_);
                            crate::leanh::lean_ctor_set(v___x_1200_, 0, v_size_x27_1218_);
                            v___x_1232_ = v___x_1200_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1233_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1233_,
                                0,
                                v_size_x27_1218_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1233_,
                                1,
                                v_buckets_x27_1220_,
                            );
                            v___x_1232_ = v_reuseFailAlloc_1233_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1215_);
                    v___x_1234_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1235_ =
                        lean_array_uset(v_buckets_1198_, v___x_1214_, v___x_1234_);
                    v___x_1236_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11___redArg(v_a_1195_, v_b_1196_, v_bkt_1215_);
                    v___x_1237_ = lean_array_uset(v_buckets_x27_1235_, v___x_1214_, v___x_1236_);
                    if v_isShared_1201_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1200_, 1, v___x_1237_);
                        v___x_1239_ = v___x_1200_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1240_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_size_1197_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 1, v___x_1237_);
                        v___x_1239_ = v_reuseFailAlloc_1240_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1229_;
            }
            3 => {
                return v___x_1232_;
            }
            4 => {
                return v___x_1239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1247_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1248_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1248_, 0, v___x_1247_);
    return v___x_1248_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3);
    v___x_1250_ = l_Lean_MessageData_ofFormat(v___x_1249_);
    return v___x_1250_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1251_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4);
    v___x_1252_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2;
    v___x_1253_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1253_, 0, v___x_1252_);
    crate::leanh::lean_ctor_set(v___x_1253_, 1, v___x_1251_);
    return v___x_1253_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(
    mut v_ref_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1256_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5);
    v___x_1257_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1257_, 0, v_ref_1254_);
    crate::leanh::lean_ctor_set(v___x_1257_, 1, v___x_1256_);
    v___x_1258_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1258_, 0, v___x_1257_);
    return v___x_1258_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___boxed(
    mut v_ref_1259_: *mut crate::leanh::LeanObject,
    mut v___y_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1261_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_1259_);
    return v_res_1261_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1262_ = crate::leanh::lean_box(0);
    v___x_1263_ = l_Lean_interruptExceptionId;
    v___x_1264_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1264_, 0, v___x_1263_);
    crate::leanh::lean_ctor_set(v___x_1264_, 1, v___x_1262_);
    return v___x_1264_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1266_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0);
    v___x_1267_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1266_);
    return v___x_1267_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___boxed(
    mut v___y_1268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1269_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg();
    return v_res_1269_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(
    mut v_x_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
    mut v___y_1273_: *mut crate::leanh::LeanObject,
    mut v___y_1274_: *mut crate::leanh::LeanObject,
    mut v___y_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1286_: u8 = 0;
    let mut v___y_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1295_: u8 = 0;
    let mut v___y_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1303_: u8 = 0;
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1320_: u8 = 0;
    let mut v_cancelTk_x3f_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1322_: u8 = 0;
    let mut v_inheritedTraceOptions_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: u8 = 0;
    let mut v___x_1327_: u8 = 0;
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: u8 = 0;
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1335_: u8 = 0;
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1339_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1308_ = crate::leanh::lean_ctor_get(v___y_1274_, 0);
                v_fileMap_1309_ = crate::leanh::lean_ctor_get(v___y_1274_, 1);
                v_options_1310_ = crate::leanh::lean_ctor_get(v___y_1274_, 2);
                v_currRecDepth_1311_ = crate::leanh::lean_ctor_get(v___y_1274_, 3);
                v_maxRecDepth_1312_ = crate::leanh::lean_ctor_get(v___y_1274_, 4);
                v_ref_1313_ = crate::leanh::lean_ctor_get(v___y_1274_, 5);
                v_currNamespace_1314_ = crate::leanh::lean_ctor_get(v___y_1274_, 6);
                v_openDecls_1315_ = crate::leanh::lean_ctor_get(v___y_1274_, 7);
                v_initHeartbeats_1316_ = crate::leanh::lean_ctor_get(v___y_1274_, 8);
                v_maxHeartbeats_1317_ = crate::leanh::lean_ctor_get(v___y_1274_, 9);
                v_quotContext_1318_ = crate::leanh::lean_ctor_get(v___y_1274_, 10);
                v_currMacroScope_1319_ = crate::leanh::lean_ctor_get(v___y_1274_, 11);
                v_diag_1320_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1274_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1321_ = crate::leanh::lean_ctor_get(v___y_1274_, 12);
                v_suppressElabErrors_1322_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1274_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1323_ = crate::leanh::lean_ctor_get(v___y_1274_, 13);
                if crate::leanh::lean_obj_tag(v_cancelTk_x3f_1321_) == 1 {
                    v_val_1329_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_1321_, 0);
                    v___x_1330_ = l_IO_CancelToken_isSet(v_val_1329_);
                    if v___x_1330_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_1270_);
                        v___x_1331_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg();
                        v_a_1332_ = crate::leanh::lean_ctor_get(v___x_1331_, 0);
                        v_isSharedCheck_1339_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1331_)) as u8;
                        if v_isSharedCheck_1339_ == 0 {
                            v___x_1334_ = v___x_1331_;
                            v_isShared_1335_ = v_isSharedCheck_1339_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1332_);
                            crate::leanh::lean_dec(v___x_1331_);
                            v___x_1334_ = crate::leanh::lean_box(0);
                            v_isShared_1335_ = v_isSharedCheck_1339_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    state = 5;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_1278_) == 0 {
                    return v___y_1278_;
                } else {
                    v_a_1279_ = crate::leanh::lean_ctor_get(v___y_1278_, 0);
                    v_isSharedCheck_1286_ = (!crate::leanh::lean_is_exclusive(v___y_1278_)) as u8;
                    if v_isSharedCheck_1286_ == 0 {
                        v___x_1281_ = v___y_1278_;
                        v_isShared_1282_ = v_isSharedCheck_1286_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1279_);
                        crate::leanh::lean_dec(v___y_1278_);
                        v___x_1281_ = crate::leanh::lean_box(0);
                        v_isShared_1282_ = v_isSharedCheck_1286_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1282_ == 0 {
                    v___x_1284_ = v___x_1281_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
                    v___x_1284_ = v_reuseFailAlloc_1285_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1284_;
            }
            4 => {
                v___x_1304_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1305_ = lean_nat_add(v___y_1289_, v___x_1304_);
                crate::leanh::lean_inc_ref(v___y_1294_);
                crate::leanh::lean_inc(v___y_1302_);
                crate::leanh::lean_inc(v___y_1298_);
                crate::leanh::lean_inc(v___y_1297_);
                crate::leanh::lean_inc(v___y_1296_);
                crate::leanh::lean_inc(v___y_1288_);
                crate::leanh::lean_inc(v___y_1301_);
                crate::leanh::lean_inc(v___y_1293_);
                crate::leanh::lean_inc(v___y_1300_);
                crate::leanh::lean_inc_ref(v___y_1299_);
                crate::leanh::lean_inc_ref(v___y_1292_);
                crate::leanh::lean_inc_ref(v___y_1291_);
                v___x_1306_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1306_, 0, v___y_1291_);
                crate::leanh::lean_ctor_set(v___x_1306_, 1, v___y_1292_);
                crate::leanh::lean_ctor_set(v___x_1306_, 2, v___y_1299_);
                crate::leanh::lean_ctor_set(v___x_1306_, 3, v___x_1305_);
                crate::leanh::lean_ctor_set(v___x_1306_, 4, v___y_1300_);
                crate::leanh::lean_ctor_set(v___x_1306_, 5, v___y_1290_);
                crate::leanh::lean_ctor_set(v___x_1306_, 6, v___y_1293_);
                crate::leanh::lean_ctor_set(v___x_1306_, 7, v___y_1301_);
                crate::leanh::lean_ctor_set(v___x_1306_, 8, v___y_1288_);
                crate::leanh::lean_ctor_set(v___x_1306_, 9, v___y_1296_);
                crate::leanh::lean_ctor_set(v___x_1306_, 10, v___y_1297_);
                crate::leanh::lean_ctor_set(v___x_1306_, 11, v___y_1298_);
                crate::leanh::lean_ctor_set(v___x_1306_, 12, v___y_1302_);
                crate::leanh::lean_ctor_set(v___x_1306_, 13, v___y_1294_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1306_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___y_1303_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1306_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_1295_,
                );
                crate::leanh::lean_inc(v___y_1275_);
                crate::leanh::lean_inc(v___y_1273_);
                crate::leanh::lean_inc_ref(v___y_1272_);
                crate::leanh::lean_inc(v___y_1271_);
                v___x_1307_ = crate::leanh::lean_apply_6(
                    v_x_1270_,
                    v___y_1271_,
                    v___y_1272_,
                    v___y_1273_,
                    v___x_1306_,
                    v___y_1275_,
                    crate::leanh::lean_box(0),
                );
                v___y_1278_ = v___x_1307_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1325_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1326_ = lean_nat_dec_eq(v_maxRecDepth_1312_, v___x_1325_);
                if v___x_1326_ == 0 {
                    v___x_1327_ = lean_nat_dec_eq(v_currRecDepth_1311_, v_maxRecDepth_1312_);
                    if v___x_1327_ == 0 {
                        crate::leanh::lean_inc(v_ref_1313_);
                        v___y_1288_ = v_initHeartbeats_1316_;
                        v___y_1289_ = v_currRecDepth_1311_;
                        v___y_1290_ = v_ref_1313_;
                        v___y_1291_ = v_fileName_1308_;
                        v___y_1292_ = v_fileMap_1309_;
                        v___y_1293_ = v_currNamespace_1314_;
                        v___y_1294_ = v_inheritedTraceOptions_1323_;
                        v___y_1295_ = v_suppressElabErrors_1322_;
                        v___y_1296_ = v_maxHeartbeats_1317_;
                        v___y_1297_ = v_quotContext_1318_;
                        v___y_1298_ = v_currMacroScope_1319_;
                        v___y_1299_ = v_options_1310_;
                        v___y_1300_ = v_maxRecDepth_1312_;
                        v___y_1301_ = v_openDecls_1315_;
                        v___y_1302_ = v_cancelTk_x3f_1321_;
                        v___y_1303_ = v_diag_1320_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_1270_);
                        crate::leanh::lean_inc(v_ref_1313_);
                        v___x_1328_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_1313_);
                        v___y_1278_ = v___x_1328_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_ref_1313_);
                    v___y_1288_ = v_initHeartbeats_1316_;
                    v___y_1289_ = v_currRecDepth_1311_;
                    v___y_1290_ = v_ref_1313_;
                    v___y_1291_ = v_fileName_1308_;
                    v___y_1292_ = v_fileMap_1309_;
                    v___y_1293_ = v_currNamespace_1314_;
                    v___y_1294_ = v_inheritedTraceOptions_1323_;
                    v___y_1295_ = v_suppressElabErrors_1322_;
                    v___y_1296_ = v_maxHeartbeats_1317_;
                    v___y_1297_ = v_quotContext_1318_;
                    v___y_1298_ = v_currMacroScope_1319_;
                    v___y_1299_ = v_options_1310_;
                    v___y_1300_ = v_maxRecDepth_1312_;
                    v___y_1301_ = v_openDecls_1315_;
                    v___y_1302_ = v_cancelTk_x3f_1321_;
                    v___y_1303_ = v_diag_1320_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v_isShared_1335_ == 0 {
                    v___x_1337_ = v___x_1334_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1338_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
                    v___x_1337_ = v_reuseFailAlloc_1338_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1337_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg___boxed(
    mut v_x_1340_: *mut crate::leanh::LeanObject,
    mut v___y_1341_: *mut crate::leanh::LeanObject,
    mut v___y_1342_: *mut crate::leanh::LeanObject,
    mut v___y_1343_: *mut crate::leanh::LeanObject,
    mut v___y_1344_: *mut crate::leanh::LeanObject,
    mut v___y_1345_: *mut crate::leanh::LeanObject,
    mut v___y_1346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1347_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v_x_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
    crate::leanh::lean_dec(v___y_1345_);
    crate::leanh::lean_dec_ref(v___y_1344_);
    crate::leanh::lean_dec(v___y_1343_);
    crate::leanh::lean_dec_ref(v___y_1342_);
    crate::leanh::lean_dec(v___y_1341_);
    return v_res_1347_;
}
pub unsafe fn _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1351_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2;
    v___x_1352_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_1353_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_1354_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1;
    v___x_1355_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0;
    v___x_1356_ = l_mkPanicMessageWithDecl(
        v___x_1355_,
        v___x_1354_,
        v___x_1353_,
        v___x_1352_,
        v___x_1351_,
    );
    return v___x_1356_;
}
pub unsafe fn _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = crate::leanh::lean_box(0);
    v_dummy_1358_ = l_Lean_Expr_sort___override(v___x_1357_);
    return v_dummy_1358_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(
    mut v_explicitOnly_1359_: u8,
    mut v_skipTypes_1360_: u8,
    mut v_skipProofs_1361_: u8,
    mut v_upperBound_1362_: *mut crate::leanh::LeanObject,
    mut v_a_1363_: *mut crate::leanh::LeanObject,
    mut v_a_1364_: u8,
    mut v_a_1365_: *mut crate::leanh::LeanObject,
    mut v_b_1366_: *mut crate::leanh::LeanObject,
    mut v___y_1367_: *mut crate::leanh::LeanObject,
    mut v___y_1368_: *mut crate::leanh::LeanObject,
    mut v___y_1369_: *mut crate::leanh::LeanObject,
    mut v___y_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v_v_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1394_: u8 = 0;
    let mut v___x_1395_: u8 = 0;
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: u8 = 0;
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: u8 = 0;
    let mut v_v_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1415_: u8 = 0;
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1395_ = lean_nat_dec_lt(v_a_1365_, v_upperBound_1362_);
                if v___x_1395_ == 0 {
                    crate::leanh::lean_dec(v_a_1365_);
                    v___x_1396_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1396_, 0, v_b_1366_);
                    return v___x_1396_;
                } else {
                    v_paramInfo_1397_ = crate::leanh::lean_ctor_get(v_a_1363_, 0);
                    v___x_1398_ = lean_array_get_size(v_paramInfo_1397_);
                    v___x_1399_ = lean_nat_dec_lt(v_a_1365_, v___x_1398_);
                    if v___x_1399_ == 0 {
                        v___x_1400_ = lean_array_get_size(v_b_1366_);
                        v___x_1401_ = lean_nat_dec_lt(v_a_1365_, v___x_1400_);
                        if v___x_1401_ == 0 {
                            v_a_1374_ = v_b_1366_;
                            state = 1;
                            continue;
                        } else {
                            v_v_1402_ = lean_array_fget_borrowed(v_b_1366_, v_a_1365_);
                            crate::leanh::lean_inc(v_v_1402_);
                            v___x_1403_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(
                                v_explicitOnly_1359_,
                                v_skipTypes_1360_,
                                v_skipProofs_1361_,
                                v_v_1402_,
                                v___y_1367_,
                                v___y_1368_,
                                v___y_1369_,
                                v___y_1370_,
                                v___y_1371_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1403_) == 0 {
                                v_a_1404_ = crate::leanh::lean_ctor_get(v___x_1403_, 0);
                                crate::leanh::lean_inc(v_a_1404_);
                                crate::leanh::lean_dec_ref_known(v___x_1403_, 1);
                                v___x_1405_ = crate::leanh::lean_box(0);
                                v_xs_x27_1406_ = lean_array_fset(v_b_1366_, v_a_1365_, v___x_1405_);
                                v___x_1407_ = lean_array_fset(v_xs_x27_1406_, v_a_1365_, v_a_1404_);
                                v_a_1374_ = v___x_1407_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_b_1366_);
                                crate::leanh::lean_dec(v_a_1365_);
                                v_a_1408_ = crate::leanh::lean_ctor_get(v___x_1403_, 0);
                                v_isSharedCheck_1415_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1403_)) as u8;
                                if v_isSharedCheck_1415_ == 0 {
                                    v___x_1410_ = v___x_1403_;
                                    v_isShared_1411_ = v_isSharedCheck_1415_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1408_);
                                    crate::leanh::lean_dec(v___x_1403_);
                                    v___x_1410_ = crate::leanh::lean_box(0);
                                    v_isShared_1411_ = v_isSharedCheck_1415_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        if v_explicitOnly_1359_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            if v_a_1364_ == 0 {
                                v___x_1416_ =
                                    lean_array_fget_borrowed(v_paramInfo_1397_, v_a_1365_);
                                v___x_1417_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_1416_);
                                if v___x_1417_ == 0 {
                                    v_a_1374_ = v_b_1366_;
                                    state = 1;
                                    continue;
                                } else {
                                    state = 2;
                                    continue;
                                }
                            } else {
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1375_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1376_ = lean_nat_add(v_a_1365_, v___x_1375_);
                crate::leanh::lean_dec(v_a_1365_);
                v_a_1365_ = v___x_1376_;
                v_b_1366_ = v_a_1374_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1379_ = lean_array_get_size(v_b_1366_);
                v___x_1380_ = lean_nat_dec_lt(v_a_1365_, v___x_1379_);
                if v___x_1380_ == 0 {
                    v_a_1374_ = v_b_1366_;
                    state = 1;
                    continue;
                } else {
                    v_v_1381_ = lean_array_fget_borrowed(v_b_1366_, v_a_1365_);
                    crate::leanh::lean_inc(v_v_1381_);
                    v___x_1382_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(
                        v_explicitOnly_1359_,
                        v_skipTypes_1360_,
                        v_skipProofs_1361_,
                        v_v_1381_,
                        v___y_1367_,
                        v___y_1368_,
                        v___y_1369_,
                        v___y_1370_,
                        v___y_1371_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1382_) == 0 {
                        v_a_1383_ = crate::leanh::lean_ctor_get(v___x_1382_, 0);
                        crate::leanh::lean_inc(v_a_1383_);
                        crate::leanh::lean_dec_ref_known(v___x_1382_, 1);
                        v___x_1384_ = crate::leanh::lean_box(0);
                        v_xs_x27_1385_ = lean_array_fset(v_b_1366_, v_a_1365_, v___x_1384_);
                        v___x_1386_ = lean_array_fset(v_xs_x27_1385_, v_a_1365_, v_a_1383_);
                        v_a_1374_ = v___x_1386_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_1366_);
                        crate::leanh::lean_dec(v_a_1365_);
                        v_a_1387_ = crate::leanh::lean_ctor_get(v___x_1382_, 0);
                        v_isSharedCheck_1394_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1382_)) as u8;
                        if v_isSharedCheck_1394_ == 0 {
                            v___x_1389_ = v___x_1382_;
                            v_isShared_1390_ = v_isSharedCheck_1394_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1387_);
                            crate::leanh::lean_dec(v___x_1382_);
                            v___x_1389_ = crate::leanh::lean_box(0);
                            v_isShared_1390_ = v_isSharedCheck_1394_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_1390_ == 0 {
                    v___x_1392_ = v___x_1389_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1393_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
                    v___x_1392_ = v_reuseFailAlloc_1393_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1392_;
            }
            5 => {
                if v_isShared_1411_ == 0 {
                    v___x_1413_ = v___x_1410_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
                    v___x_1413_ = v_reuseFailAlloc_1414_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed(
    mut v_explicitOnly_1423_: *mut crate::leanh::LeanObject,
    mut v_skipTypes_1424_: *mut crate::leanh::LeanObject,
    mut v_skipProofs_1425_: *mut crate::leanh::LeanObject,
    mut v_a_1426_: *mut crate::leanh::LeanObject,
    mut v___x_1427_: *mut crate::leanh::LeanObject,
    mut v_xs_1428_: *mut crate::leanh::LeanObject,
    mut v_b_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
    mut v___y_1435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_explicitOnly_boxed_1436_: u8 = 0;
    let mut v_skipTypes_boxed_1437_: u8 = 0;
    let mut v_skipProofs_boxed_1438_: u8 = 0;
    let mut v_a_16743__boxed_1439_: u8 = 0;
    let mut v___x_16744__boxed_1440_: u8 = 0;
    let mut v_res_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_explicitOnly_boxed_1436_ = (crate::leanh::lean_unbox(v_explicitOnly_1423_) as u8);
    v_skipTypes_boxed_1437_ = (crate::leanh::lean_unbox(v_skipTypes_1424_) as u8);
    v_skipProofs_boxed_1438_ = (crate::leanh::lean_unbox(v_skipProofs_1425_) as u8);
    v_a_16743__boxed_1439_ = (crate::leanh::lean_unbox(v_a_1426_) as u8);
    v___x_16744__boxed_1440_ = (crate::leanh::lean_unbox(v___x_1427_) as u8);
    v_res_1441_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(
        v_explicitOnly_boxed_1436_,
        v_skipTypes_boxed_1437_,
        v_skipProofs_boxed_1438_,
        v_a_16743__boxed_1439_,
        v___x_16744__boxed_1440_,
        v_xs_1428_,
        v_b_1429_,
        v___y_1430_,
        v___y_1431_,
        v___y_1432_,
        v___y_1433_,
        v___y_1434_,
    );
    crate::leanh::lean_dec(v___y_1434_);
    crate::leanh::lean_dec_ref(v___y_1433_);
    crate::leanh::lean_dec(v___y_1432_);
    crate::leanh::lean_dec_ref(v___y_1431_);
    crate::leanh::lean_dec(v___y_1430_);
    crate::leanh::lean_dec_ref(v_xs_1428_);
    return v_res_1441_;
}
pub unsafe fn l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(
    mut v_explicitOnly_1442_: u8,
    mut v_skipTypes_1443_: u8,
    mut v_skipProofs_1444_: u8,
    mut v_a_1445_: u8,
    mut v___x_1446_: u8,
    mut v_xs_1447_: *mut crate::leanh::LeanObject,
    mut v_b_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
    mut v___y_1452_: *mut crate::leanh::LeanObject,
    mut v___y_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1455_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(
        v_explicitOnly_1442_,
        v_skipTypes_1443_,
        v_skipProofs_1444_,
        v_b_1448_,
        v___y_1449_,
        v___y_1450_,
        v___y_1451_,
        v___y_1452_,
        v___y_1453_,
    );
    if crate::leanh::lean_obj_tag(v___x_1455_) == 0 {
        let mut v_a_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1457_: u8 = 0;
        let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1456_ = crate::leanh::lean_ctor_get(v___x_1455_, 0);
        crate::leanh::lean_inc(v_a_1456_);
        crate::leanh::lean_dec_ref_known(v___x_1455_, 1);
        v___x_1457_ = 1;
        v___x_1458_ = l_Lean_Meta_mkForallFVars(
            v_xs_1447_,
            v_a_1456_,
            v_a_1445_,
            v___x_1446_,
            v___x_1446_,
            v___x_1457_,
            v___y_1450_,
            v___y_1451_,
            v___y_1452_,
            v___y_1453_,
        );
        return v___x_1458_;
    } else {
        return v___x_1455_;
    }
}
pub unsafe fn l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed(
    mut v_explicitOnly_1459_: *mut crate::leanh::LeanObject,
    mut v_skipTypes_1460_: *mut crate::leanh::LeanObject,
    mut v_skipProofs_1461_: *mut crate::leanh::LeanObject,
    mut v_a_1462_: *mut crate::leanh::LeanObject,
    mut v___x_1463_: *mut crate::leanh::LeanObject,
    mut v_xs_1464_: *mut crate::leanh::LeanObject,
    mut v_b_1465_: *mut crate::leanh::LeanObject,
    mut v___y_1466_: *mut crate::leanh::LeanObject,
    mut v___y_1467_: *mut crate::leanh::LeanObject,
    mut v___y_1468_: *mut crate::leanh::LeanObject,
    mut v___y_1469_: *mut crate::leanh::LeanObject,
    mut v___y_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_explicitOnly_boxed_1472_: u8 = 0;
    let mut v_skipTypes_boxed_1473_: u8 = 0;
    let mut v_skipProofs_boxed_1474_: u8 = 0;
    let mut v_a_16756__boxed_1475_: u8 = 0;
    let mut v___x_16757__boxed_1476_: u8 = 0;
    let mut v_res_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_explicitOnly_boxed_1472_ = (crate::leanh::lean_unbox(v_explicitOnly_1459_) as u8);
    v_skipTypes_boxed_1473_ = (crate::leanh::lean_unbox(v_skipTypes_1460_) as u8);
    v_skipProofs_boxed_1474_ = (crate::leanh::lean_unbox(v_skipProofs_1461_) as u8);
    v_a_16756__boxed_1475_ = (crate::leanh::lean_unbox(v_a_1462_) as u8);
    v___x_16757__boxed_1476_ = (crate::leanh::lean_unbox(v___x_1463_) as u8);
    v_res_1477_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(
        v_explicitOnly_boxed_1472_,
        v_skipTypes_boxed_1473_,
        v_skipProofs_boxed_1474_,
        v_a_16756__boxed_1475_,
        v___x_16757__boxed_1476_,
        v_xs_1464_,
        v_b_1465_,
        v___y_1466_,
        v___y_1467_,
        v___y_1468_,
        v___y_1469_,
        v___y_1470_,
    );
    crate::leanh::lean_dec(v___y_1470_);
    crate::leanh::lean_dec_ref(v___y_1469_);
    crate::leanh::lean_dec(v___y_1468_);
    crate::leanh::lean_dec_ref(v___y_1467_);
    crate::leanh::lean_dec(v___y_1466_);
    crate::leanh::lean_dec_ref(v_xs_1464_);
    return v_res_1477_;
}
pub unsafe fn l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(
    mut v_e_1478_: *mut crate::leanh::LeanObject,
    mut v_explicitOnly_1479_: u8,
    mut v_skipTypes_1480_: u8,
    mut v_skipProofs_1481_: u8,
    mut v___y_1482_: *mut crate::leanh::LeanObject,
    mut v___y_1483_: *mut crate::leanh::LeanObject,
    mut v___y_1484_: *mut crate::leanh::LeanObject,
    mut v___y_1485_: *mut crate::leanh::LeanObject,
    mut v___y_1486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1502_: u8 = 0;
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1512_: u8 = 0;
    let mut v_a_1513_: u8 = 0;
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: u8 = 0;
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: u8 = 0;
    let mut v_a_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1538_: u8 = 0;
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1542_: u8 = 0;
    let mut v_a_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1546_: u8 = 0;
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1550_: u8 = 0;
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1572_: u8 = 0;
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1577_: u8 = 0;
    let mut v___x_1579_: u8 = 0;
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1584_: u8 = 0;
    let mut v___x_1585_: u8 = 0;
    let mut v___x_1586_: u8 = 0;
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut v_a_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1594_: u8 = 0;
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1598_: u8 = 0;
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v___x_1604_: u8 = 0;
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1608_: u8 = 0;
    let mut v_a_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1616_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_skipTypes_1480_ == 0 {
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_e_1478_);
                    v___x_1599_ = l_Lean_Meta_isType(
                        v_e_1478_,
                        v___y_1483_,
                        v___y_1484_,
                        v___y_1485_,
                        v___y_1486_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1599_) == 0 {
                        v_a_1600_ = crate::leanh::lean_ctor_get(v___x_1599_, 0);
                        v_isSharedCheck_1608_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1599_)) as u8;
                        if v_isSharedCheck_1608_ == 0 {
                            v___x_1602_ = v___x_1599_;
                            v_isShared_1603_ = v_isSharedCheck_1608_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1600_);
                            crate::leanh::lean_dec(v___x_1599_);
                            v___x_1602_ = crate::leanh::lean_box(0);
                            v_isShared_1603_ = v_isSharedCheck_1608_;
                            state = 16;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1478_);
                        v_a_1609_ = crate::leanh::lean_ctor_get(v___x_1599_, 0);
                        v_isSharedCheck_1616_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1599_)) as u8;
                        if v_isSharedCheck_1616_ == 0 {
                            v___x_1611_ = v___x_1599_;
                            v_isShared_1612_ = v_isSharedCheck_1616_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1609_);
                            crate::leanh::lean_dec(v___x_1599_);
                            v___x_1611_ = crate::leanh::lean_box(0);
                            v_isShared_1612_ = v_isSharedCheck_1616_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1491_ = l_Lean_mkAppN(v___y_1489_, v___y_1490_);
                crate::leanh::lean_dec_ref(v___y_1490_);
                v___x_1492_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1492_, 0, v___x_1491_);
                return v___x_1492_;
            }
            2 => {
                v___x_1495_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1496_ = lean_nat_add(v___y_1494_, v___x_1495_);
                crate::leanh::lean_dec(v___y_1494_);
                v___x_1497_ = l_Lean_mkRawNatLit(v___x_1496_);
                v___x_1498_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1498_, 0, v___x_1497_);
                return v___x_1498_;
            }
            3 => {
                if v___y_1502_ == 0 {
                    v___y_1489_ = v___y_1500_;
                    v___y_1490_ = v___y_1501_;
                    state = 1;
                    continue;
                } else {
                    v___x_1503_ = l_Lean_instInhabitedExpr;
                    v___x_1504_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1505_ = lean_array_get_borrowed(v___x_1503_, v___y_1501_, v___x_1504_);
                    v___x_1506_ = l_Lean_Expr_isRawNatLit(v___x_1505_);
                    if v___x_1506_ == 0 {
                        v___y_1489_ = v___y_1500_;
                        v___y_1490_ = v___y_1501_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_1505_);
                        crate::leanh::lean_dec_ref(v___y_1501_);
                        crate::leanh::lean_dec_ref(v___y_1500_);
                        v___x_1507_ = l_Lean_Expr_rawNatLit_x3f(v___x_1505_);
                        if crate::leanh::lean_obj_tag(v___x_1507_) == 0 {
                            v___x_1508_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3_once), _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3);
                            v___x_1509_ = l_panic___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__1(v___x_1508_);
                            v___y_1494_ = v___x_1509_;
                            state = 2;
                            continue;
                        } else {
                            v_val_1510_ = crate::leanh::lean_ctor_get(v___x_1507_, 0);
                            crate::leanh::lean_inc(v_val_1510_);
                            crate::leanh::lean_dec_ref_known(v___x_1507_, 1);
                            v___y_1494_ = v_val_1510_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            4 => {
                crate::leanh::lean_inc(v___y_1486_);
                crate::leanh::lean_inc_ref(v___y_1485_);
                crate::leanh::lean_inc(v___y_1484_);
                crate::leanh::lean_inc_ref(v___y_1483_);
                v___x_1514_ = lean_whnf(
                    v_e_1478_,
                    v___y_1483_,
                    v___y_1484_,
                    v___y_1485_,
                    v___y_1486_,
                );
                if crate::leanh::lean_obj_tag(v___x_1514_) == 0 {
                    v_a_1515_ = crate::leanh::lean_ctor_get(v___x_1514_, 0);
                    crate::leanh::lean_inc(v_a_1515_);
                    match crate::leanh::lean_obj_tag(v_a_1515_) {
                        5 => {
                            crate::leanh::lean_dec_ref_known(v___x_1514_, 1);
                            v___x_1516_ = l_Lean_Expr_getAppFn(v_a_1515_);
                            v___x_1517_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(
                                v_explicitOnly_1479_,
                                v_skipTypes_1480_,
                                v_skipProofs_1481_,
                                v___x_1516_,
                                v___y_1482_,
                                v___y_1483_,
                                v___y_1484_,
                                v___y_1485_,
                                v___y_1486_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1517_) == 0 {
                                v_a_1518_ = crate::leanh::lean_ctor_get(v___x_1517_, 0);
                                crate::leanh::lean_inc_n(v_a_1518_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_1517_, 1);
                                v___x_1519_ = l_Lean_Expr_getAppNumArgs(v_a_1515_);
                                crate::leanh::lean_inc(v___x_1519_);
                                v___x_1520_ = l_Lean_Meta_getFunInfoNArgs(
                                    v_a_1518_,
                                    v___x_1519_,
                                    v___y_1483_,
                                    v___y_1484_,
                                    v___y_1485_,
                                    v___y_1486_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1520_) == 0 {
                                    v_a_1521_ = crate::leanh::lean_ctor_get(v___x_1520_, 0);
                                    crate::leanh::lean_inc(v_a_1521_);
                                    crate::leanh::lean_dec_ref_known(v___x_1520_, 1);
                                    v_dummy_1522_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4_once), _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4);
                                    crate::leanh::lean_inc(v___x_1519_);
                                    v___x_1523_ = lean_mk_array(v___x_1519_, v_dummy_1522_);
                                    v___x_1524_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_1525_ = lean_nat_sub(v___x_1519_, v___x_1524_);
                                    crate::leanh::lean_dec(v___x_1519_);
                                    v___x_1526_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                        v_a_1515_,
                                        v___x_1523_,
                                        v___x_1525_,
                                    );
                                    v___x_1527_ = lean_array_get_size(v___x_1526_);
                                    v___x_1528_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v___x_1529_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_1479_, v_skipTypes_1480_, v_skipProofs_1481_, v___x_1527_, v_a_1521_, v_a_1513_, v___x_1528_, v___x_1526_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
                                    crate::leanh::lean_dec(v_a_1521_);
                                    if crate::leanh::lean_obj_tag(v___x_1529_) == 0 {
                                        v_a_1530_ = crate::leanh::lean_ctor_get(v___x_1529_, 0);
                                        crate::leanh::lean_inc(v_a_1530_);
                                        crate::leanh::lean_dec_ref_known(v___x_1529_, 1);
                                        v___x_1531_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7;
                                        v___x_1532_ = l_Lean_Expr_isConstOf(v_a_1518_, v___x_1531_);
                                        if v___x_1532_ == 0 {
                                            v___y_1500_ = v_a_1518_;
                                            v___y_1501_ = v_a_1530_;
                                            v___y_1502_ = v___x_1532_;
                                            state = 3;
                                            continue;
                                        } else {
                                            v___x_1533_ = lean_array_get_size(v_a_1530_);
                                            v___x_1534_ = lean_nat_dec_eq(v___x_1533_, v___x_1524_);
                                            v___y_1500_ = v_a_1518_;
                                            v___y_1501_ = v_a_1530_;
                                            v___y_1502_ = v___x_1534_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_1518_);
                                        v_a_1535_ = crate::leanh::lean_ctor_get(v___x_1529_, 0);
                                        v_isSharedCheck_1542_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1529_)) as u8;
                                        if v_isSharedCheck_1542_ == 0 {
                                            v___x_1537_ = v___x_1529_;
                                            v_isShared_1538_ = v_isSharedCheck_1542_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1535_);
                                            crate::leanh::lean_dec(v___x_1529_);
                                            v___x_1537_ = crate::leanh::lean_box(0);
                                            v_isShared_1538_ = v_isSharedCheck_1542_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_1519_);
                                    crate::leanh::lean_dec(v_a_1518_);
                                    crate::leanh::lean_dec_ref_known(v_a_1515_, 2);
                                    v_a_1543_ = crate::leanh::lean_ctor_get(v___x_1520_, 0);
                                    v_isSharedCheck_1550_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1520_)) as u8;
                                    if v_isSharedCheck_1550_ == 0 {
                                        v___x_1545_ = v___x_1520_;
                                        v_isShared_1546_ = v_isSharedCheck_1550_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1543_);
                                        crate::leanh::lean_dec(v___x_1520_);
                                        v___x_1545_ = crate::leanh::lean_box(0);
                                        v_isShared_1546_ = v_isSharedCheck_1550_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_a_1515_, 2);
                                return v___x_1517_;
                            }
                        }
                        6 => {
                            crate::leanh::lean_dec_ref_known(v___x_1514_, 1);
                            v___x_1551_ = crate::leanh::lean_box((v_explicitOnly_1479_) as usize);
                            v___x_1552_ = crate::leanh::lean_box((v_skipTypes_1480_) as usize);
                            v___x_1553_ = crate::leanh::lean_box((v_skipProofs_1481_) as usize);
                            v___x_1554_ = crate::leanh::lean_box((v_a_1513_) as usize);
                            v___x_1555_ = crate::leanh::lean_box((v___y_1512_) as usize);
                            v___f_1556_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed as *mut core::ffi::c_void, 13, 5);
                            crate::leanh::lean_closure_set(v___f_1556_, 0, v___x_1551_);
                            crate::leanh::lean_closure_set(v___f_1556_, 1, v___x_1552_);
                            crate::leanh::lean_closure_set(v___f_1556_, 2, v___x_1553_);
                            crate::leanh::lean_closure_set(v___f_1556_, 3, v___x_1554_);
                            crate::leanh::lean_closure_set(v___f_1556_, 4, v___x_1555_);
                            v___x_1557_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(v_a_1515_, v___f_1556_, v_a_1513_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
                            return v___x_1557_;
                        }
                        7 => {
                            crate::leanh::lean_dec_ref_known(v___x_1514_, 1);
                            v___x_1558_ = crate::leanh::lean_box((v_explicitOnly_1479_) as usize);
                            v___x_1559_ = crate::leanh::lean_box((v_skipTypes_1480_) as usize);
                            v___x_1560_ = crate::leanh::lean_box((v_skipProofs_1481_) as usize);
                            v___x_1561_ = crate::leanh::lean_box((v_a_1513_) as usize);
                            v___x_1562_ = crate::leanh::lean_box((v___y_1512_) as usize);
                            v___f_1563_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed as *mut core::ffi::c_void, 13, 5);
                            crate::leanh::lean_closure_set(v___f_1563_, 0, v___x_1558_);
                            crate::leanh::lean_closure_set(v___f_1563_, 1, v___x_1559_);
                            crate::leanh::lean_closure_set(v___f_1563_, 2, v___x_1560_);
                            crate::leanh::lean_closure_set(v___f_1563_, 3, v___x_1561_);
                            crate::leanh::lean_closure_set(v___f_1563_, 4, v___x_1562_);
                            v___x_1564_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(v_a_1515_, v___f_1563_, v_a_1513_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
                            return v___x_1564_;
                        }
                        11 => {
                            crate::leanh::lean_dec_ref_known(v___x_1514_, 1);
                            v_typeName_1565_ = crate::leanh::lean_ctor_get(v_a_1515_, 0);
                            crate::leanh::lean_inc(v_typeName_1565_);
                            v_idx_1566_ = crate::leanh::lean_ctor_get(v_a_1515_, 1);
                            crate::leanh::lean_inc(v_idx_1566_);
                            v_struct_1567_ = crate::leanh::lean_ctor_get(v_a_1515_, 2);
                            crate::leanh::lean_inc_ref(v_struct_1567_);
                            crate::leanh::lean_dec_ref_known(v_a_1515_, 3);
                            v___x_1568_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(
                                v_explicitOnly_1479_,
                                v_skipTypes_1480_,
                                v_skipProofs_1481_,
                                v_struct_1567_,
                                v___y_1482_,
                                v___y_1483_,
                                v___y_1484_,
                                v___y_1485_,
                                v___y_1486_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1568_) == 0 {
                                v_a_1569_ = crate::leanh::lean_ctor_get(v___x_1568_, 0);
                                v_isSharedCheck_1577_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1568_)) as u8;
                                if v_isSharedCheck_1577_ == 0 {
                                    v___x_1571_ = v___x_1568_;
                                    v_isShared_1572_ = v_isSharedCheck_1577_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1569_);
                                    crate::leanh::lean_dec(v___x_1568_);
                                    v___x_1571_ = crate::leanh::lean_box(0);
                                    v_isShared_1572_ = v_isSharedCheck_1577_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_idx_1566_);
                                crate::leanh::lean_dec(v_typeName_1565_);
                                return v___x_1568_;
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec(v_a_1515_);
                            return v___x_1514_;
                        }
                    }
                } else {
                    return v___x_1514_;
                }
            }
            5 => {
                if v_isShared_1538_ == 0 {
                    v___x_1540_ = v___x_1537_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
                    v___x_1540_ = v_reuseFailAlloc_1541_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1540_;
            }
            7 => {
                if v_isShared_1546_ == 0 {
                    v___x_1548_ = v___x_1545_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
                    v___x_1548_ = v_reuseFailAlloc_1549_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1548_;
            }
            9 => {
                v___x_1573_ = l_Lean_mkProj(v_typeName_1565_, v_idx_1566_, v_a_1569_);
                if v_isShared_1572_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1571_, 0, v___x_1573_);
                    v___x_1575_ = v___x_1571_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1576_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
                    v___x_1575_ = v_reuseFailAlloc_1576_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1575_;
            }
            11 => {
                v___x_1579_ = 1;
                if v_skipProofs_1481_ == 0 {
                    v___y_1512_ = v___x_1579_;
                    v_a_1513_ = v_skipProofs_1481_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_e_1478_);
                    v___x_1580_ = l_Lean_Meta_isProof(
                        v_e_1478_,
                        v___y_1483_,
                        v___y_1484_,
                        v___y_1485_,
                        v___y_1486_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1580_) == 0 {
                        v_a_1581_ = crate::leanh::lean_ctor_get(v___x_1580_, 0);
                        v_isSharedCheck_1590_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1580_)) as u8;
                        if v_isSharedCheck_1590_ == 0 {
                            v___x_1583_ = v___x_1580_;
                            v_isShared_1584_ = v_isSharedCheck_1590_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1581_);
                            crate::leanh::lean_dec(v___x_1580_);
                            v___x_1583_ = crate::leanh::lean_box(0);
                            v_isShared_1584_ = v_isSharedCheck_1590_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1478_);
                        v_a_1591_ = crate::leanh::lean_ctor_get(v___x_1580_, 0);
                        v_isSharedCheck_1598_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1580_)) as u8;
                        if v_isSharedCheck_1598_ == 0 {
                            v___x_1593_ = v___x_1580_;
                            v_isShared_1594_ = v_isSharedCheck_1598_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1591_);
                            crate::leanh::lean_dec(v___x_1580_);
                            v___x_1593_ = crate::leanh::lean_box(0);
                            v_isShared_1594_ = v_isSharedCheck_1598_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            12 => {
                v___x_1585_ = (crate::leanh::lean_unbox(v_a_1581_) as u8);
                if v___x_1585_ == 0 {
                    crate::leanh::lean_del_object(v___x_1583_);
                    v___x_1586_ = (crate::leanh::lean_unbox(v_a_1581_) as u8);
                    crate::leanh::lean_dec(v_a_1581_);
                    v___y_1512_ = v___x_1579_;
                    v_a_1513_ = v___x_1586_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1581_);
                    if v_isShared_1584_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1583_, 0, v_e_1478_);
                        v___x_1588_ = v___x_1583_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_1589_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_e_1478_);
                        v___x_1588_ = v_reuseFailAlloc_1589_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                return v___x_1588_;
            }
            14 => {
                if v_isShared_1594_ == 0 {
                    v___x_1596_ = v___x_1593_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
                    v___x_1596_ = v_reuseFailAlloc_1597_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1596_;
            }
            16 => {
                v___x_1604_ = (crate::leanh::lean_unbox(v_a_1600_) as u8);
                crate::leanh::lean_dec(v_a_1600_);
                if v___x_1604_ == 0 {
                    crate::leanh::lean_del_object(v___x_1602_);
                    state = 11;
                    continue;
                } else {
                    if v_isShared_1603_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1602_, 0, v_e_1478_);
                        v___x_1606_ = v___x_1602_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1607_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_e_1478_);
                        v___x_1606_ = v_reuseFailAlloc_1607_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                return v___x_1606_;
            }
            18 => {
                if v_isShared_1612_ == 0 {
                    v___x_1614_ = v___x_1611_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1615_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
                    v___x_1614_ = v_reuseFailAlloc_1615_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed(
    mut v_e_1617_: *mut crate::leanh::LeanObject,
    mut v_explicitOnly_1618_: *mut crate::leanh::LeanObject,
    mut v_skipTypes_1619_: *mut crate::leanh::LeanObject,
    mut v_skipProofs_1620_: *mut crate::leanh::LeanObject,
    mut v___y_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
    mut v___y_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_explicitOnly_boxed_1627_: u8 = 0;
    let mut v_skipTypes_boxed_1628_: u8 = 0;
    let mut v_skipProofs_boxed_1629_: u8 = 0;
    let mut v_res_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_explicitOnly_boxed_1627_ = (crate::leanh::lean_unbox(v_explicitOnly_1618_) as u8);
    v_skipTypes_boxed_1628_ = (crate::leanh::lean_unbox(v_skipTypes_1619_) as u8);
    v_skipProofs_boxed_1629_ = (crate::leanh::lean_unbox(v_skipProofs_1620_) as u8);
    v_res_1630_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(
        v_e_1617_,
        v_explicitOnly_boxed_1627_,
        v_skipTypes_boxed_1628_,
        v_skipProofs_boxed_1629_,
        v___y_1621_,
        v___y_1622_,
        v___y_1623_,
        v___y_1624_,
        v___y_1625_,
    );
    crate::leanh::lean_dec(v___y_1625_);
    crate::leanh::lean_dec_ref(v___y_1624_);
    crate::leanh::lean_dec(v___y_1623_);
    crate::leanh::lean_dec_ref(v___y_1622_);
    crate::leanh::lean_dec(v___y_1621_);
    return v_res_1630_;
}
pub unsafe fn l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(
    mut v_explicitOnly_1631_: u8,
    mut v_skipTypes_1632_: u8,
    mut v_skipProofs_1633_: u8,
    mut v_e_1634_: *mut crate::leanh::LeanObject,
    mut v_a_1635_: *mut crate::leanh::LeanObject,
    mut v_a_1636_: *mut crate::leanh::LeanObject,
    mut v_a_1637_: *mut crate::leanh::LeanObject,
    mut v_a_1638_: *mut crate::leanh::LeanObject,
    mut v_a_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1651_: u8 = 0;
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1658_: u8 = 0;
    let mut v_val_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1662_: u8 = 0;
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1666_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1641_ = lean_st_ref_get(v_a_1635_);
                v___x_1642_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v___x_1641_, v_e_1634_);
                crate::leanh::lean_dec(v___x_1641_);
                if crate::leanh::lean_obj_tag(v___x_1642_) == 0 {
                    v___x_1643_ = crate::leanh::lean_box((v_explicitOnly_1631_) as usize);
                    v___x_1644_ = crate::leanh::lean_box((v_skipTypes_1632_) as usize);
                    v___x_1645_ = crate::leanh::lean_box((v_skipProofs_1633_) as usize);
                    crate::leanh::lean_inc_ref(v_e_1634_);
                    v___f_1646_ = crate::leanh::lean_alloc_closure(
                        l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed
                            as *mut core::ffi::c_void,
                        10,
                        4,
                    );
                    crate::leanh::lean_closure_set(v___f_1646_, 0, v_e_1634_);
                    crate::leanh::lean_closure_set(v___f_1646_, 1, v___x_1643_);
                    crate::leanh::lean_closure_set(v___f_1646_, 2, v___x_1644_);
                    crate::leanh::lean_closure_set(v___f_1646_, 3, v___x_1645_);
                    v___x_1647_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v___f_1646_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
                    if crate::leanh::lean_obj_tag(v___x_1647_) == 0 {
                        v_a_1648_ = crate::leanh::lean_ctor_get(v___x_1647_, 0);
                        v_isSharedCheck_1658_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1647_)) as u8;
                        if v_isSharedCheck_1658_ == 0 {
                            v___x_1650_ = v___x_1647_;
                            v_isShared_1651_ = v_isSharedCheck_1658_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1648_);
                            crate::leanh::lean_dec(v___x_1647_);
                            v___x_1650_ = crate::leanh::lean_box(0);
                            v_isShared_1651_ = v_isSharedCheck_1658_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1634_);
                        return v___x_1647_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1634_);
                    v_val_1659_ = crate::leanh::lean_ctor_get(v___x_1642_, 0);
                    v_isSharedCheck_1666_ = (!crate::leanh::lean_is_exclusive(v___x_1642_)) as u8;
                    if v_isSharedCheck_1666_ == 0 {
                        v___x_1661_ = v___x_1642_;
                        v_isShared_1662_ = v_isSharedCheck_1666_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1659_);
                        crate::leanh::lean_dec(v___x_1642_);
                        v___x_1661_ = crate::leanh::lean_box(0);
                        v_isShared_1662_ = v_isSharedCheck_1666_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1652_ = lean_st_ref_take(v_a_1635_);
                crate::leanh::lean_inc(v_a_1648_);
                v___x_1653_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v___x_1652_, v_e_1634_, v_a_1648_);
                v___x_1654_ = lean_st_ref_set(v_a_1635_, v___x_1653_);
                if v_isShared_1651_ == 0 {
                    v___x_1656_ = v___x_1650_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1657_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1648_);
                    v___x_1656_ = v_reuseFailAlloc_1657_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1656_;
            }
            3 => {
                if v_isShared_1662_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1661_, 0);
                    v___x_1664_ = v___x_1661_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1665_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_val_1659_);
                    v___x_1664_ = v_reuseFailAlloc_1665_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1664_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(
    mut v_explicitOnly_1667_: u8,
    mut v_skipTypes_1668_: u8,
    mut v_skipProofs_1669_: u8,
    mut v_a_1670_: u8,
    mut v___x_1671_: u8,
    mut v_xs_1672_: *mut crate::leanh::LeanObject,
    mut v_b_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(
        v_explicitOnly_1667_,
        v_skipTypes_1668_,
        v_skipProofs_1669_,
        v_b_1673_,
        v___y_1674_,
        v___y_1675_,
        v___y_1676_,
        v___y_1677_,
        v___y_1678_,
    );
    if crate::leanh::lean_obj_tag(v___x_1680_) == 0 {
        let mut v_a_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1682_: u8 = 0;
        let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1681_ = crate::leanh::lean_ctor_get(v___x_1680_, 0);
        crate::leanh::lean_inc(v_a_1681_);
        crate::leanh::lean_dec_ref_known(v___x_1680_, 1);
        v___x_1682_ = 1;
        v___x_1683_ = l_Lean_Meta_mkLambdaFVars(
            v_xs_1672_,
            v_a_1681_,
            v_a_1670_,
            v___x_1671_,
            v_a_1670_,
            v___x_1671_,
            v___x_1682_,
            v___y_1675_,
            v___y_1676_,
            v___y_1677_,
            v___y_1678_,
        );
        return v___x_1683_;
    } else {
        return v___x_1680_;
    }
}
pub unsafe fn l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___boxed(
    mut v_explicitOnly_1684_: *mut crate::leanh::LeanObject,
    mut v_skipTypes_1685_: *mut crate::leanh::LeanObject,
    mut v_skipProofs_1686_: *mut crate::leanh::LeanObject,
    mut v_e_1687_: *mut crate::leanh::LeanObject,
    mut v_a_1688_: *mut crate::leanh::LeanObject,
    mut v_a_1689_: *mut crate::leanh::LeanObject,
    mut v_a_1690_: *mut crate::leanh::LeanObject,
    mut v_a_1691_: *mut crate::leanh::LeanObject,
    mut v_a_1692_: *mut crate::leanh::LeanObject,
    mut v_a_1693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_explicitOnly_boxed_1694_: u8 = 0;
    let mut v_skipTypes_boxed_1695_: u8 = 0;
    let mut v_skipProofs_boxed_1696_: u8 = 0;
    let mut v_res_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_explicitOnly_boxed_1694_ = (crate::leanh::lean_unbox(v_explicitOnly_1684_) as u8);
    v_skipTypes_boxed_1695_ = (crate::leanh::lean_unbox(v_skipTypes_1685_) as u8);
    v_skipProofs_boxed_1696_ = (crate::leanh::lean_unbox(v_skipProofs_1686_) as u8);
    v_res_1697_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(
        v_explicitOnly_boxed_1694_,
        v_skipTypes_boxed_1695_,
        v_skipProofs_boxed_1696_,
        v_e_1687_,
        v_a_1688_,
        v_a_1689_,
        v_a_1690_,
        v_a_1691_,
        v_a_1692_,
    );
    crate::leanh::lean_dec(v_a_1692_);
    crate::leanh::lean_dec_ref(v_a_1691_);
    crate::leanh::lean_dec(v_a_1690_);
    crate::leanh::lean_dec_ref(v_a_1689_);
    crate::leanh::lean_dec(v_a_1688_);
    return v_res_1697_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg___boxed(
    mut v_explicitOnly_1698_: *mut crate::leanh::LeanObject,
    mut v_skipTypes_1699_: *mut crate::leanh::LeanObject,
    mut v_skipProofs_1700_: *mut crate::leanh::LeanObject,
    mut v_upperBound_1701_: *mut crate::leanh::LeanObject,
    mut v_a_1702_: *mut crate::leanh::LeanObject,
    mut v_a_1703_: *mut crate::leanh::LeanObject,
    mut v_a_1704_: *mut crate::leanh::LeanObject,
    mut v_b_1705_: *mut crate::leanh::LeanObject,
    mut v___y_1706_: *mut crate::leanh::LeanObject,
    mut v___y_1707_: *mut crate::leanh::LeanObject,
    mut v___y_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
    mut v___y_1710_: *mut crate::leanh::LeanObject,
    mut v___y_1711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_explicitOnly_boxed_1712_: u8 = 0;
    let mut v_skipTypes_boxed_1713_: u8 = 0;
    let mut v_skipProofs_boxed_1714_: u8 = 0;
    let mut v_a_16784__boxed_1715_: u8 = 0;
    let mut v_res_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_explicitOnly_boxed_1712_ = (crate::leanh::lean_unbox(v_explicitOnly_1698_) as u8);
    v_skipTypes_boxed_1713_ = (crate::leanh::lean_unbox(v_skipTypes_1699_) as u8);
    v_skipProofs_boxed_1714_ = (crate::leanh::lean_unbox(v_skipProofs_1700_) as u8);
    v_a_16784__boxed_1715_ = (crate::leanh::lean_unbox(v_a_1703_) as u8);
    v_res_1716_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_boxed_1712_, v_skipTypes_boxed_1713_, v_skipProofs_boxed_1714_, v_upperBound_1701_, v_a_1702_, v_a_16784__boxed_1715_, v_a_1704_, v_b_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
    crate::leanh::lean_dec(v___y_1710_);
    crate::leanh::lean_dec_ref(v___y_1709_);
    crate::leanh::lean_dec(v___y_1708_);
    crate::leanh::lean_dec_ref(v___y_1707_);
    crate::leanh::lean_dec(v___y_1706_);
    crate::leanh::lean_dec_ref(v_a_1702_);
    crate::leanh::lean_dec(v_upperBound_1701_);
    return v_res_1716_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(
    mut v_00_u03b2_1717_: *mut crate::leanh::LeanObject,
    mut v_m_1718_: *mut crate::leanh::LeanObject,
    mut v_a_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v_m_1718_, v_a_1719_);
    return v___x_1720_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___boxed(
    mut v_00_u03b2_1721_: *mut crate::leanh::LeanObject,
    mut v_m_1722_: *mut crate::leanh::LeanObject,
    mut v_a_1723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1724_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(v_00_u03b2_1721_, v_m_1722_, v_a_1723_);
    crate::leanh::lean_dec_ref(v_a_1723_);
    crate::leanh::lean_dec_ref(v_m_1722_);
    return v_res_1724_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(
    mut v_explicitOnly_1725_: u8,
    mut v_skipTypes_1726_: u8,
    mut v_skipProofs_1727_: u8,
    mut v_upperBound_1728_: *mut crate::leanh::LeanObject,
    mut v_a_1729_: *mut crate::leanh::LeanObject,
    mut v_a_1730_: u8,
    mut v_inst_1731_: *mut crate::leanh::LeanObject,
    mut v_R_1732_: *mut crate::leanh::LeanObject,
    mut v_a_1733_: *mut crate::leanh::LeanObject,
    mut v_b_1734_: *mut crate::leanh::LeanObject,
    mut v_c_1735_: *mut crate::leanh::LeanObject,
    mut v___y_1736_: *mut crate::leanh::LeanObject,
    mut v___y_1737_: *mut crate::leanh::LeanObject,
    mut v___y_1738_: *mut crate::leanh::LeanObject,
    mut v___y_1739_: *mut crate::leanh::LeanObject,
    mut v___y_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1742_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_1725_, v_skipTypes_1726_, v_skipProofs_1727_, v_upperBound_1728_, v_a_1729_, v_a_1730_, v_a_1733_, v_b_1734_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
    return v___x_1742_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_explicitOnly_1743_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_skipTypes_1744_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_skipProofs_1745_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_upperBound_1746_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_1747_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_1748_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_inst_1749_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_R_1750_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_1751_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_b_1752_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_c_1753_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_1754_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_1755_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_1756_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_1757_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_1758_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_1759_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_explicitOnly_boxed_1760_: u8 = 0;
    let mut v_skipTypes_boxed_1761_: u8 = 0;
    let mut v_skipProofs_boxed_1762_: u8 = 0;
    let mut v_a_17293__boxed_1763_: u8 = 0;
    let mut v_res_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_explicitOnly_boxed_1760_ = (crate::leanh::lean_unbox(v_explicitOnly_1743_) as u8);
    v_skipTypes_boxed_1761_ = (crate::leanh::lean_unbox(v_skipTypes_1744_) as u8);
    v_skipProofs_boxed_1762_ = (crate::leanh::lean_unbox(v_skipProofs_1745_) as u8);
    v_a_17293__boxed_1763_ = (crate::leanh::lean_unbox(v_a_1748_) as u8);
    v_res_1764_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(v_explicitOnly_boxed_1760_, v_skipTypes_boxed_1761_, v_skipProofs_boxed_1762_, v_upperBound_1746_, v_a_1747_, v_a_17293__boxed_1763_, v_inst_1749_, v_R_1750_, v_a_1751_, v_b_1752_, v_c_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
    crate::leanh::lean_dec(v___y_1758_);
    crate::leanh::lean_dec_ref(v___y_1757_);
    crate::leanh::lean_dec(v___y_1756_);
    crate::leanh::lean_dec_ref(v___y_1755_);
    crate::leanh::lean_dec(v___y_1754_);
    crate::leanh::lean_dec_ref(v_a_1747_);
    crate::leanh::lean_dec(v_upperBound_1746_);
    return v_res_1764_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6(
    mut v_00_u03b1_1765_: *mut crate::leanh::LeanObject,
    mut v_ref_1766_: *mut crate::leanh::LeanObject,
    mut v___y_1767_: *mut crate::leanh::LeanObject,
    mut v___y_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_1766_);
    return v___x_1770_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___boxed(
    mut v_00_u03b1_1771_: *mut crate::leanh::LeanObject,
    mut v_ref_1772_: *mut crate::leanh::LeanObject,
    mut v___y_1773_: *mut crate::leanh::LeanObject,
    mut v___y_1774_: *mut crate::leanh::LeanObject,
    mut v___y_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1776_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6(v_00_u03b1_1771_, v_ref_1772_, v___y_1773_, v___y_1774_);
    crate::leanh::lean_dec(v___y_1774_);
    crate::leanh::lean_dec_ref(v___y_1773_);
    return v_res_1776_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7(
    mut v_00_u03b1_1777_: *mut crate::leanh::LeanObject,
    mut v___y_1778_: *mut crate::leanh::LeanObject,
    mut v___y_1779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg();
    return v___x_1781_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___boxed(
    mut v_00_u03b1_1782_: *mut crate::leanh::LeanObject,
    mut v___y_1783_: *mut crate::leanh::LeanObject,
    mut v___y_1784_: *mut crate::leanh::LeanObject,
    mut v___y_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1786_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7(v_00_u03b1_1782_, v___y_1783_, v___y_1784_);
    crate::leanh::lean_dec(v___y_1784_);
    crate::leanh::lean_dec_ref(v___y_1783_);
    return v_res_1786_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(
    mut v_00_u03b1_1787_: *mut crate::leanh::LeanObject,
    mut v_x_1788_: *mut crate::leanh::LeanObject,
    mut v___y_1789_: *mut crate::leanh::LeanObject,
    mut v___y_1790_: *mut crate::leanh::LeanObject,
    mut v___y_1791_: *mut crate::leanh::LeanObject,
    mut v___y_1792_: *mut crate::leanh::LeanObject,
    mut v___y_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1795_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v_x_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
    return v___x_1795_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___boxed(
    mut v_00_u03b1_1796_: *mut crate::leanh::LeanObject,
    mut v_x_1797_: *mut crate::leanh::LeanObject,
    mut v___y_1798_: *mut crate::leanh::LeanObject,
    mut v___y_1799_: *mut crate::leanh::LeanObject,
    mut v___y_1800_: *mut crate::leanh::LeanObject,
    mut v___y_1801_: *mut crate::leanh::LeanObject,
    mut v___y_1802_: *mut crate::leanh::LeanObject,
    mut v___y_1803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1804_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(v_00_u03b1_1796_, v_x_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
    crate::leanh::lean_dec(v___y_1802_);
    crate::leanh::lean_dec_ref(v___y_1801_);
    crate::leanh::lean_dec(v___y_1800_);
    crate::leanh::lean_dec_ref(v___y_1799_);
    crate::leanh::lean_dec(v___y_1798_);
    return v_res_1804_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6(
    mut v_00_u03b2_1805_: *mut crate::leanh::LeanObject,
    mut v_m_1806_: *mut crate::leanh::LeanObject,
    mut v_a_1807_: *mut crate::leanh::LeanObject,
    mut v_b_1808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1809_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v_m_1806_, v_a_1807_, v_b_1808_);
    return v___x_1809_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(
    mut v_00_u03b2_1810_: *mut crate::leanh::LeanObject,
    mut v_a_1811_: *mut crate::leanh::LeanObject,
    mut v_x_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1813_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(v_a_1811_, v_x_1812_);
    return v___x_1813_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___boxed(
    mut v_00_u03b2_1814_: *mut crate::leanh::LeanObject,
    mut v_a_1815_: *mut crate::leanh::LeanObject,
    mut v_x_1816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1817_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(v_00_u03b2_1814_, v_a_1815_, v_x_1816_);
    crate::leanh::lean_dec(v_x_1816_);
    crate::leanh::lean_dec_ref(v_a_1815_);
    return v_res_1817_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9(
    mut v_00_u03b2_1818_: *mut crate::leanh::LeanObject,
    mut v_a_1819_: *mut crate::leanh::LeanObject,
    mut v_x_1820_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1821_: u8 = 0;
    v___x_1821_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_a_1819_, v_x_1820_);
    return v___x_1821_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___boxed(
    mut v_00_u03b2_1822_: *mut crate::leanh::LeanObject,
    mut v_a_1823_: *mut crate::leanh::LeanObject,
    mut v_x_1824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1825_: u8 = 0;
    let mut v_r_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1825_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9(v_00_u03b2_1822_, v_a_1823_, v_x_1824_);
    crate::leanh::lean_dec(v_x_1824_);
    crate::leanh::lean_dec_ref(v_a_1823_);
    v_r_1826_ = crate::leanh::lean_box((v_res_1825_) as usize);
    return v_r_1826_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10(
    mut v_00_u03b2_1827_: *mut crate::leanh::LeanObject,
    mut v_data_1828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1829_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(v_data_1828_);
    return v___x_1829_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11(
    mut v_00_u03b2_1830_: *mut crate::leanh::LeanObject,
    mut v_a_1831_: *mut crate::leanh::LeanObject,
    mut v_b_1832_: *mut crate::leanh::LeanObject,
    mut v_x_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1834_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11___redArg(v_a_1831_, v_b_1832_, v_x_1833_);
    return v___x_1834_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11(
    mut v_00_u03b2_1835_: *mut crate::leanh::LeanObject,
    mut v_i_1836_: *mut crate::leanh::LeanObject,
    mut v_source_1837_: *mut crate::leanh::LeanObject,
    mut v_target_1838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1839_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11___redArg(v_i_1836_, v_source_1837_, v_target_1838_);
    return v___x_1839_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11_spec__12(
    mut v_00_u03b2_1840_: *mut crate::leanh::LeanObject,
    mut v_x_1841_: *mut crate::leanh::LeanObject,
    mut v_x_1842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1843_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11_spec__12___redArg(v_x_1841_, v_x_1842_);
    return v___x_1843_;
}
pub unsafe fn _init_l_Lean_Meta_reduce___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1844_ = crate::leanh::lean_box(0);
    v___x_1845_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1846_ = lean_mk_array(v___x_1845_, v___x_1844_);
    return v___x_1846_;
}
pub unsafe fn _init_l_Lean_Meta_reduce___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1847_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_reduce___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_reduce___closed__0_once),
        _init_l_Lean_Meta_reduce___closed__0,
    );
    v___x_1848_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1849_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1849_, 0, v___x_1848_);
    crate::leanh::lean_ctor_set(v___x_1849_, 1, v___x_1847_);
    return v___x_1849_;
}
pub unsafe fn l_Lean_Meta_reduce(
    mut v_e_1850_: *mut crate::leanh::LeanObject,
    mut v_explicitOnly_1851_: u8,
    mut v_skipTypes_1852_: u8,
    mut v_skipProofs_1853_: u8,
    mut v_a_1854_: *mut crate::leanh::LeanObject,
    mut v_a_1855_: *mut crate::leanh::LeanObject,
    mut v_a_1856_: *mut crate::leanh::LeanObject,
    mut v_a_1857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1865_: u8 = 0;
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1859_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_reduce___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_reduce___closed__1_once),
                    _init_l_Lean_Meta_reduce___closed__1,
                );
                v___x_1860_ = lean_st_mk_ref(v___x_1859_);
                v___x_1861_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(
                    v_explicitOnly_1851_,
                    v_skipTypes_1852_,
                    v_skipProofs_1853_,
                    v_e_1850_,
                    v___x_1860_,
                    v_a_1854_,
                    v_a_1855_,
                    v_a_1856_,
                    v_a_1857_,
                );
                if crate::leanh::lean_obj_tag(v___x_1861_) == 0 {
                    v_a_1862_ = crate::leanh::lean_ctor_get(v___x_1861_, 0);
                    v_isSharedCheck_1870_ = (!crate::leanh::lean_is_exclusive(v___x_1861_)) as u8;
                    if v_isSharedCheck_1870_ == 0 {
                        v___x_1864_ = v___x_1861_;
                        v_isShared_1865_ = v_isSharedCheck_1870_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1862_);
                        crate::leanh::lean_dec(v___x_1861_);
                        v___x_1864_ = crate::leanh::lean_box(0);
                        v_isShared_1865_ = v_isSharedCheck_1870_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1860_);
                    return v___x_1861_;
                }
            }
            1 => {
                v___x_1866_ = lean_st_ref_get(v___x_1860_);
                crate::leanh::lean_dec(v___x_1860_);
                crate::leanh::lean_dec(v___x_1866_);
                if v_isShared_1865_ == 0 {
                    v___x_1868_ = v___x_1864_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1869_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1862_);
                    v___x_1868_ = v_reuseFailAlloc_1869_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_reduce___boxed(
    mut v_e_1871_: *mut crate::leanh::LeanObject,
    mut v_explicitOnly_1872_: *mut crate::leanh::LeanObject,
    mut v_skipTypes_1873_: *mut crate::leanh::LeanObject,
    mut v_skipProofs_1874_: *mut crate::leanh::LeanObject,
    mut v_a_1875_: *mut crate::leanh::LeanObject,
    mut v_a_1876_: *mut crate::leanh::LeanObject,
    mut v_a_1877_: *mut crate::leanh::LeanObject,
    mut v_a_1878_: *mut crate::leanh::LeanObject,
    mut v_a_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_explicitOnly_boxed_1880_: u8 = 0;
    let mut v_skipTypes_boxed_1881_: u8 = 0;
    let mut v_skipProofs_boxed_1882_: u8 = 0;
    let mut v_res_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_explicitOnly_boxed_1880_ = (crate::leanh::lean_unbox(v_explicitOnly_1872_) as u8);
    v_skipTypes_boxed_1881_ = (crate::leanh::lean_unbox(v_skipTypes_1873_) as u8);
    v_skipProofs_boxed_1882_ = (crate::leanh::lean_unbox(v_skipProofs_1874_) as u8);
    v_res_1883_ = l_Lean_Meta_reduce(
        v_e_1871_,
        v_explicitOnly_boxed_1880_,
        v_skipTypes_boxed_1881_,
        v_skipProofs_boxed_1882_,
        v_a_1875_,
        v_a_1876_,
        v_a_1877_,
        v_a_1878_,
    );
    crate::leanh::lean_dec(v_a_1878_);
    crate::leanh::lean_dec_ref(v_a_1877_);
    crate::leanh::lean_dec(v_a_1876_);
    crate::leanh::lean_dec_ref(v_a_1875_);
    return v_res_1883_;
}
pub unsafe fn l_Lean_Meta_reduceAll(
    mut v_e_1884_: *mut crate::leanh::LeanObject,
    mut v_a_1885_: *mut crate::leanh::LeanObject,
    mut v_a_1886_: *mut crate::leanh::LeanObject,
    mut v_a_1887_: *mut crate::leanh::LeanObject,
    mut v_a_1888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1890_: u8 = 0;
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1890_ = 0;
    v___x_1891_ = l_Lean_Meta_reduce(
        v_e_1884_,
        v___x_1890_,
        v___x_1890_,
        v___x_1890_,
        v_a_1885_,
        v_a_1886_,
        v_a_1887_,
        v_a_1888_,
    );
    return v___x_1891_;
}
pub unsafe fn l_Lean_Meta_reduceAll___boxed(
    mut v_e_1892_: *mut crate::leanh::LeanObject,
    mut v_a_1893_: *mut crate::leanh::LeanObject,
    mut v_a_1894_: *mut crate::leanh::LeanObject,
    mut v_a_1895_: *mut crate::leanh::LeanObject,
    mut v_a_1896_: *mut crate::leanh::LeanObject,
    mut v_a_1897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1898_ = l_Lean_Meta_reduceAll(v_e_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
    crate::leanh::lean_dec(v_a_1896_);
    crate::leanh::lean_dec_ref(v_a_1895_);
    crate::leanh::lean_dec(v_a_1894_);
    crate::leanh::lean_dec_ref(v_a_1893_);
    return v_res_1898_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Reduce(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_FunInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Reduce(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Reduce(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_FunInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Reduce(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Reduce(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Reduce(builtin);
}
