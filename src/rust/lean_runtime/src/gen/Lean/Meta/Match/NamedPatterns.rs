// Lean compiler output
// Module: Lean.Meta.Match.NamedPatterns
// Imports: Lean.Meta.Basic Lean.Meta.AppBuilder Lean.Meta.WHNF
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_maxRecDepthErrorMessage,
};
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_mkRef___boxed};
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_consumeMData, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isConst,
    l_Lean_Expr_isConstOf, l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override,
    l_Lean_Expr_sort___override, l_Lean_ExprStructEq_beq, l_Lean_ExprStructEq_hash, l_Lean_mkAppN,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkAppM, runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_mkLetFVars, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::FunInfo::l_Lean_Meta_getFunInfoNArgs;
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_unfoldDefinition_x3f, runtime_initialize_Lean_Meta_WHNF,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate_rev;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_5, lean_apply_6, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Match_mkNamedPattern___closed__0_value: LeanStringObject<13> =
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
        m_data: [110, 97, 109, 101, 100, 80, 97, 116, 116, 101, 114, 110, 0],
    };
static mut l_Lean_Meta_Match_mkNamedPattern___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_mkNamedPattern___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Match_mkNamedPattern___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Match_mkNamedPattern___closed__0_value) as *mut LeanObject,
        5746968175786816561 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Match_mkNamedPattern___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_mkNamedPattern___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Match_unfoldNamedPattern___lam__0___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Meta_Match_unfoldNamedPattern___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_unfoldNamedPattern___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_unfoldNamedPattern___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Match_unfoldNamedPattern___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Match_unfoldNamedPattern___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_unfoldNamedPattern___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Match_unfoldNamedPattern___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Match_unfoldNamedPattern___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Match_unfoldNamedPattern___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_unfoldNamedPattern___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Match_mkNamedPattern(
    mut v_x_1505_: *mut LeanObject,
    mut v_h_1506_: *mut LeanObject,
    mut v_p_1507_: *mut LeanObject,
    mut v_a_1508_: *mut LeanObject,
    mut v_a_1509_: *mut LeanObject,
    mut v_a_1510_: *mut LeanObject,
    mut v_a_1511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    v___x_1513_ = l_Lean_Meta_Match_mkNamedPattern___closed__1;
    v___x_1514_ = lean_unsigned_to_nat(3);
    v___x_1515_ = lean_mk_empty_array_with_capacity(v___x_1514_);
    v___x_1516_ = lean_array_push(v___x_1515_, v_x_1505_);
    v___x_1517_ = lean_array_push(v___x_1516_, v_p_1507_);
    v___x_1518_ = lean_array_push(v___x_1517_, v_h_1506_);
    v___x_1519_ = l_Lean_Meta_mkAppM(
        v___x_1513_,
        v___x_1518_,
        v_a_1508_,
        v_a_1509_,
        v_a_1510_,
        v_a_1511_,
    );
    return v___x_1519_;
}
pub unsafe fn l_Lean_Meta_Match_mkNamedPattern___boxed(
    mut v_x_1520_: *mut LeanObject,
    mut v_h_1521_: *mut LeanObject,
    mut v_p_1522_: *mut LeanObject,
    mut v_a_1523_: *mut LeanObject,
    mut v_a_1524_: *mut LeanObject,
    mut v_a_1525_: *mut LeanObject,
    mut v_a_1526_: *mut LeanObject,
    mut v_a_1527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1528_: *mut LeanObject = core::ptr::null_mut();
    v_res_1528_ = l_Lean_Meta_Match_mkNamedPattern(
        v_x_1520_, v_h_1521_, v_p_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_,
    );
    lean_dec(v_a_1526_);
    lean_dec_ref(v_a_1525_);
    lean_dec(v_a_1524_);
    lean_dec_ref(v_a_1523_);
    return v_res_1528_;
}
pub unsafe fn l_Lean_Meta_Match_isNamedPattern(mut v_e_1529_: *mut LeanObject) -> u8 {
    let mut v_e_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: u8 = 0;
    v_e_1530_ = l_Lean_Expr_consumeMData(v_e_1529_);
    v___x_1531_ = l_Lean_Expr_getAppNumArgs(v_e_1530_);
    v___x_1532_ = lean_unsigned_to_nat(4);
    v___x_1533_ = lean_nat_dec_eq(v___x_1531_, v___x_1532_);
    lean_dec(v___x_1531_);
    if v___x_1533_ == 0 {
        lean_dec_ref(v_e_1530_);
        return v___x_1533_;
    } else {
        let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1537_: u8 = 0;
        v___x_1534_ = l_Lean_Expr_getAppFn(v_e_1530_);
        lean_dec_ref(v_e_1530_);
        v___x_1535_ = l_Lean_Expr_consumeMData(v___x_1534_);
        lean_dec_ref(v___x_1534_);
        v___x_1536_ = l_Lean_Meta_Match_mkNamedPattern___closed__1;
        v___x_1537_ = l_Lean_Expr_isConstOf(v___x_1535_, v___x_1536_);
        lean_dec_ref(v___x_1535_);
        return v___x_1537_;
    }
}
pub unsafe fn l_Lean_Meta_Match_isNamedPattern___boxed(
    mut v_e_1538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1539_: u8 = 0;
    let mut v_r_1540_: *mut LeanObject = core::ptr::null_mut();
    v_res_1539_ = l_Lean_Meta_Match_isNamedPattern(v_e_1538_);
    lean_dec_ref(v_e_1538_);
    v_r_1540_ = lean_box((v_res_1539_) as usize);
    return v_r_1540_;
}
pub unsafe fn l_Lean_Meta_Match_isNamedPattern_x3f(
    mut v_e_1541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1544_: u8 = 0;
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_e_1542_ = l_Lean_Expr_consumeMData(v_e_1541_);
                v___x_1547_ = l_Lean_Expr_getAppNumArgs(v_e_1542_);
                v___x_1548_ = lean_unsigned_to_nat(4);
                v___x_1549_ = lean_nat_dec_eq(v___x_1547_, v___x_1548_);
                lean_dec(v___x_1547_);
                if v___x_1549_ == 0 {
                    v___y_1544_ = v___x_1549_;
                    state = 1;
                    continue;
                } else {
                    v___x_1550_ = l_Lean_Expr_getAppFn(v_e_1542_);
                    v___x_1551_ = l_Lean_Expr_consumeMData(v___x_1550_);
                    lean_dec_ref(v___x_1550_);
                    v___x_1552_ = l_Lean_Meta_Match_mkNamedPattern___closed__1;
                    v___x_1553_ = l_Lean_Expr_isConstOf(v___x_1551_, v___x_1552_);
                    lean_dec_ref(v___x_1551_);
                    v___y_1544_ = v___x_1553_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1544_ == 0 {
                    lean_dec_ref(v_e_1542_);
                    v___x_1545_ = lean_box(0);
                    return v___x_1545_;
                } else {
                    v___x_1546_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1546_, 0, v_e_1542_);
                    return v___x_1546_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_isNamedPattern_x3f___boxed(
    mut v_e_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1555_: *mut LeanObject = core::ptr::null_mut();
    v_res_1555_ = l_Lean_Meta_Match_isNamedPattern_x3f(v_e_1554_);
    lean_dec_ref(v_e_1554_);
    return v_res_1555_;
}
pub unsafe fn l_Lean_Meta_Match_unfoldNamedPattern___lam__0(
    mut v_e_1558_: *mut LeanObject,
    mut v___y_1559_: *mut LeanObject,
    mut v___y_1560_: *mut LeanObject,
    mut v___y_1561_: *mut LeanObject,
    mut v___y_1562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1574_: u8 = 0;
    let mut v_val_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1578_: u8 = 0;
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1585_: u8 = 0;
    let mut v_isSharedCheck_1586_: u8 = 0;
    let mut v_a_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1590_: u8 = 0;
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1567_ = l_Lean_Meta_Match_isNamedPattern_x3f(v_e_1558_);
                if lean_obj_tag(v___x_1567_) == 1 {
                    v_val_1568_ = lean_ctor_get(v___x_1567_, 0);
                    lean_inc(v_val_1568_);
                    lean_dec_ref_known(v___x_1567_, 1);
                    v___x_1569_ = 0;
                    v___x_1570_ = l_Lean_Meta_unfoldDefinition_x3f(
                        v_val_1568_,
                        v___x_1569_,
                        v___y_1559_,
                        v___y_1560_,
                        v___y_1561_,
                        v___y_1562_,
                    );
                    if lean_obj_tag(v___x_1570_) == 0 {
                        v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
                        v_isSharedCheck_1586_ = (!lean_is_exclusive(v___x_1570_)) as u8;
                        if v_isSharedCheck_1586_ == 0 {
                            v___x_1573_ = v___x_1570_;
                            v_isShared_1574_ = v_isSharedCheck_1586_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1571_);
                            lean_dec(v___x_1570_);
                            v___x_1573_ = lean_box(0);
                            v_isShared_1574_ = v_isSharedCheck_1586_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1587_ = lean_ctor_get(v___x_1570_, 0);
                        v_isSharedCheck_1594_ = (!lean_is_exclusive(v___x_1570_)) as u8;
                        if v_isSharedCheck_1594_ == 0 {
                            v___x_1589_ = v___x_1570_;
                            v_isShared_1590_ = v_isSharedCheck_1594_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1587_);
                            lean_dec(v___x_1570_);
                            v___x_1589_ = lean_box(0);
                            v_isShared_1590_ = v_isSharedCheck_1594_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1567_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1565_ = l_Lean_Meta_Match_unfoldNamedPattern___lam__0___closed__0;
                v___x_1566_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1566_, 0, v___x_1565_);
                return v___x_1566_;
            }
            2 => {
                if lean_obj_tag(v_a_1571_) == 1 {
                    v_val_1575_ = lean_ctor_get(v_a_1571_, 0);
                    v_isSharedCheck_1585_ = (!lean_is_exclusive(v_a_1571_)) as u8;
                    if v_isSharedCheck_1585_ == 0 {
                        v___x_1577_ = v_a_1571_;
                        v_isShared_1578_ = v_isSharedCheck_1585_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1575_);
                        lean_dec(v_a_1571_);
                        v___x_1577_ = lean_box(0);
                        v_isShared_1578_ = v_isSharedCheck_1585_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1573_);
                    lean_dec(v_a_1571_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_1578_ == 0 {
                    v___x_1580_ = v___x_1577_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_val_1575_);
                    v___x_1580_ = v_reuseFailAlloc_1584_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1574_ == 0 {
                    lean_ctor_set(v___x_1573_, 0, v___x_1580_);
                    v___x_1582_ = v___x_1573_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
                    v___x_1582_ = v_reuseFailAlloc_1583_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1582_;
            }
            6 => {
                if v_isShared_1590_ == 0 {
                    v___x_1592_ = v___x_1589_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
                    v___x_1592_ = v_reuseFailAlloc_1593_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_unfoldNamedPattern___lam__0___boxed(
    mut v_e_1595_: *mut LeanObject,
    mut v___y_1596_: *mut LeanObject,
    mut v___y_1597_: *mut LeanObject,
    mut v___y_1598_: *mut LeanObject,
    mut v___y_1599_: *mut LeanObject,
    mut v___y_1600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1601_: *mut LeanObject = core::ptr::null_mut();
    v_res_1601_ = l_Lean_Meta_Match_unfoldNamedPattern___lam__0(
        v_e_1595_,
        v___y_1596_,
        v___y_1597_,
        v___y_1598_,
        v___y_1599_,
    );
    lean_dec(v___y_1599_);
    lean_dec_ref(v___y_1598_);
    lean_dec(v___y_1597_);
    lean_dec_ref(v___y_1596_);
    lean_dec_ref(v_e_1595_);
    return v_res_1601_;
}
pub unsafe fn l_Lean_Meta_Match_unfoldNamedPattern___lam__1(
    mut v_e_1602_: *mut LeanObject,
    mut v___y_1603_: *mut LeanObject,
    mut v___y_1604_: *mut LeanObject,
    mut v___y_1605_: *mut LeanObject,
    mut v___y_1606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    v___x_1608_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1608_, 0, v_e_1602_);
    v___x_1609_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1609_, 0, v___x_1608_);
    return v___x_1609_;
}
pub unsafe fn l_Lean_Meta_Match_unfoldNamedPattern___lam__1___boxed(
    mut v_e_1610_: *mut LeanObject,
    mut v___y_1611_: *mut LeanObject,
    mut v___y_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
    mut v___y_1615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1616_: *mut LeanObject = core::ptr::null_mut();
    v_res_1616_ = l_Lean_Meta_Match_unfoldNamedPattern___lam__1(
        v_e_1610_,
        v___y_1611_,
        v___y_1612_,
        v___y_1613_,
        v___y_1614_,
    );
    lean_dec(v___y_1614_);
    lean_dec_ref(v___y_1613_);
    lean_dec(v___y_1612_);
    lean_dec_ref(v___y_1611_);
    return v_res_1616_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__17___redArg(
    mut v_a_1617_: *mut LeanObject,
    mut v_b_1618_: *mut LeanObject,
    mut v_x_1619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1619_) == 0 {
                    lean_dec(v_b_1618_);
                    lean_dec_ref(v_a_1617_);
                    return v_x_1619_;
                } else {
                    v_key_1620_ = lean_ctor_get(v_x_1619_, 0);
                    v_value_1621_ = lean_ctor_get(v_x_1619_, 1);
                    v_tail_1622_ = lean_ctor_get(v_x_1619_, 2);
                    v_isSharedCheck_1634_ = (!lean_is_exclusive(v_x_1619_)) as u8;
                    if v_isSharedCheck_1634_ == 0 {
                        v___x_1624_ = v_x_1619_;
                        v_isShared_1625_ = v_isSharedCheck_1634_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1622_);
                        lean_inc(v_value_1621_);
                        lean_inc(v_key_1620_);
                        lean_dec(v_x_1619_);
                        v___x_1624_ = lean_box(0);
                        v_isShared_1625_ = v_isSharedCheck_1634_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1626_ = l_Lean_ExprStructEq_beq(v_key_1620_, v_a_1617_);
                if v___x_1626_ == 0 {
                    v___x_1627_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__17___redArg(v_a_1617_, v_b_1618_, v_tail_1622_);
                    if v_isShared_1625_ == 0 {
                        lean_ctor_set(v___x_1624_, 2, v___x_1627_);
                        v___x_1629_ = v___x_1624_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_key_1620_);
                        lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_value_1621_);
                        lean_ctor_set(v_reuseFailAlloc_1630_, 2, v___x_1627_);
                        v___x_1629_ = v_reuseFailAlloc_1630_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_1621_);
                    lean_dec(v_key_1620_);
                    if v_isShared_1625_ == 0 {
                        lean_ctor_set(v___x_1624_, 1, v_b_1618_);
                        lean_ctor_set(v___x_1624_, 0, v_a_1617_);
                        v___x_1632_ = v___x_1624_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1617_);
                        lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_b_1618_);
                        lean_ctor_set(v_reuseFailAlloc_1633_, 2, v_tail_1622_);
                        v___x_1632_ = v_reuseFailAlloc_1633_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1629_;
            }
            3 => {
                return v___x_1632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(
    mut v_x_1635_: *mut LeanObject,
    mut v_x_1636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1642_: u8 = 0;
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: u64 = 0;
    let mut v___x_1645_: u64 = 0;
    let mut v___x_1646_: u64 = 0;
    let mut v_fold_1647_: u64 = 0;
    let mut v___x_1648_: u64 = 0;
    let mut v___x_1649_: u64 = 0;
    let mut v___x_1650_: u64 = 0;
    let mut v___x_1651_: usize = 0;
    let mut v___x_1652_: usize = 0;
    let mut v___x_1653_: usize = 0;
    let mut v___x_1654_: usize = 0;
    let mut v___x_1655_: usize = 0;
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1636_) == 0 {
                    return v_x_1635_;
                } else {
                    v_key_1637_ = lean_ctor_get(v_x_1636_, 0);
                    v_value_1638_ = lean_ctor_get(v_x_1636_, 1);
                    v_tail_1639_ = lean_ctor_get(v_x_1636_, 2);
                    v_isSharedCheck_1662_ = (!lean_is_exclusive(v_x_1636_)) as u8;
                    if v_isSharedCheck_1662_ == 0 {
                        v___x_1641_ = v_x_1636_;
                        v_isShared_1642_ = v_isSharedCheck_1662_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1639_);
                        lean_inc(v_value_1638_);
                        lean_inc(v_key_1637_);
                        lean_dec(v_x_1636_);
                        v___x_1641_ = lean_box(0);
                        v_isShared_1642_ = v_isSharedCheck_1662_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1643_ = lean_array_get_size(v_x_1635_);
                v___x_1644_ = l_Lean_ExprStructEq_hash(v_key_1637_);
                v___x_1645_ = 32u64;
                v___x_1646_ = lean_uint64_shift_right(v___x_1644_, v___x_1645_);
                v_fold_1647_ = lean_uint64_xor(v___x_1644_, v___x_1646_);
                v___x_1648_ = 16u64;
                v___x_1649_ = lean_uint64_shift_right(v_fold_1647_, v___x_1648_);
                v___x_1650_ = lean_uint64_xor(v_fold_1647_, v___x_1649_);
                v___x_1651_ = lean_uint64_to_usize(v___x_1650_);
                v___x_1652_ = lean_usize_of_nat(v___x_1643_);
                v___x_1653_ = 1usize;
                v___x_1654_ = lean_usize_sub(v___x_1652_, v___x_1653_);
                v___x_1655_ = lean_usize_land(v___x_1651_, v___x_1654_);
                v___x_1656_ = lean_array_uget_borrowed(v_x_1635_, v___x_1655_);
                lean_inc(v___x_1656_);
                if v_isShared_1642_ == 0 {
                    lean_ctor_set(v___x_1641_, 2, v___x_1656_);
                    v___x_1658_ = v___x_1641_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_key_1637_);
                    lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_value_1638_);
                    lean_ctor_set(v_reuseFailAlloc_1661_, 2, v___x_1656_);
                    v___x_1658_ = v_reuseFailAlloc_1661_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1659_ = lean_array_uset(v_x_1635_, v___x_1655_, v___x_1658_);
                v_x_1635_ = v___x_1659_;
                v_x_1636_ = v_tail_1639_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(
    mut v_i_1663_: *mut LeanObject,
    mut v_source_1664_: *mut LeanObject,
    mut v_target_1665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: u8 = 0;
    let mut v_es_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1666_ = lean_array_get_size(v_source_1664_);
                v___x_1667_ = lean_nat_dec_lt(v_i_1663_, v___x_1666_);
                if v___x_1667_ == 0 {
                    lean_dec_ref(v_source_1664_);
                    lean_dec(v_i_1663_);
                    return v_target_1665_;
                } else {
                    v_es_1668_ = lean_array_fget(v_source_1664_, v_i_1663_);
                    v___x_1669_ = lean_box(0);
                    v_source_1670_ = lean_array_fset(v_source_1664_, v_i_1663_, v___x_1669_);
                    v_target_1671_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_1665_, v_es_1668_);
                    v___x_1672_ = lean_unsigned_to_nat(1);
                    v___x_1673_ = lean_nat_add(v_i_1663_, v___x_1672_);
                    lean_dec(v_i_1663_);
                    v_i_1663_ = v___x_1673_;
                    v_source_1664_ = v_source_1670_;
                    v_target_1665_ = v_target_1671_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__16___redArg(
    mut v_data_1675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    v___x_1676_ = lean_array_get_size(v_data_1675_);
    v___x_1677_ = lean_unsigned_to_nat(2);
    v_nbuckets_1678_ = lean_nat_mul(v___x_1676_, v___x_1677_);
    v___x_1679_ = lean_unsigned_to_nat(0);
    v___x_1680_ = lean_box(0);
    v___x_1681_ = lean_mk_array(v_nbuckets_1678_, v___x_1680_);
    v___x_1682_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_1679_, v_data_1675_, v___x_1681_);
    return v___x_1682_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__15___redArg(
    mut v_a_1683_: *mut LeanObject,
    mut v_x_1684_: *mut LeanObject,
) -> u8 {
    let mut v___x_1685_: u8 = 0;
    let mut v_key_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1684_) == 0 {
                    v___x_1685_ = 0;
                    return v___x_1685_;
                } else {
                    v_key_1686_ = lean_ctor_get(v_x_1684_, 0);
                    v_tail_1687_ = lean_ctor_get(v_x_1684_, 2);
                    v___x_1688_ = l_Lean_ExprStructEq_beq(v_key_1686_, v_a_1683_);
                    if v___x_1688_ == 0 {
                        v_x_1684_ = v_tail_1687_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1688_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__15___redArg___boxed(
    mut v_a_1690_: *mut LeanObject,
    mut v_x_1691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1692_: u8 = 0;
    let mut v_r_1693_: *mut LeanObject = core::ptr::null_mut();
    v_res_1692_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__15___redArg(v_a_1690_, v_x_1691_);
    lean_dec(v_x_1691_);
    lean_dec_ref(v_a_1690_);
    v_r_1693_ = lean_box((v_res_1692_) as usize);
    return v_r_1693_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10___redArg(
    mut v_m_1694_: *mut LeanObject,
    mut v_a_1695_: *mut LeanObject,
    mut v_b_1696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1701_: u8 = 0;
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: u64 = 0;
    let mut v___x_1704_: u64 = 0;
    let mut v___x_1705_: u64 = 0;
    let mut v_fold_1706_: u64 = 0;
    let mut v___x_1707_: u64 = 0;
    let mut v___x_1708_: u64 = 0;
    let mut v___x_1709_: u64 = 0;
    let mut v___x_1710_: usize = 0;
    let mut v___x_1711_: usize = 0;
    let mut v___x_1712_: usize = 0;
    let mut v___x_1713_: usize = 0;
    let mut v___x_1714_: usize = 0;
    let mut v_bkt_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: u8 = 0;
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: u8 = 0;
    let mut v_val_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1697_ = lean_ctor_get(v_m_1694_, 0);
                v_buckets_1698_ = lean_ctor_get(v_m_1694_, 1);
                v_isSharedCheck_1741_ = (!lean_is_exclusive(v_m_1694_)) as u8;
                if v_isSharedCheck_1741_ == 0 {
                    v___x_1700_ = v_m_1694_;
                    v_isShared_1701_ = v_isSharedCheck_1741_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_1698_);
                    lean_inc(v_size_1697_);
                    lean_dec(v_m_1694_);
                    v___x_1700_ = lean_box(0);
                    v_isShared_1701_ = v_isSharedCheck_1741_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1702_ = lean_array_get_size(v_buckets_1698_);
                v___x_1703_ = l_Lean_ExprStructEq_hash(v_a_1695_);
                v___x_1704_ = 32u64;
                v___x_1705_ = lean_uint64_shift_right(v___x_1703_, v___x_1704_);
                v_fold_1706_ = lean_uint64_xor(v___x_1703_, v___x_1705_);
                v___x_1707_ = 16u64;
                v___x_1708_ = lean_uint64_shift_right(v_fold_1706_, v___x_1707_);
                v___x_1709_ = lean_uint64_xor(v_fold_1706_, v___x_1708_);
                v___x_1710_ = lean_uint64_to_usize(v___x_1709_);
                v___x_1711_ = lean_usize_of_nat(v___x_1702_);
                v___x_1712_ = 1usize;
                v___x_1713_ = lean_usize_sub(v___x_1711_, v___x_1712_);
                v___x_1714_ = lean_usize_land(v___x_1710_, v___x_1713_);
                v_bkt_1715_ = lean_array_uget_borrowed(v_buckets_1698_, v___x_1714_);
                v___x_1716_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__15___redArg(v_a_1695_, v_bkt_1715_);
                if v___x_1716_ == 0 {
                    v___x_1717_ = lean_unsigned_to_nat(1);
                    v_size_x27_1718_ = lean_nat_add(v_size_1697_, v___x_1717_);
                    lean_dec(v_size_1697_);
                    lean_inc(v_bkt_1715_);
                    v___x_1719_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1719_, 0, v_a_1695_);
                    lean_ctor_set(v___x_1719_, 1, v_b_1696_);
                    lean_ctor_set(v___x_1719_, 2, v_bkt_1715_);
                    v_buckets_x27_1720_ =
                        lean_array_uset(v_buckets_1698_, v___x_1714_, v___x_1719_);
                    v___x_1721_ = lean_unsigned_to_nat(4);
                    v___x_1722_ = lean_nat_mul(v_size_x27_1718_, v___x_1721_);
                    v___x_1723_ = lean_unsigned_to_nat(3);
                    v___x_1724_ = lean_nat_div(v___x_1722_, v___x_1723_);
                    lean_dec(v___x_1722_);
                    v___x_1725_ = lean_array_get_size(v_buckets_x27_1720_);
                    v___x_1726_ = lean_nat_dec_le(v___x_1724_, v___x_1725_);
                    lean_dec(v___x_1724_);
                    if v___x_1726_ == 0 {
                        v_val_1727_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_1720_);
                        if v_isShared_1701_ == 0 {
                            lean_ctor_set(v___x_1700_, 1, v_val_1727_);
                            lean_ctor_set(v___x_1700_, 0, v_size_x27_1718_);
                            v___x_1729_ = v___x_1700_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_size_x27_1718_);
                            lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_val_1727_);
                            v___x_1729_ = v_reuseFailAlloc_1730_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1701_ == 0 {
                            lean_ctor_set(v___x_1700_, 1, v_buckets_x27_1720_);
                            lean_ctor_set(v___x_1700_, 0, v_size_x27_1718_);
                            v___x_1732_ = v___x_1700_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_size_x27_1718_);
                            lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_buckets_x27_1720_);
                            v___x_1732_ = v_reuseFailAlloc_1733_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1715_);
                    v___x_1734_ = lean_box(0);
                    v_buckets_x27_1735_ =
                        lean_array_uset(v_buckets_1698_, v___x_1714_, v___x_1734_);
                    v___x_1736_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__17___redArg(v_a_1695_, v_b_1696_, v_bkt_1715_);
                    v___x_1737_ = lean_array_uset(v_buckets_x27_1735_, v___x_1714_, v___x_1736_);
                    if v_isShared_1701_ == 0 {
                        lean_ctor_set(v___x_1700_, 1, v___x_1737_);
                        v___x_1739_ = v___x_1700_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_size_1697_);
                        lean_ctor_set(v_reuseFailAlloc_1740_, 1, v___x_1737_);
                        v___x_1739_ = v_reuseFailAlloc_1740_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1729_;
            }
            3 => {
                return v___x_1732_;
            }
            4 => {
                return v___x_1739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__2(
    mut v_a_1742_: *mut LeanObject,
    mut v_e_1743_: *mut LeanObject,
    mut v_a_1744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    v___x_1746_ = lean_st_ref_take(v_a_1742_);
    v___x_1747_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10___redArg(v___x_1746_, v_e_1743_, v_a_1744_);
    v___x_1748_ = lean_st_ref_set(v_a_1742_, v___x_1747_);
    v___x_1749_ = lean_box(0);
    return v___x_1749_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__2___boxed(
    mut v_a_1750_: *mut LeanObject,
    mut v_e_1751_: *mut LeanObject,
    mut v_a_1752_: *mut LeanObject,
    mut v___y_1753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1754_: *mut LeanObject = core::ptr::null_mut();
    v_res_1754_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__2(v_a_1750_, v_e_1751_, v_a_1752_);
    lean_dec(v_a_1750_);
    return v_res_1754_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___redArg___lam__2(
    mut v___x_1755_: *mut LeanObject,
    mut v___y_1756_: *mut LeanObject,
    mut v___y_1757_: *mut LeanObject,
    mut v___y_1758_: *mut LeanObject,
    mut v___y_1759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    v___x_1761_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1761_, 0, v___x_1755_);
    return v___x_1761_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___redArg___lam__2___boxed(
    mut v___x_1762_: *mut LeanObject,
    mut v___y_1763_: *mut LeanObject,
    mut v___y_1764_: *mut LeanObject,
    mut v___y_1765_: *mut LeanObject,
    mut v___y_1766_: *mut LeanObject,
    mut v___y_1767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1768_: *mut LeanObject = core::ptr::null_mut();
    v_res_1768_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___redArg___lam__2(v___x_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
    lean_dec(v___y_1766_);
    lean_dec_ref(v___y_1765_);
    lean_dec(v___y_1764_);
    lean_dec_ref(v___y_1763_);
    return v_res_1768_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(
    mut v_k_1769_: *mut LeanObject,
    mut v___y_1770_: *mut LeanObject,
    mut v_b_1771_: *mut LeanObject,
    mut v___y_1772_: *mut LeanObject,
    mut v___y_1773_: *mut LeanObject,
    mut v___y_1774_: *mut LeanObject,
    mut v___y_1775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1775_);
    lean_inc_ref(v___y_1774_);
    lean_inc(v___y_1773_);
    lean_inc_ref(v___y_1772_);
    lean_inc(v___y_1770_);
    v___x_1777_ = lean_apply_7(
        v_k_1769_,
        v_b_1771_,
        v___y_1770_,
        v___y_1772_,
        v___y_1773_,
        v___y_1774_,
        v___y_1775_,
        lean_box(0),
    );
    return v___x_1777_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(
    mut v_k_1778_: *mut LeanObject,
    mut v___y_1779_: *mut LeanObject,
    mut v_b_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
    mut v___y_1783_: *mut LeanObject,
    mut v___y_1784_: *mut LeanObject,
    mut v___y_1785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1786_: *mut LeanObject = core::ptr::null_mut();
    v_res_1786_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_1778_, v___y_1779_, v_b_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
    lean_dec(v___y_1784_);
    lean_dec_ref(v___y_1783_);
    lean_dec(v___y_1782_);
    lean_dec_ref(v___y_1781_);
    lean_dec(v___y_1779_);
    return v_res_1786_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5_spec__7___redArg(
    mut v_name_1787_: *mut LeanObject,
    mut v_bi_1788_: u8,
    mut v_type_1789_: *mut LeanObject,
    mut v_k_1790_: *mut LeanObject,
    mut v_kind_1791_: u8,
    mut v___y_1792_: *mut LeanObject,
    mut v___y_1793_: *mut LeanObject,
    mut v___y_1794_: *mut LeanObject,
    mut v___y_1795_: *mut LeanObject,
    mut v___y_1796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1803_: u8 = 0;
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1807_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1792_);
                v___f_1798_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                lean_closure_set(v___f_1798_, 0, v_k_1790_);
                lean_closure_set(v___f_1798_, 1, v___y_1792_);
                v___x_1799_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_1787_,
                    v_bi_1788_,
                    v_type_1789_,
                    v___f_1798_,
                    v_kind_1791_,
                    v___y_1793_,
                    v___y_1794_,
                    v___y_1795_,
                    v___y_1796_,
                );
                if lean_obj_tag(v___x_1799_) == 0 {
                    return v___x_1799_;
                } else {
                    v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
                    v_isSharedCheck_1807_ = (!lean_is_exclusive(v___x_1799_)) as u8;
                    if v_isSharedCheck_1807_ == 0 {
                        v___x_1802_ = v___x_1799_;
                        v_isShared_1803_ = v_isSharedCheck_1807_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1800_);
                        lean_dec(v___x_1799_);
                        v___x_1802_ = lean_box(0);
                        v_isShared_1803_ = v_isSharedCheck_1807_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1803_ == 0 {
                    v___x_1805_ = v___x_1802_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
                    v___x_1805_ = v_reuseFailAlloc_1806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1805_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5_spec__7___redArg___boxed(
    mut v_name_1808_: *mut LeanObject,
    mut v_bi_1809_: *mut LeanObject,
    mut v_type_1810_: *mut LeanObject,
    mut v_k_1811_: *mut LeanObject,
    mut v_kind_1812_: *mut LeanObject,
    mut v___y_1813_: *mut LeanObject,
    mut v___y_1814_: *mut LeanObject,
    mut v___y_1815_: *mut LeanObject,
    mut v___y_1816_: *mut LeanObject,
    mut v___y_1817_: *mut LeanObject,
    mut v___y_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_1819_: u8 = 0;
    let mut v_kind_boxed_1820_: u8 = 0;
    let mut v_res_1821_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_1819_ = (lean_unbox(v_bi_1809_) as u8);
    v_kind_boxed_1820_ = (lean_unbox(v_kind_1812_) as u8);
    v_res_1821_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5_spec__7___redArg(v_name_1808_, v_bi_boxed_1819_, v_type_1810_, v_k_1811_, v_kind_boxed_1820_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
    lean_dec(v___y_1817_);
    lean_dec_ref(v___y_1816_);
    lean_dec(v___y_1815_);
    lean_dec_ref(v___y_1814_);
    lean_dec(v___y_1813_);
    return v_res_1821_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7_spec__10___redArg(
    mut v_name_1822_: *mut LeanObject,
    mut v_type_1823_: *mut LeanObject,
    mut v_val_1824_: *mut LeanObject,
    mut v_k_1825_: *mut LeanObject,
    mut v_nondep_1826_: u8,
    mut v_kind_1827_: u8,
    mut v___y_1828_: *mut LeanObject,
    mut v___y_1829_: *mut LeanObject,
    mut v___y_1830_: *mut LeanObject,
    mut v___y_1831_: *mut LeanObject,
    mut v___y_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1839_: u8 = 0;
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1843_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1828_);
                v___f_1834_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                lean_closure_set(v___f_1834_, 0, v_k_1825_);
                lean_closure_set(v___f_1834_, 1, v___y_1828_);
                v___x_1835_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    lean_box(0),
                    v_name_1822_,
                    v_type_1823_,
                    v_val_1824_,
                    v___f_1834_,
                    v_nondep_1826_,
                    v_kind_1827_,
                    v___y_1829_,
                    v___y_1830_,
                    v___y_1831_,
                    v___y_1832_,
                );
                if lean_obj_tag(v___x_1835_) == 0 {
                    return v___x_1835_;
                } else {
                    v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
                    v_isSharedCheck_1843_ = (!lean_is_exclusive(v___x_1835_)) as u8;
                    if v_isSharedCheck_1843_ == 0 {
                        v___x_1838_ = v___x_1835_;
                        v_isShared_1839_ = v_isSharedCheck_1843_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1836_);
                        lean_dec(v___x_1835_);
                        v___x_1838_ = lean_box(0);
                        v_isShared_1839_ = v_isSharedCheck_1843_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1839_ == 0 {
                    v___x_1841_ = v___x_1838_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
                    v___x_1841_ = v_reuseFailAlloc_1842_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1841_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7_spec__10___redArg___boxed(
    mut v_name_1844_: *mut LeanObject,
    mut v_type_1845_: *mut LeanObject,
    mut v_val_1846_: *mut LeanObject,
    mut v_k_1847_: *mut LeanObject,
    mut v_nondep_1848_: *mut LeanObject,
    mut v_kind_1849_: *mut LeanObject,
    mut v___y_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
    mut v___y_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_1856_: u8 = 0;
    let mut v_kind_boxed_1857_: u8 = 0;
    let mut v_res_1858_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_1856_ = (lean_unbox(v_nondep_1848_) as u8);
    v_kind_boxed_1857_ = (lean_unbox(v_kind_1849_) as u8);
    v_res_1858_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1844_, v_type_1845_, v_val_1846_, v_k_1847_, v_nondep_boxed_1856_, v_kind_boxed_1857_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
    lean_dec(v___y_1854_);
    lean_dec_ref(v___y_1853_);
    lean_dec(v___y_1852_);
    lean_dec_ref(v___y_1851_);
    lean_dec(v___y_1850_);
    return v_res_1858_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__0(
    mut v_00_u03b1_1859_: *mut LeanObject,
    mut v_x_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    v___x_1866_ = lean_apply_1(v_x_1860_, lean_box(0));
    v___x_1867_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1867_, 0, v___x_1866_);
    return v___x_1867_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__0___boxed(
    mut v_00_u03b1_1868_: *mut LeanObject,
    mut v_x_1869_: *mut LeanObject,
    mut v___y_1870_: *mut LeanObject,
    mut v___y_1871_: *mut LeanObject,
    mut v___y_1872_: *mut LeanObject,
    mut v___y_1873_: *mut LeanObject,
    mut v___y_1874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1875_: *mut LeanObject = core::ptr::null_mut();
    v_res_1875_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__0(v_00_u03b1_1868_, v_x_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
    lean_dec(v___y_1873_);
    lean_dec_ref(v___y_1872_);
    lean_dec(v___y_1871_);
    lean_dec_ref(v___y_1870_);
    return v_res_1875_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    v___x_1881_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1882_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1882_, 0, v___x_1881_);
    return v___x_1882_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    v___x_1883_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
    v___x_1884_ = l_Lean_MessageData_ofFormat(v___x_1883_);
    return v___x_1884_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    v___x_1885_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
    v___x_1886_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__2;
    v___x_1887_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_1887_, 0, v___x_1886_);
    lean_ctor_set(v___x_1887_, 1, v___x_1885_);
    return v___x_1887_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg(
    mut v_ref_1888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    v___x_1890_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
    v___x_1891_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1891_, 0, v_ref_1888_);
    lean_ctor_set(v___x_1891_, 1, v___x_1890_);
    v___x_1892_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1892_, 0, v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg___boxed(
    mut v_ref_1893_: *mut LeanObject,
    mut v___y_1894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1895_: *mut LeanObject = core::ptr::null_mut();
    v_res_1895_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1893_);
    return v_res_1895_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9___redArg(
    mut v_x_1896_: *mut LeanObject,
    mut v___y_1897_: *mut LeanObject,
    mut v___y_1898_: *mut LeanObject,
    mut v___y_1899_: *mut LeanObject,
    mut v___y_1900_: *mut LeanObject,
    mut v___y_1901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1908_: u8 = 0;
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1912_: u8 = 0;
    let mut v_fileName_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1925_: u8 = 0;
    let mut v_cancelTk_x3f_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1927_: u8 = 0;
    let mut v_inheritedTraceOptions_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: u8 = 0;
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1913_ = lean_ctor_get(v___y_1900_, 0);
                v_fileMap_1914_ = lean_ctor_get(v___y_1900_, 1);
                v_options_1915_ = lean_ctor_get(v___y_1900_, 2);
                v_currRecDepth_1916_ = lean_ctor_get(v___y_1900_, 3);
                v_maxRecDepth_1917_ = lean_ctor_get(v___y_1900_, 4);
                v_ref_1918_ = lean_ctor_get(v___y_1900_, 5);
                v_currNamespace_1919_ = lean_ctor_get(v___y_1900_, 6);
                v_openDecls_1920_ = lean_ctor_get(v___y_1900_, 7);
                v_initHeartbeats_1921_ = lean_ctor_get(v___y_1900_, 8);
                v_maxHeartbeats_1922_ = lean_ctor_get(v___y_1900_, 9);
                v_quotContext_1923_ = lean_ctor_get(v___y_1900_, 10);
                v_currMacroScope_1924_ = lean_ctor_get(v___y_1900_, 11);
                v_diag_1925_ = lean_ctor_get_uint8(
                    v___y_1900_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1926_ = lean_ctor_get(v___y_1900_, 12);
                v_suppressElabErrors_1927_ = lean_ctor_get_uint8(
                    v___y_1900_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1928_ = lean_ctor_get(v___y_1900_, 13);
                v___x_1934_ = lean_unsigned_to_nat(0);
                v___x_1935_ = lean_nat_dec_eq(v_maxRecDepth_1917_, v___x_1934_);
                if v___x_1935_ == 0 {
                    v___x_1936_ = lean_nat_dec_eq(v_currRecDepth_1916_, v_maxRecDepth_1917_);
                    if v___x_1936_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        lean_dec_ref(v_x_1896_);
                        lean_inc(v_ref_1918_);
                        v___x_1937_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1918_);
                        v___y_1904_ = v___x_1937_;
                        state = 1;
                        continue;
                    }
                } else {
                    state = 4;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v___y_1904_) == 0 {
                    return v___y_1904_;
                } else {
                    v_a_1905_ = lean_ctor_get(v___y_1904_, 0);
                    v_isSharedCheck_1912_ = (!lean_is_exclusive(v___y_1904_)) as u8;
                    if v_isSharedCheck_1912_ == 0 {
                        v___x_1907_ = v___y_1904_;
                        v_isShared_1908_ = v_isSharedCheck_1912_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1905_);
                        lean_dec(v___y_1904_);
                        v___x_1907_ = lean_box(0);
                        v_isShared_1908_ = v_isSharedCheck_1912_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1908_ == 0 {
                    v___x_1910_ = v___x_1907_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
                    v___x_1910_ = v_reuseFailAlloc_1911_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1910_;
            }
            4 => {
                v___x_1930_ = lean_unsigned_to_nat(1);
                v___x_1931_ = lean_nat_add(v_currRecDepth_1916_, v___x_1930_);
                lean_inc_ref(v_inheritedTraceOptions_1928_);
                lean_inc(v_cancelTk_x3f_1926_);
                lean_inc(v_currMacroScope_1924_);
                lean_inc(v_quotContext_1923_);
                lean_inc(v_maxHeartbeats_1922_);
                lean_inc(v_initHeartbeats_1921_);
                lean_inc(v_openDecls_1920_);
                lean_inc(v_currNamespace_1919_);
                lean_inc(v_ref_1918_);
                lean_inc(v_maxRecDepth_1917_);
                lean_inc_ref(v_options_1915_);
                lean_inc_ref(v_fileMap_1914_);
                lean_inc_ref(v_fileName_1913_);
                v___x_1932_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_1932_, 0, v_fileName_1913_);
                lean_ctor_set(v___x_1932_, 1, v_fileMap_1914_);
                lean_ctor_set(v___x_1932_, 2, v_options_1915_);
                lean_ctor_set(v___x_1932_, 3, v___x_1931_);
                lean_ctor_set(v___x_1932_, 4, v_maxRecDepth_1917_);
                lean_ctor_set(v___x_1932_, 5, v_ref_1918_);
                lean_ctor_set(v___x_1932_, 6, v_currNamespace_1919_);
                lean_ctor_set(v___x_1932_, 7, v_openDecls_1920_);
                lean_ctor_set(v___x_1932_, 8, v_initHeartbeats_1921_);
                lean_ctor_set(v___x_1932_, 9, v_maxHeartbeats_1922_);
                lean_ctor_set(v___x_1932_, 10, v_quotContext_1923_);
                lean_ctor_set(v___x_1932_, 11, v_currMacroScope_1924_);
                lean_ctor_set(v___x_1932_, 12, v_cancelTk_x3f_1926_);
                lean_ctor_set(v___x_1932_, 13, v_inheritedTraceOptions_1928_);
                lean_ctor_set_uint8(
                    v___x_1932_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_1925_,
                );
                lean_ctor_set_uint8(
                    v___x_1932_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1927_,
                );
                lean_inc(v___y_1901_);
                lean_inc(v___y_1899_);
                lean_inc_ref(v___y_1898_);
                lean_inc(v___y_1897_);
                v___x_1933_ = lean_apply_6(
                    v_x_1896_,
                    v___y_1897_,
                    v___y_1898_,
                    v___y_1899_,
                    v___x_1932_,
                    v___y_1901_,
                    lean_box(0),
                );
                v___y_1904_ = v___x_1933_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9___redArg___boxed(
    mut v_x_1938_: *mut LeanObject,
    mut v___y_1939_: *mut LeanObject,
    mut v___y_1940_: *mut LeanObject,
    mut v___y_1941_: *mut LeanObject,
    mut v___y_1942_: *mut LeanObject,
    mut v___y_1943_: *mut LeanObject,
    mut v___y_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1945_: *mut LeanObject = core::ptr::null_mut();
    v_res_1945_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9___redArg(v_x_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
    lean_dec(v___y_1943_);
    lean_dec_ref(v___y_1942_);
    lean_dec(v___y_1941_);
    lean_dec_ref(v___y_1940_);
    lean_dec(v___y_1939_);
    return v_res_1945_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4_spec__5___redArg(
    mut v_a_1946_: *mut LeanObject,
    mut v_x_1947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: u8 = 0;
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1947_) == 0 {
                    v___x_1948_ = lean_box(0);
                    return v___x_1948_;
                } else {
                    v_key_1949_ = lean_ctor_get(v_x_1947_, 0);
                    v_value_1950_ = lean_ctor_get(v_x_1947_, 1);
                    v_tail_1951_ = lean_ctor_get(v_x_1947_, 2);
                    v___x_1952_ = l_Lean_ExprStructEq_beq(v_key_1949_, v_a_1946_);
                    if v___x_1952_ == 0 {
                        v_x_1947_ = v_tail_1951_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_1950_);
                        v___x_1954_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1954_, 0, v_value_1950_);
                        return v___x_1954_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4_spec__5___redArg___boxed(
    mut v_a_1955_: *mut LeanObject,
    mut v_x_1956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1957_: *mut LeanObject = core::ptr::null_mut();
    v_res_1957_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1955_, v_x_1956_);
    lean_dec(v_x_1956_);
    lean_dec_ref(v_a_1955_);
    return v_res_1957_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4___redArg(
    mut v_m_1958_: *mut LeanObject,
    mut v_a_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: u64 = 0;
    let mut v___x_1963_: u64 = 0;
    let mut v___x_1964_: u64 = 0;
    let mut v_fold_1965_: u64 = 0;
    let mut v___x_1966_: u64 = 0;
    let mut v___x_1967_: u64 = 0;
    let mut v___x_1968_: u64 = 0;
    let mut v___x_1969_: usize = 0;
    let mut v___x_1970_: usize = 0;
    let mut v___x_1971_: usize = 0;
    let mut v___x_1972_: usize = 0;
    let mut v___x_1973_: usize = 0;
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_1960_ = lean_ctor_get(v_m_1958_, 1);
    v___x_1961_ = lean_array_get_size(v_buckets_1960_);
    v___x_1962_ = l_Lean_ExprStructEq_hash(v_a_1959_);
    v___x_1963_ = 32u64;
    v___x_1964_ = lean_uint64_shift_right(v___x_1962_, v___x_1963_);
    v_fold_1965_ = lean_uint64_xor(v___x_1962_, v___x_1964_);
    v___x_1966_ = 16u64;
    v___x_1967_ = lean_uint64_shift_right(v_fold_1965_, v___x_1966_);
    v___x_1968_ = lean_uint64_xor(v_fold_1965_, v___x_1967_);
    v___x_1969_ = lean_uint64_to_usize(v___x_1968_);
    v___x_1970_ = lean_usize_of_nat(v___x_1961_);
    v___x_1971_ = 1usize;
    v___x_1972_ = lean_usize_sub(v___x_1970_, v___x_1971_);
    v___x_1973_ = lean_usize_land(v___x_1969_, v___x_1972_);
    v___x_1974_ = lean_array_uget_borrowed(v_buckets_1960_, v___x_1973_);
    v___x_1975_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1959_, v___x_1974_);
    return v___x_1975_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4___redArg___boxed(
    mut v_m_1976_: *mut LeanObject,
    mut v_a_1977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1978_: *mut LeanObject = core::ptr::null_mut();
    v_res_1978_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4___redArg(v_m_1976_, v_a_1977_);
    lean_dec_ref(v_a_1977_);
    lean_dec_ref(v_m_1976_);
    return v_res_1978_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__6___lam__0(
    mut v_fvars_1982_: *mut LeanObject,
    mut v_pre_1983_: *mut LeanObject,
    mut v_post_1984_: *mut LeanObject,
    mut v_usedLetOnly_1985_: u8,
    mut v_skipConstInApp_1986_: u8,
    mut v_skipInstances_1987_: u8,
    mut v_body_1988_: *mut LeanObject,
    mut v_x_1989_: *mut LeanObject,
    mut v___y_1990_: *mut LeanObject,
    mut v___y_1991_: *mut LeanObject,
    mut v___y_1992_: *mut LeanObject,
    mut v___y_1993_: *mut LeanObject,
    mut v___y_1994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    v___x_1996_ = lean_array_push(v_fvars_1982_, v_x_1989_);
    v___x_1997_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__6(v_pre_1983_, v_post_1984_, v_usedLetOnly_1985_, v_skipConstInApp_1986_, v_skipInstances_1987_, v___x_1996_, v_body_1988_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
    return v___x_1997_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__6___lam__0___boxed(
    mut v_fvars_1998_: *mut LeanObject,
    mut v_pre_1999_: *mut LeanObject,
    mut v_post_2000_: *mut LeanObject,
    mut v_usedLetOnly_2001_: *mut LeanObject,
    mut v_skipConstInApp_2002_: *mut LeanObject,
    mut v_skipInstances_2003_: *mut LeanObject,
    mut v_body_2004_: *mut LeanObject,
    mut v_x_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
    mut v___y_2008_: *mut LeanObject,
    mut v___y_2009_: *mut LeanObject,
    mut v___y_2010_: *mut LeanObject,
    mut v___y_2011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_2012_: u8 = 0;
    let mut v_skipConstInApp_boxed_2013_: u8 = 0;
    let mut v_skipInstances_boxed_2014_: u8 = 0;
    let mut v_res_2015_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2012_ = (lean_unbox(v_usedLetOnly_2001_) as u8);
    v_skipConstInApp_boxed_2013_ = (lean_unbox(v_skipConstInApp_2002_) as u8);
    v_skipInstances_boxed_2014_ = (lean_unbox(v_skipInstances_2003_) as u8);
    v_res_2015_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__6___lam__0(v_fvars_1998_, v_pre_1999_, v_post_2000_, v_usedLetOnly_boxed_2012_, v_skipConstInApp_boxed_2013_, v_skipInstances_boxed_2014_, v_body_2004_, v_x_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
    lean_dec(v___y_2010_);
    lean_dec_ref(v___y_2009_);
    lean_dec(v___y_2008_);
    lean_dec_ref(v___y_2007_);
    lean_dec(v___y_2006_);
    return v_res_2015_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__2(
    mut v_pre_2016_: *mut LeanObject,
    mut v_post_2017_: *mut LeanObject,
    mut v_usedLetOnly_2018_: u8,
    mut v_skipConstInApp_2019_: u8,
    mut v_skipInstances_2020_: u8,
    mut v_e_2021_: *mut LeanObject,
    mut v_a_2022_: *mut LeanObject,
    mut v___y_2023_: *mut LeanObject,
    mut v___y_2024_: *mut LeanObject,
    mut v___y_2025_: *mut LeanObject,
    mut v___y_2026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v_e_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2047_: u8 = 0;
    let mut v_a_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_post_2017_);
                lean_inc(v___y_2026_);
                lean_inc_ref(v___y_2025_);
                lean_inc(v___y_2024_);
                lean_inc_ref(v___y_2023_);
                lean_inc_ref(v_e_2021_);
                v___x_2028_ = lean_apply_6(
                    v_post_2017_,
                    v_e_2021_,
                    v___y_2023_,
                    v___y_2024_,
                    v___y_2025_,
                    v___y_2026_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2028_) == 0 {
                    v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
                    v_isSharedCheck_2047_ = (!lean_is_exclusive(v___x_2028_)) as u8;
                    if v_isSharedCheck_2047_ == 0 {
                        v___x_2031_ = v___x_2028_;
                        v_isShared_2032_ = v_isSharedCheck_2047_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2029_);
                        lean_dec(v___x_2028_);
                        v___x_2031_ = lean_box(0);
                        v_isShared_2032_ = v_isSharedCheck_2047_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_2021_);
                    lean_dec_ref(v_post_2017_);
                    lean_dec_ref(v_pre_2016_);
                    v_a_2048_ = lean_ctor_get(v___x_2028_, 0);
                    v_isSharedCheck_2055_ = (!lean_is_exclusive(v___x_2028_)) as u8;
                    if v_isSharedCheck_2055_ == 0 {
                        v___x_2050_ = v___x_2028_;
                        v_isShared_2051_ = v_isSharedCheck_2055_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2048_);
                        lean_dec(v___x_2028_);
                        v___x_2050_ = lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2055_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match lean_obj_tag(v_a_2029_) {
                0 => {
                    lean_dec_ref(v_e_2021_);
                    lean_dec_ref(v_post_2017_);
                    lean_dec_ref(v_pre_2016_);
                    v_e_2033_ = lean_ctor_get(v_a_2029_, 0);
                    lean_inc_ref(v_e_2033_);
                    lean_dec_ref_known(v_a_2029_, 1);
                    if v_isShared_2032_ == 0 {
                        lean_ctor_set(v___x_2031_, 0, v_e_2033_);
                        v___x_2035_ = v___x_2031_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_e_2033_);
                        v___x_2035_ = v_reuseFailAlloc_2036_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    lean_del_object(v___x_2031_);
                    lean_dec_ref(v_e_2021_);
                    v_e_2037_ = lean_ctor_get(v_a_2029_, 0);
                    lean_inc_ref(v_e_2037_);
                    lean_dec_ref_known(v_a_2029_, 1);
                    v___x_2038_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2016_, v_post_2017_, v_usedLetOnly_2018_, v_skipConstInApp_2019_, v_skipInstances_2020_, v_e_2037_, v_a_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
                    return v___x_2038_;
                }
                _ => {
                    lean_dec_ref(v_post_2017_);
                    lean_dec_ref(v_pre_2016_);
                    v_e_x3f_2039_ = lean_ctor_get(v_a_2029_, 0);
                    lean_inc(v_e_x3f_2039_);
                    lean_dec_ref_known(v_a_2029_, 1);
                    if lean_obj_tag(v_e_x3f_2039_) == 0 {
                        if v_isShared_2032_ == 0 {
                            lean_ctor_set(v___x_2031_, 0, v_e_2021_);
                            v___x_2041_ = v___x_2031_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_e_2021_);
                            v___x_2041_ = v_reuseFailAlloc_2042_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_2021_);
                        v_val_2043_ = lean_ctor_get(v_e_x3f_2039_, 0);
                        lean_inc(v_val_2043_);
                        lean_dec_ref_known(v_e_x3f_2039_, 1);
                        if v_isShared_2032_ == 0 {
                            lean_ctor_set(v___x_2031_, 0, v_val_2043_);
                            v___x_2045_ = v___x_2031_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_val_2043_);
                            v___x_2045_ = v_reuseFailAlloc_2046_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_2035_;
            }
            3 => {
                return v___x_2041_;
            }
            4 => {
                return v___x_2045_;
            }
            5 => {
                if v_isShared_2051_ == 0 {
                    v___x_2053_ = v___x_2050_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
                    v___x_2053_ = v_reuseFailAlloc_2054_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__6(
    mut v_pre_2056_: *mut LeanObject,
    mut v_post_2057_: *mut LeanObject,
    mut v_usedLetOnly_2058_: u8,
    mut v_skipConstInApp_2059_: u8,
    mut v_skipInstances_2060_: u8,
    mut v_fvars_2061_: *mut LeanObject,
    mut v_e_2062_: *mut LeanObject,
    mut v_a_2063_: *mut LeanObject,
    mut v___y_2064_: *mut LeanObject,
    mut v___y_2065_: *mut LeanObject,
    mut v___y_2066_: *mut LeanObject,
    mut v___y_2067_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_2062_) == 6 {
        let mut v_binderName_2069_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderType_2070_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_2071_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_2072_: u8 = 0;
        let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
        v_binderName_2069_ = lean_ctor_get(v_e_2062_, 0);
        lean_inc(v_binderName_2069_);
        v_binderType_2070_ = lean_ctor_get(v_e_2062_, 1);
        lean_inc_ref(v_binderType_2070_);
        v_body_2071_ = lean_ctor_get(v_e_2062_, 2);
        lean_inc_ref(v_body_2071_);
        v_binderInfo_2072_ = lean_ctor_get_uint8(
            v_e_2062_,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        );
        lean_dec_ref_known(v_e_2062_, 3);
        v___x_2073_ = lean_expr_instantiate_rev(v_binderType_2070_, v_fvars_2061_);
        lean_dec_ref(v_binderType_2070_);
        lean_inc_ref(v_post_2057_);
        lean_inc_ref(v_pre_2056_);
        v___x_2074_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2056_, v_post_2057_, v_usedLetOnly_2058_, v_skipConstInApp_2059_, v_skipInstances_2060_, v___x_2073_, v_a_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
        if lean_obj_tag(v___x_2074_) == 0 {
            let mut v_a_2075_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_2079_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2080_: u8 = 0;
            let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
            v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
            lean_inc(v_a_2075_);
            lean_dec_ref_known(v___x_2074_, 1);
            v___x_2076_ = lean_box((v_usedLetOnly_2058_) as usize);
            v___x_2077_ = lean_box((v_skipConstInApp_2059_) as usize);
            v___x_2078_ = lean_box((v_skipInstances_2060_) as usize);
            v___f_2079_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__6___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
            lean_closure_set(v___f_2079_, 0, v_fvars_2061_);
            lean_closure_set(v___f_2079_, 1, v_pre_2056_);
            lean_closure_set(v___f_2079_, 2, v_post_2057_);
            lean_closure_set(v___f_2079_, 3, v___x_2076_);
            lean_closure_set(v___f_2079_, 4, v___x_2077_);
            lean_closure_set(v___f_2079_, 5, v___x_2078_);
            lean_closure_set(v___f_2079_, 6, v_body_2071_);
            v___x_2080_ = 0;
            v___x_2081_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2069_, v_binderInfo_2072_, v_a_2075_, v___f_2079_, v___x_2080_, v_a_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
            return v___x_2081_;
        } else {
            lean_dec_ref(v_body_2071_);
            lean_dec(v_binderName_2069_);
            lean_dec_ref(v_fvars_2061_);
            lean_dec_ref(v_post_2057_);
            lean_dec_ref(v_pre_2056_);
            return v___x_2074_;
        }
    } else {
        let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
        v___x_2082_ = lean_expr_instantiate_rev(v_e_2062_, v_fvars_2061_);
        lean_dec_ref(v_e_2062_);
        lean_inc_ref(v_post_2057_);
        lean_inc_ref(v_pre_2056_);
        v___x_2083_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2056_, v_post_2057_, v_usedLetOnly_2058_, v_skipConstInApp_2059_, v_skipInstances_2060_, v___x_2082_, v_a_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
        if lean_obj_tag(v___x_2083_) == 0 {
            let mut v_a_2084_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2085_: u8 = 0;
            let mut v___x_2086_: u8 = 0;
            let mut v___x_2087_: u8 = 0;
            let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
            v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
            lean_inc(v_a_2084_);
            lean_dec_ref_known(v___x_2083_, 1);
            v___x_2085_ = 0;
            v___x_2086_ = 1;
            v___x_2087_ = 1;
            v___x_2088_ = l_Lean_Meta_mkLambdaFVars(
                v_fvars_2061_,
                v_a_2084_,
                v___x_2085_,
                v_usedLetOnly_2058_,
                v___x_2085_,
                v___x_2086_,
                v___x_2087_,
                v___y_2064_,
                v___y_2065_,
                v___y_2066_,
                v___y_2067_,
            );
            lean_dec_ref(v_fvars_2061_);
            if lean_obj_tag(v___x_2088_) == 0 {
                let mut v_a_2089_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
                v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
                lean_inc(v_a_2089_);
                lean_dec_ref_known(v___x_2088_, 1);
                v___x_2090_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__2(v_pre_2056_, v_post_2057_, v_usedLetOnly_2058_, v_skipConstInApp_2059_, v_skipInstances_2060_, v_a_2089_, v_a_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
                return v___x_2090_;
            } else {
                lean_dec_ref(v_post_2057_);
                lean_dec_ref(v_pre_2056_);
                return v___x_2088_;
            }
        } else {
            lean_dec_ref(v_fvars_2061_);
            lean_dec_ref(v_post_2057_);
            lean_dec_ref(v_pre_2056_);
            return v___x_2083_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7___lam__0(
    mut v_fvars_2091_: *mut LeanObject,
    mut v_pre_2092_: *mut LeanObject,
    mut v_post_2093_: *mut LeanObject,
    mut v_usedLetOnly_2094_: u8,
    mut v_skipConstInApp_2095_: u8,
    mut v_skipInstances_2096_: u8,
    mut v_body_2097_: *mut LeanObject,
    mut v_x_2098_: *mut LeanObject,
    mut v___y_2099_: *mut LeanObject,
    mut v___y_2100_: *mut LeanObject,
    mut v___y_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    v___x_2105_ = lean_array_push(v_fvars_2091_, v_x_2098_);
    v___x_2106_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7(v_pre_2092_, v_post_2093_, v_usedLetOnly_2094_, v_skipConstInApp_2095_, v_skipInstances_2096_, v___x_2105_, v_body_2097_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
    return v___x_2106_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7___lam__0___boxed(
    mut v_fvars_2107_: *mut LeanObject,
    mut v_pre_2108_: *mut LeanObject,
    mut v_post_2109_: *mut LeanObject,
    mut v_usedLetOnly_2110_: *mut LeanObject,
    mut v_skipConstInApp_2111_: *mut LeanObject,
    mut v_skipInstances_2112_: *mut LeanObject,
    mut v_body_2113_: *mut LeanObject,
    mut v_x_2114_: *mut LeanObject,
    mut v___y_2115_: *mut LeanObject,
    mut v___y_2116_: *mut LeanObject,
    mut v___y_2117_: *mut LeanObject,
    mut v___y_2118_: *mut LeanObject,
    mut v___y_2119_: *mut LeanObject,
    mut v___y_2120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_2121_: u8 = 0;
    let mut v_skipConstInApp_boxed_2122_: u8 = 0;
    let mut v_skipInstances_boxed_2123_: u8 = 0;
    let mut v_res_2124_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2121_ = (lean_unbox(v_usedLetOnly_2110_) as u8);
    v_skipConstInApp_boxed_2122_ = (lean_unbox(v_skipConstInApp_2111_) as u8);
    v_skipInstances_boxed_2123_ = (lean_unbox(v_skipInstances_2112_) as u8);
    v_res_2124_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7___lam__0(v_fvars_2107_, v_pre_2108_, v_post_2109_, v_usedLetOnly_boxed_2121_, v_skipConstInApp_boxed_2122_, v_skipInstances_boxed_2123_, v_body_2113_, v_x_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
    lean_dec(v___y_2119_);
    lean_dec_ref(v___y_2118_);
    lean_dec(v___y_2117_);
    lean_dec_ref(v___y_2116_);
    lean_dec(v___y_2115_);
    return v_res_2124_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7(
    mut v_pre_2125_: *mut LeanObject,
    mut v_post_2126_: *mut LeanObject,
    mut v_usedLetOnly_2127_: u8,
    mut v_skipConstInApp_2128_: u8,
    mut v_skipInstances_2129_: u8,
    mut v_fvars_2130_: *mut LeanObject,
    mut v_e_2131_: *mut LeanObject,
    mut v_a_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
    mut v___y_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
    mut v___y_2136_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_2131_) == 8 {
        let mut v_declName_2138_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_2139_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_2140_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_2141_: *mut LeanObject = core::ptr::null_mut();
        let mut v_nondep_2142_: u8 = 0;
        let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
        v_declName_2138_ = lean_ctor_get(v_e_2131_, 0);
        lean_inc(v_declName_2138_);
        v_type_2139_ = lean_ctor_get(v_e_2131_, 1);
        lean_inc_ref(v_type_2139_);
        v_value_2140_ = lean_ctor_get(v_e_2131_, 2);
        lean_inc_ref(v_value_2140_);
        v_body_2141_ = lean_ctor_get(v_e_2131_, 3);
        lean_inc_ref(v_body_2141_);
        v_nondep_2142_ = lean_ctor_get_uint8(
            v_e_2131_,
            (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
        );
        lean_dec_ref_known(v_e_2131_, 4);
        v___x_2143_ = lean_expr_instantiate_rev(v_type_2139_, v_fvars_2130_);
        lean_dec_ref(v_type_2139_);
        lean_inc_ref(v_post_2126_);
        lean_inc_ref(v_pre_2125_);
        v___x_2144_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2125_, v_post_2126_, v_usedLetOnly_2127_, v_skipConstInApp_2128_, v_skipInstances_2129_, v___x_2143_, v_a_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
        if lean_obj_tag(v___x_2144_) == 0 {
            let mut v_a_2145_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
            v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
            lean_inc(v_a_2145_);
            lean_dec_ref_known(v___x_2144_, 1);
            v___x_2146_ = lean_expr_instantiate_rev(v_value_2140_, v_fvars_2130_);
            lean_dec_ref(v_value_2140_);
            lean_inc_ref(v_post_2126_);
            lean_inc_ref(v_pre_2125_);
            v___x_2147_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2125_, v_post_2126_, v_usedLetOnly_2127_, v_skipConstInApp_2128_, v_skipInstances_2129_, v___x_2146_, v_a_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
            if lean_obj_tag(v___x_2147_) == 0 {
                let mut v_a_2148_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
                let mut v___f_2152_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2153_: u8 = 0;
                let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
                v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
                lean_inc(v_a_2148_);
                lean_dec_ref_known(v___x_2147_, 1);
                v___x_2149_ = lean_box((v_usedLetOnly_2127_) as usize);
                v___x_2150_ = lean_box((v_skipConstInApp_2128_) as usize);
                v___x_2151_ = lean_box((v_skipInstances_2129_) as usize);
                v___f_2152_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
                lean_closure_set(v___f_2152_, 0, v_fvars_2130_);
                lean_closure_set(v___f_2152_, 1, v_pre_2125_);
                lean_closure_set(v___f_2152_, 2, v_post_2126_);
                lean_closure_set(v___f_2152_, 3, v___x_2149_);
                lean_closure_set(v___f_2152_, 4, v___x_2150_);
                lean_closure_set(v___f_2152_, 5, v___x_2151_);
                lean_closure_set(v___f_2152_, 6, v_body_2141_);
                v___x_2153_ = 0;
                v___x_2154_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_2138_, v_a_2145_, v_a_2148_, v___f_2152_, v_nondep_2142_, v___x_2153_, v_a_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
                return v___x_2154_;
            } else {
                lean_dec(v_a_2145_);
                lean_dec_ref(v_body_2141_);
                lean_dec(v_declName_2138_);
                lean_dec_ref(v_fvars_2130_);
                lean_dec_ref(v_post_2126_);
                lean_dec_ref(v_pre_2125_);
                return v___x_2147_;
            }
        } else {
            lean_dec_ref(v_body_2141_);
            lean_dec_ref(v_value_2140_);
            lean_dec(v_declName_2138_);
            lean_dec_ref(v_fvars_2130_);
            lean_dec_ref(v_post_2126_);
            lean_dec_ref(v_pre_2125_);
            return v___x_2144_;
        }
    } else {
        let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
        v___x_2155_ = lean_expr_instantiate_rev(v_e_2131_, v_fvars_2130_);
        lean_dec_ref(v_e_2131_);
        lean_inc_ref(v_post_2126_);
        lean_inc_ref(v_pre_2125_);
        v___x_2156_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2125_, v_post_2126_, v_usedLetOnly_2127_, v_skipConstInApp_2128_, v_skipInstances_2129_, v___x_2155_, v_a_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
        if lean_obj_tag(v___x_2156_) == 0 {
            let mut v_a_2157_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2158_: u8 = 0;
            let mut v___x_2159_: u8 = 0;
            let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
            v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
            lean_inc(v_a_2157_);
            lean_dec_ref_known(v___x_2156_, 1);
            v___x_2158_ = 0;
            v___x_2159_ = 1;
            v___x_2160_ = l_Lean_Meta_mkLetFVars(
                v_fvars_2130_,
                v_a_2157_,
                v_usedLetOnly_2127_,
                v___x_2158_,
                v___x_2159_,
                v___y_2133_,
                v___y_2134_,
                v___y_2135_,
                v___y_2136_,
            );
            lean_dec_ref(v_fvars_2130_);
            if lean_obj_tag(v___x_2160_) == 0 {
                let mut v_a_2161_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
                v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
                lean_inc(v_a_2161_);
                lean_dec_ref_known(v___x_2160_, 1);
                v___x_2162_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__2(v_pre_2125_, v_post_2126_, v_usedLetOnly_2127_, v_skipConstInApp_2128_, v_skipInstances_2129_, v_a_2161_, v_a_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
                return v___x_2162_;
            } else {
                lean_dec_ref(v_post_2126_);
                lean_dec_ref(v_pre_2125_);
                return v___x_2160_;
            }
        } else {
            lean_dec_ref(v_fvars_2130_);
            lean_dec_ref(v_post_2126_);
            lean_dec_ref(v_pre_2125_);
            return v___x_2156_;
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2164_: *mut LeanObject = core::ptr::null_mut();
    v___x_2163_ = lean_box(0);
    v_dummy_2164_ = l_Lean_Expr_sort___override(v___x_2163_);
    return v_dummy_2164_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__1(
    mut v_pre_2165_: *mut LeanObject,
    mut v_post_2166_: *mut LeanObject,
    mut v_usedLetOnly_2167_: u8,
    mut v_skipConstInApp_2168_: u8,
    mut v_skipInstances_2169_: u8,
    mut v_sz_2170_: usize,
    mut v_i_2171_: usize,
    mut v_bs_2172_: *mut LeanObject,
    mut v___y_2173_: *mut LeanObject,
    mut v___y_2174_: *mut LeanObject,
    mut v___y_2175_: *mut LeanObject,
    mut v___y_2176_: *mut LeanObject,
    mut v___y_2177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2179_: u8 = 0;
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: usize = 0;
    let mut v___x_2187_: usize = 0;
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2193_: u8 = 0;
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2179_ = lean_usize_dec_lt(v_i_2171_, v_sz_2170_);
                if v___x_2179_ == 0 {
                    lean_dec_ref(v_post_2166_);
                    lean_dec_ref(v_pre_2165_);
                    v___x_2180_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2180_, 0, v_bs_2172_);
                    return v___x_2180_;
                } else {
                    v_v_2181_ = lean_array_uget_borrowed(v_bs_2172_, v_i_2171_);
                    lean_inc(v_v_2181_);
                    lean_inc_ref(v_post_2166_);
                    lean_inc_ref(v_pre_2165_);
                    v___x_2182_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2165_, v_post_2166_, v_usedLetOnly_2167_, v_skipConstInApp_2168_, v_skipInstances_2169_, v_v_2181_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
                    if lean_obj_tag(v___x_2182_) == 0 {
                        v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
                        lean_inc(v_a_2183_);
                        lean_dec_ref_known(v___x_2182_, 1);
                        v___x_2184_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2185_ = lean_array_uset(v_bs_2172_, v_i_2171_, v___x_2184_);
                        v___x_2186_ = 1usize;
                        v___x_2187_ = lean_usize_add(v_i_2171_, v___x_2186_);
                        v___x_2188_ = lean_array_uset(v_bs_x27_2185_, v_i_2171_, v_a_2183_);
                        v_i_2171_ = v___x_2187_;
                        v_bs_2172_ = v___x_2188_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_2172_);
                        lean_dec_ref(v_post_2166_);
                        lean_dec_ref(v_pre_2165_);
                        v_a_2190_ = lean_ctor_get(v___x_2182_, 0);
                        v_isSharedCheck_2197_ = (!lean_is_exclusive(v___x_2182_)) as u8;
                        if v_isSharedCheck_2197_ == 0 {
                            v___x_2192_ = v___x_2182_;
                            v_isShared_2193_ = v_isSharedCheck_2197_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2190_);
                            lean_dec(v___x_2182_);
                            v___x_2192_ = lean_box(0);
                            v_isShared_2193_ = v_isSharedCheck_2197_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2193_ == 0 {
                    v___x_2195_ = v___x_2192_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
                    v___x_2195_ = v_reuseFailAlloc_2196_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___redArg___lam__0(
    mut v_pre_2198_: *mut LeanObject,
    mut v_post_2199_: *mut LeanObject,
    mut v_usedLetOnly_2200_: u8,
    mut v_skipConstInApp_2201_: u8,
    mut v_skipInstances_2202_: u8,
    mut v___x_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
    mut v_b_2205_: *mut LeanObject,
    mut v_a_2206_: *mut LeanObject,
    mut v___y_2207_: *mut LeanObject,
    mut v___y_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
    mut v___y_2210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2222_: u8 = 0;
    let mut v_a_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2230_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2212_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2198_, v_post_2199_, v_usedLetOnly_2200_, v_skipConstInApp_2201_, v_skipInstances_2202_, v___x_2203_, v___y_2204_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
                if lean_obj_tag(v___x_2212_) == 0 {
                    v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
                    v_isSharedCheck_2222_ = (!lean_is_exclusive(v___x_2212_)) as u8;
                    if v_isSharedCheck_2222_ == 0 {
                        v___x_2215_ = v___x_2212_;
                        v_isShared_2216_ = v_isSharedCheck_2222_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2213_);
                        lean_dec(v___x_2212_);
                        v___x_2215_ = lean_box(0);
                        v_isShared_2216_ = v_isSharedCheck_2222_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_b_2205_);
                    v_a_2223_ = lean_ctor_get(v___x_2212_, 0);
                    v_isSharedCheck_2230_ = (!lean_is_exclusive(v___x_2212_)) as u8;
                    if v_isSharedCheck_2230_ == 0 {
                        v___x_2225_ = v___x_2212_;
                        v_isShared_2226_ = v_isSharedCheck_2230_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2223_);
                        lean_dec(v___x_2212_);
                        v___x_2225_ = lean_box(0);
                        v_isShared_2226_ = v_isSharedCheck_2230_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2217_ = lean_array_fset(v_b_2205_, v_a_2206_, v_a_2213_);
                v___x_2218_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2218_, 0, v___x_2217_);
                if v_isShared_2216_ == 0 {
                    lean_ctor_set(v___x_2215_, 0, v___x_2218_);
                    v___x_2220_ = v___x_2215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
                    v___x_2220_ = v_reuseFailAlloc_2221_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2220_;
            }
            3 => {
                if v_isShared_2226_ == 0 {
                    v___x_2228_ = v___x_2225_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
                    v___x_2228_ = v_reuseFailAlloc_2229_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2228_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___redArg___lam__0___boxed(
    mut v_pre_2231_: *mut LeanObject,
    mut v_post_2232_: *mut LeanObject,
    mut v_usedLetOnly_2233_: *mut LeanObject,
    mut v_skipConstInApp_2234_: *mut LeanObject,
    mut v_skipInstances_2235_: *mut LeanObject,
    mut v___x_2236_: *mut LeanObject,
    mut v___y_2237_: *mut LeanObject,
    mut v_b_2238_: *mut LeanObject,
    mut v_a_2239_: *mut LeanObject,
    mut v___y_2240_: *mut LeanObject,
    mut v___y_2241_: *mut LeanObject,
    mut v___y_2242_: *mut LeanObject,
    mut v___y_2243_: *mut LeanObject,
    mut v___y_2244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_2245_: u8 = 0;
    let mut v_skipConstInApp_boxed_2246_: u8 = 0;
    let mut v_skipInstances_boxed_2247_: u8 = 0;
    let mut v_res_2248_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2245_ = (lean_unbox(v_usedLetOnly_2233_) as u8);
    v_skipConstInApp_boxed_2246_ = (lean_unbox(v_skipConstInApp_2234_) as u8);
    v_skipInstances_boxed_2247_ = (lean_unbox(v_skipInstances_2235_) as u8);
    v_res_2248_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_2231_, v_post_2232_, v_usedLetOnly_boxed_2245_, v_skipConstInApp_boxed_2246_, v_skipInstances_boxed_2247_, v___x_2236_, v___y_2237_, v_b_2238_, v_a_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
    lean_dec(v___y_2243_);
    lean_dec_ref(v___y_2242_);
    lean_dec(v___y_2241_);
    lean_dec_ref(v___y_2240_);
    lean_dec(v_a_2239_);
    lean_dec(v___y_2237_);
    return v_res_2248_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___redArg(
    mut v_upperBound_2249_: *mut LeanObject,
    mut v___x_2250_: *mut LeanObject,
    mut v_pre_2251_: *mut LeanObject,
    mut v_post_2252_: *mut LeanObject,
    mut v_usedLetOnly_2253_: u8,
    mut v_skipConstInApp_2254_: u8,
    mut v_skipInstances_2255_: u8,
    mut v_a_2256_: *mut LeanObject,
    mut v_b_2257_: *mut LeanObject,
    mut v___y_2258_: *mut LeanObject,
    mut v___y_2259_: *mut LeanObject,
    mut v___y_2260_: *mut LeanObject,
    mut v___y_2261_: *mut LeanObject,
    mut v___y_2262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2270_: u8 = 0;
    let mut v_a_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2279_: u8 = 0;
    let mut v_a_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2283_: u8 = 0;
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2287_: u8 = 0;
    let mut v___x_2288_: u8 = 0;
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isInstance_2298_: u8 = 0;
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2288_ = lean_nat_dec_lt(v_a_2256_, v_upperBound_2249_);
                if v___x_2288_ == 0 {
                    lean_dec(v_a_2256_);
                    lean_dec_ref(v_post_2252_);
                    lean_dec_ref(v_pre_2251_);
                    v___x_2289_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2289_, 0, v_b_2257_);
                    return v___x_2289_;
                } else {
                    v___x_2290_ = lean_array_fget_borrowed(v_b_2257_, v_a_2256_);
                    v___x_2291_ = lean_array_get_size(v___x_2250_);
                    v___x_2292_ = lean_nat_dec_lt(v_a_2256_, v___x_2291_);
                    if v___x_2292_ == 0 {
                        lean_inc(v___x_2290_);
                        v___x_2293_ = lean_box((v_usedLetOnly_2253_) as usize);
                        v___x_2294_ = lean_box((v_skipConstInApp_2254_) as usize);
                        v___x_2295_ = lean_box((v_skipInstances_2255_) as usize);
                        lean_inc(v_a_2256_);
                        lean_inc(v___y_2258_);
                        lean_inc_ref(v_post_2252_);
                        lean_inc_ref(v_pre_2251_);
                        v___f_2296_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 9);
                        lean_closure_set(v___f_2296_, 0, v_pre_2251_);
                        lean_closure_set(v___f_2296_, 1, v_post_2252_);
                        lean_closure_set(v___f_2296_, 2, v___x_2293_);
                        lean_closure_set(v___f_2296_, 3, v___x_2294_);
                        lean_closure_set(v___f_2296_, 4, v___x_2295_);
                        lean_closure_set(v___f_2296_, 5, v___x_2290_);
                        lean_closure_set(v___f_2296_, 6, v___y_2258_);
                        lean_closure_set(v___f_2296_, 7, v_b_2257_);
                        lean_closure_set(v___f_2296_, 8, v_a_2256_);
                        v___y_2265_ = v___f_2296_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2297_ = lean_array_fget_borrowed(v___x_2250_, v_a_2256_);
                        v_isInstance_2298_ = lean_ctor_get_uint8(
                            v___x_2297_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 4) as u32,
                        );
                        if v_isInstance_2298_ == 0 {
                            lean_inc(v___x_2290_);
                            v___x_2299_ = lean_box((v_usedLetOnly_2253_) as usize);
                            v___x_2300_ = lean_box((v_skipConstInApp_2254_) as usize);
                            v___x_2301_ = lean_box((v_skipInstances_2255_) as usize);
                            lean_inc(v_a_2256_);
                            lean_inc(v___y_2258_);
                            lean_inc_ref(v_post_2252_);
                            lean_inc_ref(v_pre_2251_);
                            v___f_2302_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 9);
                            lean_closure_set(v___f_2302_, 0, v_pre_2251_);
                            lean_closure_set(v___f_2302_, 1, v_post_2252_);
                            lean_closure_set(v___f_2302_, 2, v___x_2299_);
                            lean_closure_set(v___f_2302_, 3, v___x_2300_);
                            lean_closure_set(v___f_2302_, 4, v___x_2301_);
                            lean_closure_set(v___f_2302_, 5, v___x_2290_);
                            lean_closure_set(v___f_2302_, 6, v___y_2258_);
                            lean_closure_set(v___f_2302_, 7, v_b_2257_);
                            lean_closure_set(v___f_2302_, 8, v_a_2256_);
                            v___y_2265_ = v___f_2302_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2303_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2303_, 0, v_b_2257_);
                            v___f_2304_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 1);
                            lean_closure_set(v___f_2304_, 0, v___x_2303_);
                            v___y_2265_ = v___f_2304_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v___y_2262_);
                lean_inc_ref(v___y_2261_);
                lean_inc(v___y_2260_);
                lean_inc_ref(v___y_2259_);
                v___x_2266_ = lean_apply_5(
                    v___y_2265_,
                    v___y_2259_,
                    v___y_2260_,
                    v___y_2261_,
                    v___y_2262_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2266_) == 0 {
                    v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
                    v_isSharedCheck_2279_ = (!lean_is_exclusive(v___x_2266_)) as u8;
                    if v_isSharedCheck_2279_ == 0 {
                        v___x_2269_ = v___x_2266_;
                        v_isShared_2270_ = v_isSharedCheck_2279_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2267_);
                        lean_dec(v___x_2266_);
                        v___x_2269_ = lean_box(0);
                        v_isShared_2270_ = v_isSharedCheck_2279_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2256_);
                    lean_dec_ref(v_post_2252_);
                    lean_dec_ref(v_pre_2251_);
                    v_a_2280_ = lean_ctor_get(v___x_2266_, 0);
                    v_isSharedCheck_2287_ = (!lean_is_exclusive(v___x_2266_)) as u8;
                    if v_isSharedCheck_2287_ == 0 {
                        v___x_2282_ = v___x_2266_;
                        v_isShared_2283_ = v_isSharedCheck_2287_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2280_);
                        lean_dec(v___x_2266_);
                        v___x_2282_ = lean_box(0);
                        v_isShared_2283_ = v_isSharedCheck_2287_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_2267_) == 0 {
                    lean_dec(v_a_2256_);
                    lean_dec_ref(v_post_2252_);
                    lean_dec_ref(v_pre_2251_);
                    v_a_2271_ = lean_ctor_get(v_a_2267_, 0);
                    lean_inc(v_a_2271_);
                    lean_dec_ref_known(v_a_2267_, 1);
                    if v_isShared_2270_ == 0 {
                        lean_ctor_set(v___x_2269_, 0, v_a_2271_);
                        v___x_2273_ = v___x_2269_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2271_);
                        v___x_2273_ = v_reuseFailAlloc_2274_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2269_);
                    v_a_2275_ = lean_ctor_get(v_a_2267_, 0);
                    lean_inc(v_a_2275_);
                    lean_dec_ref_known(v_a_2267_, 1);
                    v___x_2276_ = lean_unsigned_to_nat(1);
                    v___x_2277_ = lean_nat_add(v_a_2256_, v___x_2276_);
                    lean_dec(v_a_2256_);
                    v_a_2256_ = v___x_2277_;
                    v_b_2257_ = v_a_2275_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_2273_;
            }
            4 => {
                if v_isShared_2283_ == 0 {
                    v___x_2285_ = v___x_2282_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
                    v___x_2285_ = v_reuseFailAlloc_2286_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__8(
    mut v_skipInstances_2305_: u8,
    mut v_pre_2306_: *mut LeanObject,
    mut v_post_2307_: *mut LeanObject,
    mut v_usedLetOnly_2308_: u8,
    mut v_skipConstInApp_2309_: u8,
    mut v_x_2310_: *mut LeanObject,
    mut v_x_2311_: *mut LeanObject,
    mut v_x_2312_: *mut LeanObject,
    mut v___y_2313_: *mut LeanObject,
    mut v___y_2314_: *mut LeanObject,
    mut v___y_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
    mut v___y_2317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_f_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2326_: usize = 0;
    let mut v___x_2327_: usize = 0;
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2335_: u8 = 0;
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2339_: u8 = 0;
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2356_: u8 = 0;
    let mut v_a_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2360_: u8 = 0;
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2364_: u8 = 0;
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2310_) == 5 {
                    v_fn_2368_ = lean_ctor_get(v_x_2310_, 0);
                    lean_inc_ref(v_fn_2368_);
                    v_arg_2369_ = lean_ctor_get(v_x_2310_, 1);
                    lean_inc_ref(v_arg_2369_);
                    lean_dec_ref_known(v_x_2310_, 2);
                    v___x_2370_ = lean_array_set(v_x_2311_, v_x_2312_, v_arg_2369_);
                    v___x_2371_ = lean_unsigned_to_nat(1);
                    v___x_2372_ = lean_nat_sub(v_x_2312_, v___x_2371_);
                    lean_dec(v_x_2312_);
                    v_x_2310_ = v_fn_2368_;
                    v_x_2311_ = v___x_2370_;
                    v_x_2312_ = v___x_2372_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_2312_);
                    if v_skipConstInApp_2309_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        v___x_2374_ = l_Lean_Expr_isConst(v_x_2310_);
                        if v___x_2374_ == 0 {
                            state = 8;
                            continue;
                        } else {
                            v_f_2320_ = v_x_2310_;
                            v___y_2321_ = v___y_2313_;
                            v___y_2322_ = v___y_2314_;
                            v___y_2323_ = v___y_2315_;
                            v___y_2324_ = v___y_2316_;
                            v___y_2325_ = v___y_2317_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_skipInstances_2305_ == 0 {
                    v_sz_2326_ = lean_array_size(v_x_2311_);
                    v___x_2327_ = 0usize;
                    lean_inc_ref(v_post_2307_);
                    lean_inc_ref(v_pre_2306_);
                    v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__1(v_pre_2306_, v_post_2307_, v_usedLetOnly_2308_, v_skipConstInApp_2309_, v_skipInstances_2305_, v_sz_2326_, v___x_2327_, v_x_2311_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
                    if lean_obj_tag(v___x_2328_) == 0 {
                        v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
                        lean_inc(v_a_2329_);
                        lean_dec_ref_known(v___x_2328_, 1);
                        v___x_2330_ = l_Lean_mkAppN(v_f_2320_, v_a_2329_);
                        lean_dec(v_a_2329_);
                        v___x_2331_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__2(v_pre_2306_, v_post_2307_, v_usedLetOnly_2308_, v_skipConstInApp_2309_, v_skipInstances_2305_, v___x_2330_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
                        return v___x_2331_;
                    } else {
                        lean_dec_ref(v_f_2320_);
                        lean_dec_ref(v_post_2307_);
                        lean_dec_ref(v_pre_2306_);
                        v_a_2332_ = lean_ctor_get(v___x_2328_, 0);
                        v_isSharedCheck_2339_ = (!lean_is_exclusive(v___x_2328_)) as u8;
                        if v_isSharedCheck_2339_ == 0 {
                            v___x_2334_ = v___x_2328_;
                            v_isShared_2335_ = v_isSharedCheck_2339_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2332_);
                            lean_dec(v___x_2328_);
                            v___x_2334_ = lean_box(0);
                            v_isShared_2335_ = v_isSharedCheck_2339_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_2340_ = lean_array_get_size(v_x_2311_);
                    lean_inc_ref(v_f_2320_);
                    v___x_2341_ = l_Lean_Meta_getFunInfoNArgs(
                        v_f_2320_,
                        v___x_2340_,
                        v___y_2322_,
                        v___y_2323_,
                        v___y_2324_,
                        v___y_2325_,
                    );
                    if lean_obj_tag(v___x_2341_) == 0 {
                        v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
                        lean_inc(v_a_2342_);
                        lean_dec_ref_known(v___x_2341_, 1);
                        v_paramInfo_2343_ = lean_ctor_get(v_a_2342_, 0);
                        lean_inc_ref(v_paramInfo_2343_);
                        lean_dec(v_a_2342_);
                        v___x_2344_ = lean_unsigned_to_nat(0);
                        lean_inc_ref(v_post_2307_);
                        lean_inc_ref(v_pre_2306_);
                        v___x_2345_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___redArg(v___x_2340_, v_paramInfo_2343_, v_pre_2306_, v_post_2307_, v_usedLetOnly_2308_, v_skipConstInApp_2309_, v_skipInstances_2305_, v___x_2344_, v_x_2311_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
                        lean_dec_ref(v_paramInfo_2343_);
                        if lean_obj_tag(v___x_2345_) == 0 {
                            v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
                            lean_inc(v_a_2346_);
                            lean_dec_ref_known(v___x_2345_, 1);
                            v___x_2347_ = l_Lean_mkAppN(v_f_2320_, v_a_2346_);
                            lean_dec(v_a_2346_);
                            v___x_2348_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__2(v_pre_2306_, v_post_2307_, v_usedLetOnly_2308_, v_skipConstInApp_2309_, v_skipInstances_2305_, v___x_2347_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
                            return v___x_2348_;
                        } else {
                            lean_dec_ref(v_f_2320_);
                            lean_dec_ref(v_post_2307_);
                            lean_dec_ref(v_pre_2306_);
                            v_a_2349_ = lean_ctor_get(v___x_2345_, 0);
                            v_isSharedCheck_2356_ = (!lean_is_exclusive(v___x_2345_)) as u8;
                            if v_isSharedCheck_2356_ == 0 {
                                v___x_2351_ = v___x_2345_;
                                v_isShared_2352_ = v_isSharedCheck_2356_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_2349_);
                                lean_dec(v___x_2345_);
                                v___x_2351_ = lean_box(0);
                                v_isShared_2352_ = v_isSharedCheck_2356_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_f_2320_);
                        lean_dec_ref(v_x_2311_);
                        lean_dec_ref(v_post_2307_);
                        lean_dec_ref(v_pre_2306_);
                        v_a_2357_ = lean_ctor_get(v___x_2341_, 0);
                        v_isSharedCheck_2364_ = (!lean_is_exclusive(v___x_2341_)) as u8;
                        if v_isSharedCheck_2364_ == 0 {
                            v___x_2359_ = v___x_2341_;
                            v_isShared_2360_ = v_isSharedCheck_2364_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2357_);
                            lean_dec(v___x_2341_);
                            v___x_2359_ = lean_box(0);
                            v_isShared_2360_ = v_isSharedCheck_2364_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2335_ == 0 {
                    v___x_2337_ = v___x_2334_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
                    v___x_2337_ = v_reuseFailAlloc_2338_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2337_;
            }
            4 => {
                if v_isShared_2352_ == 0 {
                    v___x_2354_ = v___x_2351_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
                    v___x_2354_ = v_reuseFailAlloc_2355_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2354_;
            }
            6 => {
                if v_isShared_2360_ == 0 {
                    v___x_2362_ = v___x_2359_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
                    v___x_2362_ = v_reuseFailAlloc_2363_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2362_;
            }
            8 => {
                lean_inc_ref(v_post_2307_);
                lean_inc_ref(v_pre_2306_);
                v___x_2366_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2306_, v_post_2307_, v_usedLetOnly_2308_, v_skipConstInApp_2309_, v_skipInstances_2305_, v_x_2310_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
                if lean_obj_tag(v___x_2366_) == 0 {
                    v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
                    lean_inc(v_a_2367_);
                    lean_dec_ref_known(v___x_2366_, 1);
                    v_f_2320_ = v_a_2367_;
                    v___y_2321_ = v___y_2313_;
                    v___y_2322_ = v___y_2314_;
                    v___y_2323_ = v___y_2315_;
                    v___y_2324_ = v___y_2316_;
                    v___y_2325_ = v___y_2317_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_x_2311_);
                    lean_dec_ref(v_post_2307_);
                    lean_dec_ref(v_pre_2306_);
                    return v___x_2366_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1(
    mut v___x_2375_: *mut LeanObject,
    mut v_pre_2376_: *mut LeanObject,
    mut v_e_2377_: *mut LeanObject,
    mut v_post_2378_: *mut LeanObject,
    mut v_usedLetOnly_2379_: u8,
    mut v_skipConstInApp_2380_: u8,
    mut v_skipInstances_2381_: u8,
    mut v___y_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
    mut v___y_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2393_: u8 = 0;
    let mut v___y_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: usize = 0;
    let mut v___x_2413_: usize = 0;
    let mut v___x_2414_: u8 = 0;
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: usize = 0;
    let mut v___x_2424_: usize = 0;
    let mut v___x_2425_: u8 = 0;
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2438_: u8 = 0;
    let mut v_a_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2442_: u8 = 0;
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2446_: u8 = 0;
    let mut v_a_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2450_: u8 = 0;
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2388_ = l_Lean_Core_checkSystem(v___x_2375_, v___y_2385_, v___y_2386_);
                if lean_obj_tag(v___x_2388_) == 0 {
                    lean_dec_ref_known(v___x_2388_, 1);
                    lean_inc_ref(v_pre_2376_);
                    lean_inc(v___y_2386_);
                    lean_inc_ref(v___y_2385_);
                    lean_inc(v___y_2384_);
                    lean_inc_ref(v___y_2383_);
                    lean_inc_ref(v_e_2377_);
                    v___x_2389_ = lean_apply_6(
                        v_pre_2376_,
                        v_e_2377_,
                        v___y_2383_,
                        v___y_2384_,
                        v___y_2385_,
                        v___y_2386_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_2389_) == 0 {
                        v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
                        v_isSharedCheck_2438_ = (!lean_is_exclusive(v___x_2389_)) as u8;
                        if v_isSharedCheck_2438_ == 0 {
                            v___x_2392_ = v___x_2389_;
                            v_isShared_2393_ = v_isSharedCheck_2438_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2390_);
                            lean_dec(v___x_2389_);
                            v___x_2392_ = lean_box(0);
                            v_isShared_2393_ = v_isSharedCheck_2438_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_post_2378_);
                        lean_dec_ref(v_e_2377_);
                        lean_dec_ref(v_pre_2376_);
                        v_a_2439_ = lean_ctor_get(v___x_2389_, 0);
                        v_isSharedCheck_2446_ = (!lean_is_exclusive(v___x_2389_)) as u8;
                        if v_isSharedCheck_2446_ == 0 {
                            v___x_2441_ = v___x_2389_;
                            v_isShared_2442_ = v_isSharedCheck_2446_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2439_);
                            lean_dec(v___x_2389_);
                            v___x_2441_ = lean_box(0);
                            v_isShared_2442_ = v_isSharedCheck_2446_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_post_2378_);
                    lean_dec_ref(v_e_2377_);
                    lean_dec_ref(v_pre_2376_);
                    v_a_2447_ = lean_ctor_get(v___x_2388_, 0);
                    v_isSharedCheck_2454_ = (!lean_is_exclusive(v___x_2388_)) as u8;
                    if v_isSharedCheck_2454_ == 0 {
                        v___x_2449_ = v___x_2388_;
                        v_isShared_2450_ = v_isSharedCheck_2454_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2447_);
                        lean_dec(v___x_2388_);
                        v___x_2449_ = lean_box(0);
                        v_isShared_2450_ = v_isSharedCheck_2454_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => match lean_obj_tag(v_a_2390_) {
                0 => {
                    lean_dec_ref(v_post_2378_);
                    lean_dec_ref(v_e_2377_);
                    lean_dec_ref(v_pre_2376_);
                    v_e_2430_ = lean_ctor_get(v_a_2390_, 0);
                    lean_inc_ref(v_e_2430_);
                    lean_dec_ref_known(v_a_2390_, 1);
                    if v_isShared_2393_ == 0 {
                        lean_ctor_set(v___x_2392_, 0, v_e_2430_);
                        v___x_2432_ = v___x_2392_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_e_2430_);
                        v___x_2432_ = v_reuseFailAlloc_2433_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    lean_del_object(v___x_2392_);
                    lean_dec_ref(v_e_2377_);
                    v_e_2434_ = lean_ctor_get(v_a_2390_, 0);
                    lean_inc_ref(v_e_2434_);
                    lean_dec_ref_known(v_a_2390_, 1);
                    v___x_2435_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2376_, v_post_2378_, v_usedLetOnly_2379_, v_skipConstInApp_2380_, v_skipInstances_2381_, v_e_2434_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                    return v___x_2435_;
                }
                _ => {
                    lean_del_object(v___x_2392_);
                    v_e_x3f_2436_ = lean_ctor_get(v_a_2390_, 0);
                    lean_inc(v_e_x3f_2436_);
                    lean_dec_ref_known(v_a_2390_, 1);
                    if lean_obj_tag(v_e_x3f_2436_) == 0 {
                        v___y_2395_ = v_e_2377_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v_e_2377_);
                        v_val_2437_ = lean_ctor_get(v_e_x3f_2436_, 0);
                        lean_inc(v_val_2437_);
                        lean_dec_ref_known(v_e_x3f_2436_, 1);
                        v___y_2395_ = v_val_2437_;
                        state = 2;
                        continue;
                    }
                }
            },
            2 => match lean_obj_tag(v___y_2395_) {
                7 => {
                    v___x_2396_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1___closed__0;
                    v___x_2397_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5(v_pre_2376_, v_post_2378_, v_usedLetOnly_2379_, v_skipConstInApp_2380_, v_skipInstances_2381_, v___x_2396_, v___y_2395_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                    return v___x_2397_;
                }
                6 => {
                    v___x_2398_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1___closed__0;
                    v___x_2399_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__6(v_pre_2376_, v_post_2378_, v_usedLetOnly_2379_, v_skipConstInApp_2380_, v_skipInstances_2381_, v___x_2398_, v___y_2395_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                    return v___x_2399_;
                }
                8 => {
                    v___x_2400_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1___closed__0;
                    v___x_2401_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7(v_pre_2376_, v_post_2378_, v_usedLetOnly_2379_, v_skipConstInApp_2380_, v_skipInstances_2381_, v___x_2400_, v___y_2395_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                    return v___x_2401_;
                }
                5 => {
                    v_dummy_2402_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1___closed__1_once), _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1___closed__1);
                    v_nargs_2403_ = l_Lean_Expr_getAppNumArgs(v___y_2395_);
                    lean_inc(v_nargs_2403_);
                    v___x_2404_ = lean_mk_array(v_nargs_2403_, v_dummy_2402_);
                    v___x_2405_ = lean_unsigned_to_nat(1);
                    v___x_2406_ = lean_nat_sub(v_nargs_2403_, v___x_2405_);
                    lean_dec(v_nargs_2403_);
                    v___x_2407_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__8(v_skipInstances_2381_, v_pre_2376_, v_post_2378_, v_usedLetOnly_2379_, v_skipConstInApp_2380_, v___y_2395_, v___x_2404_, v___x_2406_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                    return v___x_2407_;
                }
                10 => {
                    v_data_2408_ = lean_ctor_get(v___y_2395_, 0);
                    v_expr_2409_ = lean_ctor_get(v___y_2395_, 1);
                    lean_inc_ref(v_expr_2409_);
                    lean_inc_ref(v_post_2378_);
                    lean_inc_ref(v_pre_2376_);
                    v___x_2410_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2376_, v_post_2378_, v_usedLetOnly_2379_, v_skipConstInApp_2380_, v_skipInstances_2381_, v_expr_2409_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                    if lean_obj_tag(v___x_2410_) == 0 {
                        v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
                        lean_inc(v_a_2411_);
                        lean_dec_ref_known(v___x_2410_, 1);
                        v___x_2412_ = lean_ptr_addr(v_expr_2409_);
                        v___x_2413_ = lean_ptr_addr(v_a_2411_);
                        v___x_2414_ = lean_usize_dec_eq(v___x_2412_, v___x_2413_);
                        if v___x_2414_ == 0 {
                            lean_inc(v_data_2408_);
                            lean_dec_ref_known(v___y_2395_, 2);
                            v___x_2415_ = l_Lean_Expr_mdata___override(v_data_2408_, v_a_2411_);
                            v___x_2416_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__2(v_pre_2376_, v_post_2378_, v_usedLetOnly_2379_, v_skipConstInApp_2380_, v_skipInstances_2381_, v___x_2415_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                            return v___x_2416_;
                        } else {
                            lean_dec(v_a_2411_);
                            v___x_2417_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__2(v_pre_2376_, v_post_2378_, v_usedLetOnly_2379_, v_skipConstInApp_2380_, v_skipInstances_2381_, v___y_2395_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                            return v___x_2417_;
                        }
                    } else {
                        lean_dec_ref_known(v___y_2395_, 2);
                        lean_dec_ref(v_post_2378_);
                        lean_dec_ref(v_pre_2376_);
                        return v___x_2410_;
                    }
                }
                11 => {
                    v_typeName_2418_ = lean_ctor_get(v___y_2395_, 0);
                    v_idx_2419_ = lean_ctor_get(v___y_2395_, 1);
                    v_struct_2420_ = lean_ctor_get(v___y_2395_, 2);
                    lean_inc_ref(v_struct_2420_);
                    lean_inc_ref(v_post_2378_);
                    lean_inc_ref(v_pre_2376_);
                    v___x_2421_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2376_, v_post_2378_, v_usedLetOnly_2379_, v_skipConstInApp_2380_, v_skipInstances_2381_, v_struct_2420_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                    if lean_obj_tag(v___x_2421_) == 0 {
                        v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
                        lean_inc(v_a_2422_);
                        lean_dec_ref_known(v___x_2421_, 1);
                        v___x_2423_ = lean_ptr_addr(v_struct_2420_);
                        v___x_2424_ = lean_ptr_addr(v_a_2422_);
                        v___x_2425_ = lean_usize_dec_eq(v___x_2423_, v___x_2424_);
                        if v___x_2425_ == 0 {
                            lean_inc(v_idx_2419_);
                            lean_inc(v_typeName_2418_);
                            lean_dec_ref_known(v___y_2395_, 3);
                            v___x_2426_ = l_Lean_Expr_proj___override(
                                v_typeName_2418_,
                                v_idx_2419_,
                                v_a_2422_,
                            );
                            v___x_2427_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__2(v_pre_2376_, v_post_2378_, v_usedLetOnly_2379_, v_skipConstInApp_2380_, v_skipInstances_2381_, v___x_2426_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                            return v___x_2427_;
                        } else {
                            lean_dec(v_a_2422_);
                            v___x_2428_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__2(v_pre_2376_, v_post_2378_, v_usedLetOnly_2379_, v_skipConstInApp_2380_, v_skipInstances_2381_, v___y_2395_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                            return v___x_2428_;
                        }
                    } else {
                        lean_dec_ref_known(v___y_2395_, 3);
                        lean_dec_ref(v_post_2378_);
                        lean_dec_ref(v_pre_2376_);
                        return v___x_2421_;
                    }
                }
                _ => {
                    v___x_2429_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__2(v_pre_2376_, v_post_2378_, v_usedLetOnly_2379_, v_skipConstInApp_2380_, v_skipInstances_2381_, v___y_2395_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                    return v___x_2429_;
                }
            },
            3 => {
                return v___x_2432_;
            }
            4 => {
                if v_isShared_2442_ == 0 {
                    v___x_2444_ = v___x_2441_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
                    v___x_2444_ = v_reuseFailAlloc_2445_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2444_;
            }
            6 => {
                if v_isShared_2450_ == 0 {
                    v___x_2452_ = v___x_2449_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
                    v___x_2452_ = v_reuseFailAlloc_2453_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2452_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1___boxed(
    mut v___x_2455_: *mut LeanObject,
    mut v_pre_2456_: *mut LeanObject,
    mut v_e_2457_: *mut LeanObject,
    mut v_post_2458_: *mut LeanObject,
    mut v_usedLetOnly_2459_: *mut LeanObject,
    mut v_skipConstInApp_2460_: *mut LeanObject,
    mut v_skipInstances_2461_: *mut LeanObject,
    mut v___y_2462_: *mut LeanObject,
    mut v___y_2463_: *mut LeanObject,
    mut v___y_2464_: *mut LeanObject,
    mut v___y_2465_: *mut LeanObject,
    mut v___y_2466_: *mut LeanObject,
    mut v___y_2467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_2468_: u8 = 0;
    let mut v_skipConstInApp_boxed_2469_: u8 = 0;
    let mut v_skipInstances_boxed_2470_: u8 = 0;
    let mut v_res_2471_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2468_ = (lean_unbox(v_usedLetOnly_2459_) as u8);
    v_skipConstInApp_boxed_2469_ = (lean_unbox(v_skipConstInApp_2460_) as u8);
    v_skipInstances_boxed_2470_ = (lean_unbox(v_skipInstances_2461_) as u8);
    v_res_2471_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1(v___x_2455_, v_pre_2456_, v_e_2457_, v_post_2458_, v_usedLetOnly_boxed_2468_, v_skipConstInApp_boxed_2469_, v_skipInstances_boxed_2470_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
    lean_dec(v___y_2466_);
    lean_dec_ref(v___y_2465_);
    lean_dec(v___y_2464_);
    lean_dec_ref(v___y_2463_);
    lean_dec(v___y_2462_);
    return v_res_2471_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(
    mut v_pre_2472_: *mut LeanObject,
    mut v_post_2473_: *mut LeanObject,
    mut v_usedLetOnly_2474_: u8,
    mut v_skipConstInApp_2475_: u8,
    mut v_skipInstances_2476_: u8,
    mut v_e_2477_: *mut LeanObject,
    mut v_a_2478_: *mut LeanObject,
    mut v___y_2479_: *mut LeanObject,
    mut v___y_2480_: *mut LeanObject,
    mut v___y_2481_: *mut LeanObject,
    mut v___y_2482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2502_: u8 = 0;
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2506_: u8 = 0;
    let mut v_unused_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2511_: u8 = 0;
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2515_: u8 = 0;
    let mut v_val_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2520_: u8 = 0;
    let mut v_a_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2524_: u8 = 0;
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_2478_);
                v___x_2484_ =
                    lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
                lean_closure_set(v___x_2484_, 0, lean_box(0));
                lean_closure_set(v___x_2484_, 1, lean_box(0));
                lean_closure_set(v___x_2484_, 2, v_a_2478_);
                v___x_2485_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__0(lean_box(0), v___x_2484_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
                if lean_obj_tag(v___x_2485_) == 0 {
                    v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
                    v_isSharedCheck_2520_ = (!lean_is_exclusive(v___x_2485_)) as u8;
                    if v_isSharedCheck_2520_ == 0 {
                        v___x_2488_ = v___x_2485_;
                        v_isShared_2489_ = v_isSharedCheck_2520_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2486_);
                        lean_dec(v___x_2485_);
                        v___x_2488_ = lean_box(0);
                        v_isShared_2489_ = v_isSharedCheck_2520_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_2477_);
                    lean_dec_ref(v_post_2473_);
                    lean_dec_ref(v_pre_2472_);
                    v_a_2521_ = lean_ctor_get(v___x_2485_, 0);
                    v_isSharedCheck_2528_ = (!lean_is_exclusive(v___x_2485_)) as u8;
                    if v_isSharedCheck_2528_ == 0 {
                        v___x_2523_ = v___x_2485_;
                        v_isShared_2524_ = v_isSharedCheck_2528_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2521_);
                        lean_dec(v___x_2485_);
                        v___x_2523_ = lean_box(0);
                        v_isShared_2524_ = v_isSharedCheck_2528_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4___redArg(v_a_2486_, v_e_2477_);
                lean_dec(v_a_2486_);
                if lean_obj_tag(v___x_2490_) == 0 {
                    lean_del_object(v___x_2488_);
                    v___x_2491_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___closed__0;
                    v___x_2492_ = lean_box((v_usedLetOnly_2474_) as usize);
                    v___x_2493_ = lean_box((v_skipConstInApp_2475_) as usize);
                    v___x_2494_ = lean_box((v_skipInstances_2476_) as usize);
                    lean_inc_ref(v_e_2477_);
                    v___f_2495_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__1___boxed as *mut core::ffi::c_void, 13, 7);
                    lean_closure_set(v___f_2495_, 0, v___x_2491_);
                    lean_closure_set(v___f_2495_, 1, v_pre_2472_);
                    lean_closure_set(v___f_2495_, 2, v_e_2477_);
                    lean_closure_set(v___f_2495_, 3, v_post_2473_);
                    lean_closure_set(v___f_2495_, 4, v___x_2492_);
                    lean_closure_set(v___f_2495_, 5, v___x_2493_);
                    lean_closure_set(v___f_2495_, 6, v___x_2494_);
                    v___x_2496_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9___redArg(v___f_2495_, v_a_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
                    if lean_obj_tag(v___x_2496_) == 0 {
                        v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
                        lean_inc_n(v_a_2497_, 2);
                        lean_dec_ref_known(v___x_2496_, 1);
                        lean_inc(v_a_2478_);
                        v___f_2498_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        lean_closure_set(v___f_2498_, 0, v_a_2478_);
                        lean_closure_set(v___f_2498_, 1, v_e_2477_);
                        lean_closure_set(v___f_2498_, 2, v_a_2497_);
                        v___x_2499_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___lam__0(lean_box(0), v___f_2498_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
                        if lean_obj_tag(v___x_2499_) == 0 {
                            v_isSharedCheck_2506_ = (!lean_is_exclusive(v___x_2499_)) as u8;
                            if v_isSharedCheck_2506_ == 0 {
                                v_unused_2507_ = lean_ctor_get(v___x_2499_, 0);
                                lean_dec(v_unused_2507_);
                                v___x_2501_ = v___x_2499_;
                                v_isShared_2502_ = v_isSharedCheck_2506_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v___x_2499_);
                                v___x_2501_ = lean_box(0);
                                v_isShared_2502_ = v_isSharedCheck_2506_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2497_);
                            v_a_2508_ = lean_ctor_get(v___x_2499_, 0);
                            v_isSharedCheck_2515_ = (!lean_is_exclusive(v___x_2499_)) as u8;
                            if v_isSharedCheck_2515_ == 0 {
                                v___x_2510_ = v___x_2499_;
                                v_isShared_2511_ = v_isSharedCheck_2515_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_2508_);
                                lean_dec(v___x_2499_);
                                v___x_2510_ = lean_box(0);
                                v_isShared_2511_ = v_isSharedCheck_2515_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_2477_);
                        return v___x_2496_;
                    }
                } else {
                    lean_dec_ref(v_e_2477_);
                    lean_dec_ref(v_post_2473_);
                    lean_dec_ref(v_pre_2472_);
                    v_val_2516_ = lean_ctor_get(v___x_2490_, 0);
                    lean_inc(v_val_2516_);
                    lean_dec_ref_known(v___x_2490_, 1);
                    if v_isShared_2489_ == 0 {
                        lean_ctor_set(v___x_2488_, 0, v_val_2516_);
                        v___x_2518_ = v___x_2488_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_val_2516_);
                        v___x_2518_ = v_reuseFailAlloc_2519_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2502_ == 0 {
                    lean_ctor_set(v___x_2501_, 0, v_a_2497_);
                    v___x_2504_ = v___x_2501_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2497_);
                    v___x_2504_ = v_reuseFailAlloc_2505_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2504_;
            }
            4 => {
                if v_isShared_2511_ == 0 {
                    v___x_2513_ = v___x_2510_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
                    v___x_2513_ = v_reuseFailAlloc_2514_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2513_;
            }
            6 => {
                return v___x_2518_;
            }
            7 => {
                if v_isShared_2524_ == 0 {
                    v___x_2526_ = v___x_2523_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
                    v___x_2526_ = v_reuseFailAlloc_2527_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5___lam__0___boxed(
    mut v_fvars_2529_: *mut LeanObject,
    mut v_pre_2530_: *mut LeanObject,
    mut v_post_2531_: *mut LeanObject,
    mut v_usedLetOnly_2532_: *mut LeanObject,
    mut v_skipConstInApp_2533_: *mut LeanObject,
    mut v_skipInstances_2534_: *mut LeanObject,
    mut v_body_2535_: *mut LeanObject,
    mut v_x_2536_: *mut LeanObject,
    mut v___y_2537_: *mut LeanObject,
    mut v___y_2538_: *mut LeanObject,
    mut v___y_2539_: *mut LeanObject,
    mut v___y_2540_: *mut LeanObject,
    mut v___y_2541_: *mut LeanObject,
    mut v___y_2542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_2543_: u8 = 0;
    let mut v_skipConstInApp_boxed_2544_: u8 = 0;
    let mut v_skipInstances_boxed_2545_: u8 = 0;
    let mut v_res_2546_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2543_ = (lean_unbox(v_usedLetOnly_2532_) as u8);
    v_skipConstInApp_boxed_2544_ = (lean_unbox(v_skipConstInApp_2533_) as u8);
    v_skipInstances_boxed_2545_ = (lean_unbox(v_skipInstances_2534_) as u8);
    v_res_2546_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5___lam__0(v_fvars_2529_, v_pre_2530_, v_post_2531_, v_usedLetOnly_boxed_2543_, v_skipConstInApp_boxed_2544_, v_skipInstances_boxed_2545_, v_body_2535_, v_x_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
    lean_dec(v___y_2541_);
    lean_dec_ref(v___y_2540_);
    lean_dec(v___y_2539_);
    lean_dec_ref(v___y_2538_);
    lean_dec(v___y_2537_);
    return v_res_2546_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5(
    mut v_pre_2547_: *mut LeanObject,
    mut v_post_2548_: *mut LeanObject,
    mut v_usedLetOnly_2549_: u8,
    mut v_skipConstInApp_2550_: u8,
    mut v_skipInstances_2551_: u8,
    mut v_fvars_2552_: *mut LeanObject,
    mut v_e_2553_: *mut LeanObject,
    mut v_a_2554_: *mut LeanObject,
    mut v___y_2555_: *mut LeanObject,
    mut v___y_2556_: *mut LeanObject,
    mut v___y_2557_: *mut LeanObject,
    mut v___y_2558_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_2553_) == 7 {
        let mut v_binderName_2560_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderType_2561_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_2562_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_2563_: u8 = 0;
        let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
        v_binderName_2560_ = lean_ctor_get(v_e_2553_, 0);
        lean_inc(v_binderName_2560_);
        v_binderType_2561_ = lean_ctor_get(v_e_2553_, 1);
        lean_inc_ref(v_binderType_2561_);
        v_body_2562_ = lean_ctor_get(v_e_2553_, 2);
        lean_inc_ref(v_body_2562_);
        v_binderInfo_2563_ = lean_ctor_get_uint8(
            v_e_2553_,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        );
        lean_dec_ref_known(v_e_2553_, 3);
        v___x_2564_ = lean_expr_instantiate_rev(v_binderType_2561_, v_fvars_2552_);
        lean_dec_ref(v_binderType_2561_);
        lean_inc_ref(v_post_2548_);
        lean_inc_ref(v_pre_2547_);
        v___x_2565_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2547_, v_post_2548_, v_usedLetOnly_2549_, v_skipConstInApp_2550_, v_skipInstances_2551_, v___x_2564_, v_a_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
        if lean_obj_tag(v___x_2565_) == 0 {
            let mut v_a_2566_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_2570_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2571_: u8 = 0;
            let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
            v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
            lean_inc(v_a_2566_);
            lean_dec_ref_known(v___x_2565_, 1);
            v___x_2567_ = lean_box((v_usedLetOnly_2549_) as usize);
            v___x_2568_ = lean_box((v_skipConstInApp_2550_) as usize);
            v___x_2569_ = lean_box((v_skipInstances_2551_) as usize);
            v___f_2570_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
            lean_closure_set(v___f_2570_, 0, v_fvars_2552_);
            lean_closure_set(v___f_2570_, 1, v_pre_2547_);
            lean_closure_set(v___f_2570_, 2, v_post_2548_);
            lean_closure_set(v___f_2570_, 3, v___x_2567_);
            lean_closure_set(v___f_2570_, 4, v___x_2568_);
            lean_closure_set(v___f_2570_, 5, v___x_2569_);
            lean_closure_set(v___f_2570_, 6, v_body_2562_);
            v___x_2571_ = 0;
            v___x_2572_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2560_, v_binderInfo_2563_, v_a_2566_, v___f_2570_, v___x_2571_, v_a_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
            return v___x_2572_;
        } else {
            lean_dec_ref(v_body_2562_);
            lean_dec(v_binderName_2560_);
            lean_dec_ref(v_fvars_2552_);
            lean_dec_ref(v_post_2548_);
            lean_dec_ref(v_pre_2547_);
            return v___x_2565_;
        }
    } else {
        let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
        v___x_2573_ = lean_expr_instantiate_rev(v_e_2553_, v_fvars_2552_);
        lean_dec_ref(v_e_2553_);
        lean_inc_ref(v_post_2548_);
        lean_inc_ref(v_pre_2547_);
        v___x_2574_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2547_, v_post_2548_, v_usedLetOnly_2549_, v_skipConstInApp_2550_, v_skipInstances_2551_, v___x_2573_, v_a_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
        if lean_obj_tag(v___x_2574_) == 0 {
            let mut v_a_2575_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2576_: u8 = 0;
            let mut v___x_2577_: u8 = 0;
            let mut v___x_2578_: u8 = 0;
            let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
            v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
            lean_inc(v_a_2575_);
            lean_dec_ref_known(v___x_2574_, 1);
            v___x_2576_ = 0;
            v___x_2577_ = 1;
            v___x_2578_ = 1;
            v___x_2579_ = l_Lean_Meta_mkForallFVars(
                v_fvars_2552_,
                v_a_2575_,
                v___x_2576_,
                v_usedLetOnly_2549_,
                v___x_2577_,
                v___x_2578_,
                v___y_2555_,
                v___y_2556_,
                v___y_2557_,
                v___y_2558_,
            );
            lean_dec_ref(v_fvars_2552_);
            if lean_obj_tag(v___x_2579_) == 0 {
                let mut v_a_2580_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
                v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
                lean_inc(v_a_2580_);
                lean_dec_ref_known(v___x_2579_, 1);
                v___x_2581_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__2(v_pre_2547_, v_post_2548_, v_usedLetOnly_2549_, v_skipConstInApp_2550_, v_skipInstances_2551_, v_a_2580_, v_a_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
                return v___x_2581_;
            } else {
                lean_dec_ref(v_post_2548_);
                lean_dec_ref(v_pre_2547_);
                return v___x_2579_;
            }
        } else {
            lean_dec_ref(v_fvars_2552_);
            lean_dec_ref(v_post_2548_);
            lean_dec_ref(v_pre_2547_);
            return v___x_2574_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5___lam__0(
    mut v_fvars_2582_: *mut LeanObject,
    mut v_pre_2583_: *mut LeanObject,
    mut v_post_2584_: *mut LeanObject,
    mut v_usedLetOnly_2585_: u8,
    mut v_skipConstInApp_2586_: u8,
    mut v_skipInstances_2587_: u8,
    mut v_body_2588_: *mut LeanObject,
    mut v_x_2589_: *mut LeanObject,
    mut v___y_2590_: *mut LeanObject,
    mut v___y_2591_: *mut LeanObject,
    mut v___y_2592_: *mut LeanObject,
    mut v___y_2593_: *mut LeanObject,
    mut v___y_2594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    v___x_2596_ = lean_array_push(v_fvars_2582_, v_x_2589_);
    v___x_2597_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5(v_pre_2583_, v_post_2584_, v_usedLetOnly_2585_, v_skipConstInApp_2586_, v_skipInstances_2587_, v___x_2596_, v_body_2588_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
    return v___x_2597_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__2___boxed(
    mut v_pre_2598_: *mut LeanObject,
    mut v_post_2599_: *mut LeanObject,
    mut v_usedLetOnly_2600_: *mut LeanObject,
    mut v_skipConstInApp_2601_: *mut LeanObject,
    mut v_skipInstances_2602_: *mut LeanObject,
    mut v_e_2603_: *mut LeanObject,
    mut v_a_2604_: *mut LeanObject,
    mut v___y_2605_: *mut LeanObject,
    mut v___y_2606_: *mut LeanObject,
    mut v___y_2607_: *mut LeanObject,
    mut v___y_2608_: *mut LeanObject,
    mut v___y_2609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_2610_: u8 = 0;
    let mut v_skipConstInApp_boxed_2611_: u8 = 0;
    let mut v_skipInstances_boxed_2612_: u8 = 0;
    let mut v_res_2613_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2610_ = (lean_unbox(v_usedLetOnly_2600_) as u8);
    v_skipConstInApp_boxed_2611_ = (lean_unbox(v_skipConstInApp_2601_) as u8);
    v_skipInstances_boxed_2612_ = (lean_unbox(v_skipInstances_2602_) as u8);
    v_res_2613_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__2(v_pre_2598_, v_post_2599_, v_usedLetOnly_boxed_2610_, v_skipConstInApp_boxed_2611_, v_skipInstances_boxed_2612_, v_e_2603_, v_a_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
    lean_dec(v___y_2608_);
    lean_dec_ref(v___y_2607_);
    lean_dec(v___y_2606_);
    lean_dec_ref(v___y_2605_);
    lean_dec(v_a_2604_);
    return v_res_2613_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__1___boxed(
    mut v_pre_2614_: *mut LeanObject,
    mut v_post_2615_: *mut LeanObject,
    mut v_usedLetOnly_2616_: *mut LeanObject,
    mut v_skipConstInApp_2617_: *mut LeanObject,
    mut v_skipInstances_2618_: *mut LeanObject,
    mut v_sz_2619_: *mut LeanObject,
    mut v_i_2620_: *mut LeanObject,
    mut v_bs_2621_: *mut LeanObject,
    mut v___y_2622_: *mut LeanObject,
    mut v___y_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
    mut v___y_2625_: *mut LeanObject,
    mut v___y_2626_: *mut LeanObject,
    mut v___y_2627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_2628_: u8 = 0;
    let mut v_skipConstInApp_boxed_2629_: u8 = 0;
    let mut v_skipInstances_boxed_2630_: u8 = 0;
    let mut v_sz_boxed_2631_: usize = 0;
    let mut v_i_boxed_2632_: usize = 0;
    let mut v_res_2633_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2628_ = (lean_unbox(v_usedLetOnly_2616_) as u8);
    v_skipConstInApp_boxed_2629_ = (lean_unbox(v_skipConstInApp_2617_) as u8);
    v_skipInstances_boxed_2630_ = (lean_unbox(v_skipInstances_2618_) as u8);
    v_sz_boxed_2631_ = lean_unbox_usize(v_sz_2619_);
    lean_dec(v_sz_2619_);
    v_i_boxed_2632_ = lean_unbox_usize(v_i_2620_);
    lean_dec(v_i_2620_);
    v_res_2633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__1(v_pre_2614_, v_post_2615_, v_usedLetOnly_boxed_2628_, v_skipConstInApp_boxed_2629_, v_skipInstances_boxed_2630_, v_sz_boxed_2631_, v_i_boxed_2632_, v_bs_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
    lean_dec(v___y_2626_);
    lean_dec_ref(v___y_2625_);
    lean_dec(v___y_2624_);
    lean_dec_ref(v___y_2623_);
    lean_dec(v___y_2622_);
    return v_res_2633_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0___boxed(
    mut v_pre_2634_: *mut LeanObject,
    mut v_post_2635_: *mut LeanObject,
    mut v_usedLetOnly_2636_: *mut LeanObject,
    mut v_skipConstInApp_2637_: *mut LeanObject,
    mut v_skipInstances_2638_: *mut LeanObject,
    mut v_e_2639_: *mut LeanObject,
    mut v_a_2640_: *mut LeanObject,
    mut v___y_2641_: *mut LeanObject,
    mut v___y_2642_: *mut LeanObject,
    mut v___y_2643_: *mut LeanObject,
    mut v___y_2644_: *mut LeanObject,
    mut v___y_2645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_2646_: u8 = 0;
    let mut v_skipConstInApp_boxed_2647_: u8 = 0;
    let mut v_skipInstances_boxed_2648_: u8 = 0;
    let mut v_res_2649_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2646_ = (lean_unbox(v_usedLetOnly_2636_) as u8);
    v_skipConstInApp_boxed_2647_ = (lean_unbox(v_skipConstInApp_2637_) as u8);
    v_skipInstances_boxed_2648_ = (lean_unbox(v_skipInstances_2638_) as u8);
    v_res_2649_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2634_, v_post_2635_, v_usedLetOnly_boxed_2646_, v_skipConstInApp_boxed_2647_, v_skipInstances_boxed_2648_, v_e_2639_, v_a_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
    lean_dec(v___y_2644_);
    lean_dec_ref(v___y_2643_);
    lean_dec(v___y_2642_);
    lean_dec_ref(v___y_2641_);
    lean_dec(v_a_2640_);
    return v_res_2649_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5___boxed(
    mut v_pre_2650_: *mut LeanObject,
    mut v_post_2651_: *mut LeanObject,
    mut v_usedLetOnly_2652_: *mut LeanObject,
    mut v_skipConstInApp_2653_: *mut LeanObject,
    mut v_skipInstances_2654_: *mut LeanObject,
    mut v_fvars_2655_: *mut LeanObject,
    mut v_e_2656_: *mut LeanObject,
    mut v_a_2657_: *mut LeanObject,
    mut v___y_2658_: *mut LeanObject,
    mut v___y_2659_: *mut LeanObject,
    mut v___y_2660_: *mut LeanObject,
    mut v___y_2661_: *mut LeanObject,
    mut v___y_2662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_2663_: u8 = 0;
    let mut v_skipConstInApp_boxed_2664_: u8 = 0;
    let mut v_skipInstances_boxed_2665_: u8 = 0;
    let mut v_res_2666_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2663_ = (lean_unbox(v_usedLetOnly_2652_) as u8);
    v_skipConstInApp_boxed_2664_ = (lean_unbox(v_skipConstInApp_2653_) as u8);
    v_skipInstances_boxed_2665_ = (lean_unbox(v_skipInstances_2654_) as u8);
    v_res_2666_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5(v_pre_2650_, v_post_2651_, v_usedLetOnly_boxed_2663_, v_skipConstInApp_boxed_2664_, v_skipInstances_boxed_2665_, v_fvars_2655_, v_e_2656_, v_a_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
    lean_dec(v___y_2661_);
    lean_dec_ref(v___y_2660_);
    lean_dec(v___y_2659_);
    lean_dec_ref(v___y_2658_);
    lean_dec(v_a_2657_);
    return v_res_2666_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__6___boxed(
    mut v_pre_2667_: *mut LeanObject,
    mut v_post_2668_: *mut LeanObject,
    mut v_usedLetOnly_2669_: *mut LeanObject,
    mut v_skipConstInApp_2670_: *mut LeanObject,
    mut v_skipInstances_2671_: *mut LeanObject,
    mut v_fvars_2672_: *mut LeanObject,
    mut v_e_2673_: *mut LeanObject,
    mut v_a_2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
    mut v___y_2676_: *mut LeanObject,
    mut v___y_2677_: *mut LeanObject,
    mut v___y_2678_: *mut LeanObject,
    mut v___y_2679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_2680_: u8 = 0;
    let mut v_skipConstInApp_boxed_2681_: u8 = 0;
    let mut v_skipInstances_boxed_2682_: u8 = 0;
    let mut v_res_2683_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2680_ = (lean_unbox(v_usedLetOnly_2669_) as u8);
    v_skipConstInApp_boxed_2681_ = (lean_unbox(v_skipConstInApp_2670_) as u8);
    v_skipInstances_boxed_2682_ = (lean_unbox(v_skipInstances_2671_) as u8);
    v_res_2683_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__6(v_pre_2667_, v_post_2668_, v_usedLetOnly_boxed_2680_, v_skipConstInApp_boxed_2681_, v_skipInstances_boxed_2682_, v_fvars_2672_, v_e_2673_, v_a_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
    lean_dec(v___y_2678_);
    lean_dec_ref(v___y_2677_);
    lean_dec(v___y_2676_);
    lean_dec_ref(v___y_2675_);
    lean_dec(v_a_2674_);
    return v_res_2683_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7___boxed(
    mut v_pre_2684_: *mut LeanObject,
    mut v_post_2685_: *mut LeanObject,
    mut v_usedLetOnly_2686_: *mut LeanObject,
    mut v_skipConstInApp_2687_: *mut LeanObject,
    mut v_skipInstances_2688_: *mut LeanObject,
    mut v_fvars_2689_: *mut LeanObject,
    mut v_e_2690_: *mut LeanObject,
    mut v_a_2691_: *mut LeanObject,
    mut v___y_2692_: *mut LeanObject,
    mut v___y_2693_: *mut LeanObject,
    mut v___y_2694_: *mut LeanObject,
    mut v___y_2695_: *mut LeanObject,
    mut v___y_2696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_2697_: u8 = 0;
    let mut v_skipConstInApp_boxed_2698_: u8 = 0;
    let mut v_skipInstances_boxed_2699_: u8 = 0;
    let mut v_res_2700_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2697_ = (lean_unbox(v_usedLetOnly_2686_) as u8);
    v_skipConstInApp_boxed_2698_ = (lean_unbox(v_skipConstInApp_2687_) as u8);
    v_skipInstances_boxed_2699_ = (lean_unbox(v_skipInstances_2688_) as u8);
    v_res_2700_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7(v_pre_2684_, v_post_2685_, v_usedLetOnly_boxed_2697_, v_skipConstInApp_boxed_2698_, v_skipInstances_boxed_2699_, v_fvars_2689_, v_e_2690_, v_a_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
    lean_dec(v___y_2695_);
    lean_dec_ref(v___y_2694_);
    lean_dec(v___y_2693_);
    lean_dec_ref(v___y_2692_);
    lean_dec(v_a_2691_);
    return v_res_2700_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_upperBound_2701_: *mut LeanObject,
    mut v___x_2702_: *mut LeanObject,
    mut v_pre_2703_: *mut LeanObject,
    mut v_post_2704_: *mut LeanObject,
    mut v_usedLetOnly_2705_: *mut LeanObject,
    mut v_skipConstInApp_2706_: *mut LeanObject,
    mut v_skipInstances_2707_: *mut LeanObject,
    mut v_a_2708_: *mut LeanObject,
    mut v_b_2709_: *mut LeanObject,
    mut v___y_2710_: *mut LeanObject,
    mut v___y_2711_: *mut LeanObject,
    mut v___y_2712_: *mut LeanObject,
    mut v___y_2713_: *mut LeanObject,
    mut v___y_2714_: *mut LeanObject,
    mut v___y_2715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_2716_: u8 = 0;
    let mut v_skipConstInApp_boxed_2717_: u8 = 0;
    let mut v_skipInstances_boxed_2718_: u8 = 0;
    let mut v_res_2719_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2716_ = (lean_unbox(v_usedLetOnly_2705_) as u8);
    v_skipConstInApp_boxed_2717_ = (lean_unbox(v_skipConstInApp_2706_) as u8);
    v_skipInstances_boxed_2718_ = (lean_unbox(v_skipInstances_2707_) as u8);
    v_res_2719_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___redArg(v_upperBound_2701_, v___x_2702_, v_pre_2703_, v_post_2704_, v_usedLetOnly_boxed_2716_, v_skipConstInApp_boxed_2717_, v_skipInstances_boxed_2718_, v_a_2708_, v_b_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
    lean_dec(v___y_2714_);
    lean_dec_ref(v___y_2713_);
    lean_dec(v___y_2712_);
    lean_dec_ref(v___y_2711_);
    lean_dec(v___y_2710_);
    lean_dec_ref(v___x_2702_);
    lean_dec(v_upperBound_2701_);
    return v_res_2719_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__8___boxed(
    mut v_skipInstances_2720_: *mut LeanObject,
    mut v_pre_2721_: *mut LeanObject,
    mut v_post_2722_: *mut LeanObject,
    mut v_usedLetOnly_2723_: *mut LeanObject,
    mut v_skipConstInApp_2724_: *mut LeanObject,
    mut v_x_2725_: *mut LeanObject,
    mut v_x_2726_: *mut LeanObject,
    mut v_x_2727_: *mut LeanObject,
    mut v___y_2728_: *mut LeanObject,
    mut v___y_2729_: *mut LeanObject,
    mut v___y_2730_: *mut LeanObject,
    mut v___y_2731_: *mut LeanObject,
    mut v___y_2732_: *mut LeanObject,
    mut v___y_2733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipInstances_boxed_2734_: u8 = 0;
    let mut v_usedLetOnly_boxed_2735_: u8 = 0;
    let mut v_skipConstInApp_boxed_2736_: u8 = 0;
    let mut v_res_2737_: *mut LeanObject = core::ptr::null_mut();
    v_skipInstances_boxed_2734_ = (lean_unbox(v_skipInstances_2720_) as u8);
    v_usedLetOnly_boxed_2735_ = (lean_unbox(v_usedLetOnly_2723_) as u8);
    v_skipConstInApp_boxed_2736_ = (lean_unbox(v_skipConstInApp_2724_) as u8);
    v_res_2737_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__8(v_skipInstances_boxed_2734_, v_pre_2721_, v_post_2722_, v_usedLetOnly_boxed_2735_, v_skipConstInApp_boxed_2736_, v_x_2725_, v_x_2726_, v_x_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
    lean_dec(v___y_2732_);
    lean_dec_ref(v___y_2731_);
    lean_dec(v___y_2730_);
    lean_dec_ref(v___y_2729_);
    lean_dec(v___y_2728_);
    return v_res_2737_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___lam__0(
    mut v_00_u03b1_2738_: *mut LeanObject,
    mut v_x_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
    mut v___y_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    v___x_2745_ = lean_apply_1(v_x_2739_, lean_box(0));
    v___x_2746_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2746_, 0, v___x_2745_);
    return v___x_2746_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___lam__0___boxed(
    mut v_00_u03b1_2747_: *mut LeanObject,
    mut v_x_2748_: *mut LeanObject,
    mut v___y_2749_: *mut LeanObject,
    mut v___y_2750_: *mut LeanObject,
    mut v___y_2751_: *mut LeanObject,
    mut v___y_2752_: *mut LeanObject,
    mut v___y_2753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2754_: *mut LeanObject = core::ptr::null_mut();
    v_res_2754_ =
        l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___lam__0(
            v_00_u03b1_2747_,
            v_x_2748_,
            v___y_2749_,
            v___y_2750_,
            v___y_2751_,
            v___y_2752_,
        );
    lean_dec(v___y_2752_);
    lean_dec_ref(v___y_2751_);
    lean_dec(v___y_2750_);
    lean_dec_ref(v___y_2749_);
    return v_res_2754_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    v___x_2755_ = lean_box(0);
    v___x_2756_ = lean_unsigned_to_nat(16);
    v___x_2757_ = lean_mk_array(v___x_2756_, v___x_2755_);
    return v___x_2757_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    v___x_2758_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__0_once), _init_l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__0);
    v___x_2759_ = lean_unsigned_to_nat(0);
    v___x_2760_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2760_, 0, v___x_2759_);
    lean_ctor_set(v___x_2760_, 1, v___x_2758_);
    return v___x_2760_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    v___x_2761_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__1_once), _init_l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__1);
    v___x_2762_ = lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_2762_, 0, lean_box(0));
    lean_closure_set(v___x_2762_, 1, lean_box(0));
    lean_closure_set(v___x_2762_, 2, v___x_2761_);
    return v___x_2762_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0(
    mut v_input_2763_: *mut LeanObject,
    mut v_pre_2764_: *mut LeanObject,
    mut v_post_2765_: *mut LeanObject,
    mut v_usedLetOnly_2766_: u8,
    mut v_skipConstInApp_2767_: u8,
    mut v___y_2768_: *mut LeanObject,
    mut v___y_2769_: *mut LeanObject,
    mut v___y_2770_: *mut LeanObject,
    mut v___y_2771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: u8 = 0;
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2783_: u8 = 0;
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2787_: u8 = 0;
    let mut v_unused_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2773_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__2_once), _init_l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___closed__2);
                v___x_2774_ = l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___lam__0(lean_box(0), v___x_2773_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
                v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
                lean_inc(v_a_2775_);
                lean_dec_ref(v___x_2774_);
                v___x_2776_ = 0;
                v___x_2777_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0(v_pre_2764_, v_post_2765_, v_usedLetOnly_2766_, v_skipConstInApp_2767_, v___x_2776_, v_input_2763_, v_a_2775_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
                if lean_obj_tag(v___x_2777_) == 0 {
                    v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
                    lean_inc(v_a_2778_);
                    lean_dec_ref_known(v___x_2777_, 1);
                    v___x_2779_ = lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___x_2779_, 0, lean_box(0));
                    lean_closure_set(v___x_2779_, 1, lean_box(0));
                    lean_closure_set(v___x_2779_, 2, v_a_2775_);
                    v___x_2780_ = l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___lam__0(lean_box(0), v___x_2779_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
                    v_isSharedCheck_2787_ = (!lean_is_exclusive(v___x_2780_)) as u8;
                    if v_isSharedCheck_2787_ == 0 {
                        v_unused_2788_ = lean_ctor_get(v___x_2780_, 0);
                        lean_dec(v_unused_2788_);
                        v___x_2782_ = v___x_2780_;
                        v_isShared_2783_ = v_isSharedCheck_2787_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2780_);
                        v___x_2782_ = lean_box(0);
                        v_isShared_2783_ = v_isSharedCheck_2787_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2775_);
                    return v___x_2777_;
                }
            }
            1 => {
                if v_isShared_2783_ == 0 {
                    lean_ctor_set(v___x_2782_, 0, v_a_2778_);
                    v___x_2785_ = v___x_2782_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2778_);
                    v___x_2785_ = v_reuseFailAlloc_2786_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2785_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0___boxed(
    mut v_input_2789_: *mut LeanObject,
    mut v_pre_2790_: *mut LeanObject,
    mut v_post_2791_: *mut LeanObject,
    mut v_usedLetOnly_2792_: *mut LeanObject,
    mut v_skipConstInApp_2793_: *mut LeanObject,
    mut v___y_2794_: *mut LeanObject,
    mut v___y_2795_: *mut LeanObject,
    mut v___y_2796_: *mut LeanObject,
    mut v___y_2797_: *mut LeanObject,
    mut v___y_2798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_2799_: u8 = 0;
    let mut v_skipConstInApp_boxed_2800_: u8 = 0;
    let mut v_res_2801_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2799_ = (lean_unbox(v_usedLetOnly_2792_) as u8);
    v_skipConstInApp_boxed_2800_ = (lean_unbox(v_skipConstInApp_2793_) as u8);
    v_res_2801_ = l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0(
        v_input_2789_,
        v_pre_2790_,
        v_post_2791_,
        v_usedLetOnly_boxed_2799_,
        v_skipConstInApp_boxed_2800_,
        v___y_2794_,
        v___y_2795_,
        v___y_2796_,
        v___y_2797_,
    );
    lean_dec(v___y_2797_);
    lean_dec_ref(v___y_2796_);
    lean_dec(v___y_2795_);
    lean_dec_ref(v___y_2794_);
    return v_res_2801_;
}
pub unsafe fn l_Lean_Meta_Match_unfoldNamedPattern(
    mut v_e_2804_: *mut LeanObject,
    mut v_a_2805_: *mut LeanObject,
    mut v_a_2806_: *mut LeanObject,
    mut v_a_2807_: *mut LeanObject,
    mut v_a_2808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_visit_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: u8 = 0;
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    v_visit_2810_ = l_Lean_Meta_Match_unfoldNamedPattern___closed__0;
    v___f_2811_ = l_Lean_Meta_Match_unfoldNamedPattern___closed__1;
    v___x_2812_ = 0;
    v___x_2813_ = l_Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0(
        v_e_2804_,
        v_visit_2810_,
        v___f_2811_,
        v___x_2812_,
        v___x_2812_,
        v_a_2805_,
        v_a_2806_,
        v_a_2807_,
        v_a_2808_,
    );
    return v___x_2813_;
}
pub unsafe fn l_Lean_Meta_Match_unfoldNamedPattern___boxed(
    mut v_e_2814_: *mut LeanObject,
    mut v_a_2815_: *mut LeanObject,
    mut v_a_2816_: *mut LeanObject,
    mut v_a_2817_: *mut LeanObject,
    mut v_a_2818_: *mut LeanObject,
    mut v_a_2819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2820_: *mut LeanObject = core::ptr::null_mut();
    v_res_2820_ =
        l_Lean_Meta_Match_unfoldNamedPattern(v_e_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
    lean_dec(v_a_2818_);
    lean_dec_ref(v_a_2817_);
    lean_dec(v_a_2816_);
    lean_dec_ref(v_a_2815_);
    return v_res_2820_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3(
    mut v_upperBound_2821_: *mut LeanObject,
    mut v___x_2822_: *mut LeanObject,
    mut v_pre_2823_: *mut LeanObject,
    mut v_post_2824_: *mut LeanObject,
    mut v_usedLetOnly_2825_: u8,
    mut v_skipConstInApp_2826_: u8,
    mut v_skipInstances_2827_: u8,
    mut v___x_2828_: *mut LeanObject,
    mut v_inst_2829_: *mut LeanObject,
    mut v_R_2830_: *mut LeanObject,
    mut v_a_2831_: *mut LeanObject,
    mut v_b_2832_: *mut LeanObject,
    mut v_c_2833_: *mut LeanObject,
    mut v___y_2834_: *mut LeanObject,
    mut v___y_2835_: *mut LeanObject,
    mut v___y_2836_: *mut LeanObject,
    mut v___y_2837_: *mut LeanObject,
    mut v___y_2838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    v___x_2840_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___redArg(v_upperBound_2821_, v___x_2822_, v_pre_2823_, v_post_2824_, v_usedLetOnly_2825_, v_skipConstInApp_2826_, v_skipInstances_2827_, v_a_2831_, v_b_2832_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
    return v___x_2840_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_2841_: *mut LeanObject = *_args.add(0);
    let mut v___x_2842_: *mut LeanObject = *_args.add(1);
    let mut v_pre_2843_: *mut LeanObject = *_args.add(2);
    let mut v_post_2844_: *mut LeanObject = *_args.add(3);
    let mut v_usedLetOnly_2845_: *mut LeanObject = *_args.add(4);
    let mut v_skipConstInApp_2846_: *mut LeanObject = *_args.add(5);
    let mut v_skipInstances_2847_: *mut LeanObject = *_args.add(6);
    let mut v___x_2848_: *mut LeanObject = *_args.add(7);
    let mut v_inst_2849_: *mut LeanObject = *_args.add(8);
    let mut v_R_2850_: *mut LeanObject = *_args.add(9);
    let mut v_a_2851_: *mut LeanObject = *_args.add(10);
    let mut v_b_2852_: *mut LeanObject = *_args.add(11);
    let mut v_c_2853_: *mut LeanObject = *_args.add(12);
    let mut v___y_2854_: *mut LeanObject = *_args.add(13);
    let mut v___y_2855_: *mut LeanObject = *_args.add(14);
    let mut v___y_2856_: *mut LeanObject = *_args.add(15);
    let mut v___y_2857_: *mut LeanObject = *_args.add(16);
    let mut v___y_2858_: *mut LeanObject = *_args.add(17);
    let mut v___y_2859_: *mut LeanObject = *_args.add(18);
    let mut v_usedLetOnly_boxed_2860_: u8 = 0;
    let mut v_skipConstInApp_boxed_2861_: u8 = 0;
    let mut v_skipInstances_boxed_2862_: u8 = 0;
    let mut v_res_2863_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2860_ = (lean_unbox(v_usedLetOnly_2845_) as u8);
    v_skipConstInApp_boxed_2861_ = (lean_unbox(v_skipConstInApp_2846_) as u8);
    v_skipInstances_boxed_2862_ = (lean_unbox(v_skipInstances_2847_) as u8);
    v_res_2863_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__3(v_upperBound_2841_, v___x_2842_, v_pre_2843_, v_post_2844_, v_usedLetOnly_boxed_2860_, v_skipConstInApp_boxed_2861_, v_skipInstances_boxed_2862_, v___x_2848_, v_inst_2849_, v_R_2850_, v_a_2851_, v_b_2852_, v_c_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
    lean_dec(v___y_2858_);
    lean_dec_ref(v___y_2857_);
    lean_dec(v___y_2856_);
    lean_dec_ref(v___y_2855_);
    lean_dec(v___y_2854_);
    lean_dec(v___x_2848_);
    lean_dec_ref(v___x_2842_);
    lean_dec(v_upperBound_2841_);
    return v_res_2863_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4(
    mut v_00_u03b2_2864_: *mut LeanObject,
    mut v_m_2865_: *mut LeanObject,
    mut v_a_2866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    v___x_2867_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4___redArg(v_m_2865_, v_a_2866_);
    return v___x_2867_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4___boxed(
    mut v_00_u03b2_2868_: *mut LeanObject,
    mut v_m_2869_: *mut LeanObject,
    mut v_a_2870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2871_: *mut LeanObject = core::ptr::null_mut();
    v_res_2871_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4(v_00_u03b2_2868_, v_m_2869_, v_a_2870_);
    lean_dec_ref(v_a_2870_);
    lean_dec_ref(v_m_2869_);
    return v_res_2871_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5_spec__7(
    mut v_00_u03b1_2872_: *mut LeanObject,
    mut v_name_2873_: *mut LeanObject,
    mut v_bi_2874_: u8,
    mut v_type_2875_: *mut LeanObject,
    mut v_k_2876_: *mut LeanObject,
    mut v_kind_2877_: u8,
    mut v___y_2878_: *mut LeanObject,
    mut v___y_2879_: *mut LeanObject,
    mut v___y_2880_: *mut LeanObject,
    mut v___y_2881_: *mut LeanObject,
    mut v___y_2882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    v___x_2884_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5_spec__7___redArg(v_name_2873_, v_bi_2874_, v_type_2875_, v_k_2876_, v_kind_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
    return v___x_2884_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5_spec__7___boxed(
    mut v_00_u03b1_2885_: *mut LeanObject,
    mut v_name_2886_: *mut LeanObject,
    mut v_bi_2887_: *mut LeanObject,
    mut v_type_2888_: *mut LeanObject,
    mut v_k_2889_: *mut LeanObject,
    mut v_kind_2890_: *mut LeanObject,
    mut v___y_2891_: *mut LeanObject,
    mut v___y_2892_: *mut LeanObject,
    mut v___y_2893_: *mut LeanObject,
    mut v___y_2894_: *mut LeanObject,
    mut v___y_2895_: *mut LeanObject,
    mut v___y_2896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_2897_: u8 = 0;
    let mut v_kind_boxed_2898_: u8 = 0;
    let mut v_res_2899_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_2897_ = (lean_unbox(v_bi_2887_) as u8);
    v_kind_boxed_2898_ = (lean_unbox(v_kind_2890_) as u8);
    v_res_2899_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_2885_, v_name_2886_, v_bi_boxed_2897_, v_type_2888_, v_k_2889_, v_kind_boxed_2898_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
    lean_dec(v___y_2895_);
    lean_dec_ref(v___y_2894_);
    lean_dec(v___y_2893_);
    lean_dec_ref(v___y_2892_);
    lean_dec(v___y_2891_);
    return v_res_2899_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7_spec__10(
    mut v_00_u03b1_2900_: *mut LeanObject,
    mut v_name_2901_: *mut LeanObject,
    mut v_type_2902_: *mut LeanObject,
    mut v_val_2903_: *mut LeanObject,
    mut v_k_2904_: *mut LeanObject,
    mut v_nondep_2905_: u8,
    mut v_kind_2906_: u8,
    mut v___y_2907_: *mut LeanObject,
    mut v___y_2908_: *mut LeanObject,
    mut v___y_2909_: *mut LeanObject,
    mut v___y_2910_: *mut LeanObject,
    mut v___y_2911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    v___x_2913_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7_spec__10___redArg(v_name_2901_, v_type_2902_, v_val_2903_, v_k_2904_, v_nondep_2905_, v_kind_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
    return v___x_2913_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7_spec__10___boxed(
    mut v_00_u03b1_2914_: *mut LeanObject,
    mut v_name_2915_: *mut LeanObject,
    mut v_type_2916_: *mut LeanObject,
    mut v_val_2917_: *mut LeanObject,
    mut v_k_2918_: *mut LeanObject,
    mut v_nondep_2919_: *mut LeanObject,
    mut v_kind_2920_: *mut LeanObject,
    mut v___y_2921_: *mut LeanObject,
    mut v___y_2922_: *mut LeanObject,
    mut v___y_2923_: *mut LeanObject,
    mut v___y_2924_: *mut LeanObject,
    mut v___y_2925_: *mut LeanObject,
    mut v___y_2926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_2927_: u8 = 0;
    let mut v_kind_boxed_2928_: u8 = 0;
    let mut v_res_2929_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_2927_ = (lean_unbox(v_nondep_2919_) as u8);
    v_kind_boxed_2928_ = (lean_unbox(v_kind_2920_) as u8);
    v_res_2929_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_2914_, v_name_2915_, v_type_2916_, v_val_2917_, v_k_2918_, v_nondep_boxed_2927_, v_kind_boxed_2928_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
    lean_dec(v___y_2925_);
    lean_dec_ref(v___y_2924_);
    lean_dec(v___y_2923_);
    lean_dec_ref(v___y_2922_);
    lean_dec(v___y_2921_);
    return v_res_2929_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13(
    mut v_00_u03b1_2930_: *mut LeanObject,
    mut v_ref_2931_: *mut LeanObject,
    mut v___y_2932_: *mut LeanObject,
    mut v___y_2933_: *mut LeanObject,
    mut v___y_2934_: *mut LeanObject,
    mut v___y_2935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    v___x_2937_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_2931_);
    return v___x_2937_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13___boxed(
    mut v_00_u03b1_2938_: *mut LeanObject,
    mut v_ref_2939_: *mut LeanObject,
    mut v___y_2940_: *mut LeanObject,
    mut v___y_2941_: *mut LeanObject,
    mut v___y_2942_: *mut LeanObject,
    mut v___y_2943_: *mut LeanObject,
    mut v___y_2944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2945_: *mut LeanObject = core::ptr::null_mut();
    v_res_2945_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_2938_, v_ref_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
    lean_dec(v___y_2943_);
    lean_dec_ref(v___y_2942_);
    lean_dec(v___y_2941_);
    lean_dec_ref(v___y_2940_);
    return v_res_2945_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9(
    mut v_00_u03b1_2946_: *mut LeanObject,
    mut v_x_2947_: *mut LeanObject,
    mut v___y_2948_: *mut LeanObject,
    mut v___y_2949_: *mut LeanObject,
    mut v___y_2950_: *mut LeanObject,
    mut v___y_2951_: *mut LeanObject,
    mut v___y_2952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    v___x_2954_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9___redArg(v_x_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
    return v___x_2954_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9___boxed(
    mut v_00_u03b1_2955_: *mut LeanObject,
    mut v_x_2956_: *mut LeanObject,
    mut v___y_2957_: *mut LeanObject,
    mut v___y_2958_: *mut LeanObject,
    mut v___y_2959_: *mut LeanObject,
    mut v___y_2960_: *mut LeanObject,
    mut v___y_2961_: *mut LeanObject,
    mut v___y_2962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2963_: *mut LeanObject = core::ptr::null_mut();
    v_res_2963_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__9(v_00_u03b1_2955_, v_x_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
    lean_dec(v___y_2961_);
    lean_dec_ref(v___y_2960_);
    lean_dec(v___y_2959_);
    lean_dec_ref(v___y_2958_);
    lean_dec(v___y_2957_);
    return v_res_2963_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10(
    mut v_00_u03b2_2964_: *mut LeanObject,
    mut v_m_2965_: *mut LeanObject,
    mut v_a_2966_: *mut LeanObject,
    mut v_b_2967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    v___x_2968_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10___redArg(v_m_2965_, v_a_2966_, v_b_2967_);
    return v___x_2968_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4_spec__5(
    mut v_00_u03b2_2969_: *mut LeanObject,
    mut v_a_2970_: *mut LeanObject,
    mut v_x_2971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    v___x_2972_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4_spec__5___redArg(v_a_2970_, v_x_2971_);
    return v___x_2972_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4_spec__5___boxed(
    mut v_00_u03b2_2973_: *mut LeanObject,
    mut v_a_2974_: *mut LeanObject,
    mut v_x_2975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2976_: *mut LeanObject = core::ptr::null_mut();
    v_res_2976_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_2973_, v_a_2974_, v_x_2975_);
    lean_dec(v_x_2975_);
    lean_dec_ref(v_a_2974_);
    return v_res_2976_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__15(
    mut v_00_u03b2_2977_: *mut LeanObject,
    mut v_a_2978_: *mut LeanObject,
    mut v_x_2979_: *mut LeanObject,
) -> u8 {
    let mut v___x_2980_: u8 = 0;
    v___x_2980_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2978_, v_x_2979_);
    return v___x_2980_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__15___boxed(
    mut v_00_u03b2_2981_: *mut LeanObject,
    mut v_a_2982_: *mut LeanObject,
    mut v_x_2983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2984_: u8 = 0;
    let mut v_r_2985_: *mut LeanObject = core::ptr::null_mut();
    v_res_2984_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_2981_, v_a_2982_, v_x_2983_);
    lean_dec(v_x_2983_);
    lean_dec_ref(v_a_2982_);
    v_r_2985_ = lean_box((v_res_2984_) as usize);
    return v_r_2985_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__16(
    mut v_00_u03b2_2986_: *mut LeanObject,
    mut v_data_2987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    v___x_2988_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__16___redArg(v_data_2987_);
    return v___x_2988_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__17(
    mut v_00_u03b2_2989_: *mut LeanObject,
    mut v_a_2990_: *mut LeanObject,
    mut v_b_2991_: *mut LeanObject,
    mut v_x_2992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    v___x_2993_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2990_, v_b_2991_, v_x_2992_);
    return v___x_2993_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__16_spec__17(
    mut v_00_u03b2_2994_: *mut LeanObject,
    mut v_i_2995_: *mut LeanObject,
    mut v_source_2996_: *mut LeanObject,
    mut v_target_2997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    v___x_2998_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_2995_, v_source_2996_, v_target_2997_);
    return v___x_2998_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(
    mut v_00_u03b2_2999_: *mut LeanObject,
    mut v_x_3000_: *mut LeanObject,
    mut v_x_3001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    v___x_3002_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Match_unfoldNamedPattern_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_3000_, v_x_3001_);
    return v___x_3002_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_NamedPatterns(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_NamedPatterns(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Match_NamedPatterns(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_NamedPatterns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_NamedPatterns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Match_NamedPatterns(builtin);
}
