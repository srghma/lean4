// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Preprocess
// Imports: Lean.Elab.RecAppSyntax Lean.Meta.WHNF
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_set, lean_array_size,
    lean_array_uget_borrowed, lean_array_uset, lean_find_expr, lean_mk_array, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_panic_fn_borrowed, lean_ptr_addr, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Prelude::l_Lean_maxRecDepthErrorMessage;
use crate::r#gen::Init::System::CancelToken::l_IO_CancelToken_isSet;
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_mkRef___boxed};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_checkSystem, l_Lean_Core_instInhabitedCoreM___lam__0___boxed,
};
use crate::r#gen::Lean::Elab::RecAppSyntax::{
    initialize_Lean_Elab_RecAppSyntax, l_Lean_MData_isRecApp,
    runtime_initialize_Lean_Elab_RecAppSyntax,
};
use crate::r#gen::Lean::Exception::l_Lean_interruptExceptionId;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_beta, l_Lean_Expr_constName_x21,
    l_Lean_Expr_forallE___override, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_headBeta, l_Lean_Expr_isApp, l_Lean_Expr_isConst, l_Lean_Expr_isHeadBetaTarget,
    l_Lean_Expr_isMData, l_Lean_Expr_lam___override, l_Lean_Expr_letE___override,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_Expr_sort___override,
    l_Lean_ExprStructEq_beq, l_Lean_ExprStructEq_hash, l_Lean_instBEqBinderInfo_beq, l_Lean_mkAppN,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::Transform::l_Lean_Meta_unfoldIfArgIsAppOf;
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, runtime_initialize_Lean_Meta_WHNF,
};
pub static l_panic___at___00Lean_Elab_Structural_preprocess_spec__0___closed__0_value:
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
    m_fun: l_Lean_Core_instInhabitedCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Elab_Structural_preprocess_spec__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Elab_Structural_preprocess_spec__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_preprocess___lam__0___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_preprocess___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_preprocess___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_preprocess___lam__1___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_preprocess___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_preprocess___lam__1___closed__1_value:
    crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116,
        105, 111, 110, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108, 46, 80, 114, 101, 112,
        114, 111, 99, 101, 115, 115, 0,
    ],
};
static mut l_Lean_Elab_Structural_preprocess___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_preprocess___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_preprocess___lam__1___closed__2_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108,
        46, 112, 114, 101, 112, 114, 111, 99, 101, 115, 115, 0,
    ],
};
static mut l_Lean_Elab_Structural_preprocess___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_preprocess___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_preprocess___lam__1___closed__3_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_Structural_preprocess___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_preprocess___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_preprocess___lam__1___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_preprocess___lam__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_preprocess___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Structural_preprocess___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Structural_preprocess___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_preprocess___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce_spec__0_spec__0(
    mut v_a_927_: *mut crate::leanh::LeanObject,
    mut v_as_928_: *mut crate::leanh::LeanObject,
    mut v_i_929_: usize,
    mut v_stop_930_: usize,
) -> u8 {
    let mut v___x_931_: u8 = 0;
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: u8 = 0;
    let mut v___x_934_: usize = 0;
    let mut v___x_935_: usize = 0;
    let mut v___x_937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_931_ = lean_usize_dec_eq(v_i_929_, v_stop_930_);
                if v___x_931_ == 0 {
                    v___x_932_ = lean_array_uget_borrowed(v_as_928_, v_i_929_);
                    v___x_933_ = lean_name_eq(v_a_927_, v___x_932_);
                    if v___x_933_ == 0 {
                        v___x_934_ = 1usize;
                        v___x_935_ = lean_usize_add(v_i_929_, v___x_934_);
                        v_i_929_ = v___x_935_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_933_;
                    }
                } else {
                    v___x_937_ = 0;
                    return v___x_937_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce_spec__0_spec__0___boxed(
    mut v_a_938_: *mut crate::leanh::LeanObject,
    mut v_as_939_: *mut crate::leanh::LeanObject,
    mut v_i_940_: *mut crate::leanh::LeanObject,
    mut v_stop_941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_942_: usize = 0;
    let mut v_stop_boxed_943_: usize = 0;
    let mut v_res_944_: u8 = 0;
    let mut v_r_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_942_ = crate::leanh::lean_unbox_usize(v_i_940_);
    crate::leanh::lean_dec(v_i_940_);
    v_stop_boxed_943_ = crate::leanh::lean_unbox_usize(v_stop_941_);
    crate::leanh::lean_dec(v_stop_941_);
    v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce_spec__0_spec__0(v_a_938_, v_as_939_, v_i_boxed_942_, v_stop_boxed_943_);
    crate::leanh::lean_dec_ref(v_as_939_);
    crate::leanh::lean_dec(v_a_938_);
    v_r_945_ = crate::leanh::lean_box((v_res_944_) as usize);
    return v_r_945_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce_spec__0(
    mut v_as_946_: *mut crate::leanh::LeanObject,
    mut v_a_947_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: u8 = 0;
    v___x_948_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_949_ = lean_array_get_size(v_as_946_);
    v___x_950_ = lean_nat_dec_lt(v___x_948_, v___x_949_);
    if v___x_950_ == 0 {
        return v___x_950_;
    } else {
        if v___x_950_ == 0 {
            return v___x_950_;
        } else {
            let mut v___x_951_: usize = 0;
            let mut v___x_952_: usize = 0;
            let mut v___x_953_: u8 = 0;
            v___x_951_ = 0usize;
            v___x_952_ = lean_usize_of_nat(v___x_949_);
            v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce_spec__0_spec__0(v_a_947_, v_as_946_, v___x_951_, v___x_952_);
            return v___x_953_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce_spec__0___boxed(
    mut v_as_954_: *mut crate::leanh::LeanObject,
    mut v_a_955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_956_: u8 = 0;
    let mut v_r_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce_spec__0(v_as_954_, v_a_955_);
    crate::leanh::lean_dec(v_a_955_);
    crate::leanh::lean_dec_ref(v_as_954_);
    v_r_957_ = crate::leanh::lean_box((v_res_956_) as usize);
    return v_r_957_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lam__0(
    mut v___x_958_: u8,
    mut v_recFnNames_959_: *mut crate::leanh::LeanObject,
    mut v_e_960_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_961_: u8 = 0;
    v___x_961_ = l_Lean_Expr_isConst(v_e_960_);
    if v___x_961_ == 0 {
        return v___x_958_;
    } else {
        let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_963_: u8 = 0;
        v___x_962_ = l_Lean_Expr_constName_x21(v_e_960_);
        v___x_963_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce_spec__0(v_recFnNames_959_, v___x_962_);
        crate::leanh::lean_dec(v___x_962_);
        return v___x_963_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lam__0___boxed(
    mut v___x_964_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_965_: *mut crate::leanh::LeanObject,
    mut v_e_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_324__boxed_967_: u8 = 0;
    let mut v_res_968_: u8 = 0;
    let mut v_r_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_324__boxed_967_ = (crate::leanh::lean_unbox(v___x_964_) as u8);
    v_res_968_ = l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lam__0(v___x_324__boxed_967_, v_recFnNames_965_, v_e_966_);
    crate::leanh::lean_dec_ref(v_e_966_);
    crate::leanh::lean_dec_ref(v_recFnNames_965_);
    v_r_969_ = crate::leanh::lean_box((v_res_968_) as usize);
    return v_r_969_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(
    mut v_e_970_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_971_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_972_: u8 = 0;
    let mut v___x_973_: u8 = 0;
    v___x_972_ = 0;
    v___x_973_ = l_Lean_Expr_isHeadBetaTarget(v_e_970_, v___x_972_);
    if v___x_973_ == 0 {
        crate::leanh::lean_dec_ref(v_recFnNames_971_);
        return v___x_972_;
    } else {
        let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_974_ = crate::leanh::lean_box((v___x_972_) as usize);
        v___f_975_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
        crate::leanh::lean_closure_set(v___f_975_, 0, v___x_974_);
        crate::leanh::lean_closure_set(v___f_975_, 1, v_recFnNames_971_);
        v___x_976_ = l_Lean_Expr_getAppFn(v_e_970_);
        v___x_977_ = lean_find_expr(v___f_975_, v___x_976_);
        crate::leanh::lean_dec_ref(v___x_976_);
        crate::leanh::lean_dec_ref(v___f_975_);
        if crate::leanh::lean_obj_tag(v___x_977_) == 0 {
            return v___x_972_;
        } else {
            crate::leanh::lean_dec_ref_known(v___x_977_, 1);
            return v___x_973_;
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___boxed(
    mut v_e_978_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_980_: u8 = 0;
    let mut v_r_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_980_ = l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(v_e_978_, v_recFnNames_979_);
    crate::leanh::lean_dec_ref(v_e_978_);
    v_r_981_ = crate::leanh::lean_box((v_res_980_) as usize);
    return v_r_981_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_preprocess_spec__0(
    mut v_msg_983_: *mut crate::leanh::LeanObject,
    mut v___y_984_: *mut crate::leanh::LeanObject,
    mut v___y_985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840__overap_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_987_ = l_panic___at___00Lean_Elab_Structural_preprocess_spec__0___closed__0;
    v___x_840__overap_988_ = lean_panic_fn_borrowed(v___f_987_, v_msg_983_);
    crate::leanh::lean_inc(v___y_985_);
    crate::leanh::lean_inc_ref(v___y_984_);
    v___x_989_ = crate::leanh::lean_apply_3(
        v___x_840__overap_988_,
        v___y_984_,
        v___y_985_,
        crate::leanh::lean_box(0),
    );
    return v___x_989_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_preprocess_spec__0___boxed(
    mut v_msg_990_: *mut crate::leanh::LeanObject,
    mut v___y_991_: *mut crate::leanh::LeanObject,
    mut v___y_992_: *mut crate::leanh::LeanObject,
    mut v___y_993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_994_ = l_panic___at___00Lean_Elab_Structural_preprocess_spec__0(
        v_msg_990_, v___y_991_, v___y_992_,
    );
    crate::leanh::lean_dec(v___y_992_);
    crate::leanh::lean_dec_ref(v___y_991_);
    return v_res_994_;
}
pub unsafe fn l_Lean_Elab_Structural_preprocess___lam__0(
    mut v_recFnNames_997_: *mut crate::leanh::LeanObject,
    mut v_e_998_: *mut crate::leanh::LeanObject,
    mut v___y_999_: *mut crate::leanh::LeanObject,
    mut v___y_1000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1002_: u8 = 0;
    v___x_1002_ = l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(v_e_998_, v_recFnNames_997_);
    if v___x_1002_ == 0 {
        let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_998_);
        v___x_1003_ = l_Lean_Elab_Structural_preprocess___lam__0___closed__0;
        v___x_1004_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1004_, 0, v___x_1003_);
        return v___x_1004_;
    } else {
        let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1005_ = l_Lean_Expr_headBeta(v_e_998_);
        v___x_1006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1006_, 0, v___x_1005_);
        v___x_1007_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1007_, 0, v___x_1006_);
        return v___x_1007_;
    }
}
pub unsafe fn l_Lean_Elab_Structural_preprocess___lam__0___boxed(
    mut v_recFnNames_1008_: *mut crate::leanh::LeanObject,
    mut v_e_1009_: *mut crate::leanh::LeanObject,
    mut v___y_1010_: *mut crate::leanh::LeanObject,
    mut v___y_1011_: *mut crate::leanh::LeanObject,
    mut v___y_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Lean_Elab_Structural_preprocess___lam__0(
        v_recFnNames_1008_,
        v_e_1009_,
        v___y_1010_,
        v___y_1011_,
    );
    crate::leanh::lean_dec(v___y_1011_);
    crate::leanh::lean_dec_ref(v___y_1010_);
    return v_res_1013_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = crate::leanh::lean_box(0);
    v_dummy_1015_ = l_Lean_Expr_sort___override(v___x_1014_);
    return v_dummy_1015_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1019_ = l_Lean_Elab_Structural_preprocess___lam__1___closed__3;
    v___x_1020_ = crate::leanh::lean_unsigned_to_nat(39);
    v___x_1021_ = crate::leanh::lean_unsigned_to_nat(56);
    v___x_1022_ = l_Lean_Elab_Structural_preprocess___lam__1___closed__2;
    v___x_1023_ = l_Lean_Elab_Structural_preprocess___lam__1___closed__1;
    v___x_1024_ = l_mkPanicMessageWithDecl(
        v___x_1023_,
        v___x_1022_,
        v___x_1021_,
        v___x_1020_,
        v___x_1019_,
    );
    return v___x_1024_;
}
pub unsafe fn l_Lean_Elab_Structural_preprocess___lam__1(
    mut v_e_1025_: *mut crate::leanh::LeanObject,
    mut v___y_1026_: *mut crate::leanh::LeanObject,
    mut v___y_1027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1033_: u8 = 0;
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: u8 = 0;
    let mut v_dummy_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1053_: u8 = 0;
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1057_: u8 = 0;
    let mut v___x_1058_: u8 = 0;
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1058_ = l_Lean_Expr_isApp(v_e_1025_);
                if v___x_1058_ == 0 {
                    v___y_1033_ = v___x_1058_;
                    state = 2;
                    continue;
                } else {
                    v___x_1059_ = l_Lean_Expr_getAppFn(v_e_1025_);
                    v___x_1060_ = l_Lean_Expr_isMData(v___x_1059_);
                    crate::leanh::lean_dec_ref(v___x_1059_);
                    v___y_1033_ = v___x_1060_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1030_ = l_Lean_Elab_Structural_preprocess___lam__0___closed__0;
                v___x_1031_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1031_, 0, v___x_1030_);
                return v___x_1031_;
            }
            2 => {
                if v___y_1033_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_1025_);
                    state = 1;
                    continue;
                } else {
                    v___x_1034_ = l_Lean_Expr_getAppFn(v_e_1025_);
                    if crate::leanh::lean_obj_tag(v___x_1034_) == 10 {
                        v_data_1035_ = crate::leanh::lean_ctor_get(v___x_1034_, 0);
                        crate::leanh::lean_inc(v_data_1035_);
                        v_expr_1036_ = crate::leanh::lean_ctor_get(v___x_1034_, 1);
                        crate::leanh::lean_inc_ref(v_expr_1036_);
                        crate::leanh::lean_dec_ref_known(v___x_1034_, 2);
                        v___x_1037_ = l_Lean_MData_isRecApp(v_data_1035_);
                        if v___x_1037_ == 0 {
                            crate::leanh::lean_dec_ref(v_expr_1036_);
                            crate::leanh::lean_dec(v_data_1035_);
                            crate::leanh::lean_dec_ref(v_e_1025_);
                            state = 1;
                            continue;
                        } else {
                            v_dummy_1038_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Structural_preprocess___lam__1___closed__0
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Structural_preprocess___lam__1___closed__0_once
                                ),
                                _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__0,
                            );
                            v_nargs_1039_ = l_Lean_Expr_getAppNumArgs(v_e_1025_);
                            crate::leanh::lean_inc(v_nargs_1039_);
                            v___x_1040_ = lean_mk_array(v_nargs_1039_, v_dummy_1038_);
                            v___x_1041_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1042_ = lean_nat_sub(v_nargs_1039_, v___x_1041_);
                            crate::leanh::lean_dec(v_nargs_1039_);
                            v___x_1043_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                v_e_1025_,
                                v___x_1040_,
                                v___x_1042_,
                            );
                            v___x_1044_ = l_Lean_Expr_beta(v_expr_1036_, v___x_1043_);
                            v___x_1045_ = l_Lean_Expr_mdata___override(v_data_1035_, v___x_1044_);
                            v___x_1046_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1046_, 0, v___x_1045_);
                            v___x_1047_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1047_, 0, v___x_1046_);
                            return v___x_1047_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1034_);
                        crate::leanh::lean_dec_ref(v_e_1025_);
                        v___x_1048_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_preprocess___lam__1___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_preprocess___lam__1___closed__4_once
                            ),
                            _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__4,
                        );
                        v___x_1049_ = l_panic___at___00Lean_Elab_Structural_preprocess_spec__0(
                            v___x_1048_,
                            v___y_1026_,
                            v___y_1027_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1049_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1049_, 1);
                            state = 1;
                            continue;
                        } else {
                            v_a_1050_ = crate::leanh::lean_ctor_get(v___x_1049_, 0);
                            v_isSharedCheck_1057_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1049_)) as u8;
                            if v_isSharedCheck_1057_ == 0 {
                                v___x_1052_ = v___x_1049_;
                                v_isShared_1053_ = v_isSharedCheck_1057_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1050_);
                                crate::leanh::lean_dec(v___x_1049_);
                                v___x_1052_ = crate::leanh::lean_box(0);
                                v_isShared_1053_ = v_isSharedCheck_1057_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_1053_ == 0 {
                    v___x_1055_ = v___x_1052_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1056_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
                    v___x_1055_ = v_reuseFailAlloc_1056_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1055_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_preprocess___lam__1___boxed(
    mut v_e_1061_: *mut crate::leanh::LeanObject,
    mut v___y_1062_: *mut crate::leanh::LeanObject,
    mut v___y_1063_: *mut crate::leanh::LeanObject,
    mut v___y_1064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1065_ = l_Lean_Elab_Structural_preprocess___lam__1(v_e_1061_, v___y_1062_, v___y_1063_);
    crate::leanh::lean_dec(v___y_1063_);
    crate::leanh::lean_dec_ref(v___y_1062_);
    return v_res_1065_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5___redArg(
    mut v_a_1066_: *mut crate::leanh::LeanObject,
    mut v_x_1067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: u8 = 0;
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1067_) == 0 {
                    v___x_1068_ = crate::leanh::lean_box(0);
                    return v___x_1068_;
                } else {
                    v_key_1069_ = crate::leanh::lean_ctor_get(v_x_1067_, 0);
                    v_value_1070_ = crate::leanh::lean_ctor_get(v_x_1067_, 1);
                    v_tail_1071_ = crate::leanh::lean_ctor_get(v_x_1067_, 2);
                    v___x_1072_ = l_Lean_ExprStructEq_beq(v_key_1069_, v_a_1066_);
                    if v___x_1072_ == 0 {
                        v_x_1067_ = v_tail_1071_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_1070_);
                        v___x_1074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1074_, 0, v_value_1070_);
                        return v___x_1074_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5___redArg___boxed(
    mut v_a_1075_: *mut crate::leanh::LeanObject,
    mut v_x_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1077_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5___redArg(v_a_1075_, v_x_1076_);
    crate::leanh::lean_dec(v_x_1076_);
    crate::leanh::lean_dec_ref(v_a_1075_);
    return v_res_1077_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4___redArg(
    mut v_m_1078_: *mut crate::leanh::LeanObject,
    mut v_a_1079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: u64 = 0;
    let mut v___x_1083_: u64 = 0;
    let mut v___x_1084_: u64 = 0;
    let mut v_fold_1085_: u64 = 0;
    let mut v___x_1086_: u64 = 0;
    let mut v___x_1087_: u64 = 0;
    let mut v___x_1088_: u64 = 0;
    let mut v___x_1089_: usize = 0;
    let mut v___x_1090_: usize = 0;
    let mut v___x_1091_: usize = 0;
    let mut v___x_1092_: usize = 0;
    let mut v___x_1093_: usize = 0;
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1080_ = crate::leanh::lean_ctor_get(v_m_1078_, 1);
    v___x_1081_ = lean_array_get_size(v_buckets_1080_);
    v___x_1082_ = l_Lean_ExprStructEq_hash(v_a_1079_);
    v___x_1083_ = 32u64;
    v___x_1084_ = lean_uint64_shift_right(v___x_1082_, v___x_1083_);
    v_fold_1085_ = lean_uint64_xor(v___x_1082_, v___x_1084_);
    v___x_1086_ = 16u64;
    v___x_1087_ = lean_uint64_shift_right(v_fold_1085_, v___x_1086_);
    v___x_1088_ = lean_uint64_xor(v_fold_1085_, v___x_1087_);
    v___x_1089_ = lean_uint64_to_usize(v___x_1088_);
    v___x_1090_ = lean_usize_of_nat(v___x_1081_);
    v___x_1091_ = 1usize;
    v___x_1092_ = lean_usize_sub(v___x_1090_, v___x_1091_);
    v___x_1093_ = lean_usize_land(v___x_1089_, v___x_1092_);
    v___x_1094_ = lean_array_uget_borrowed(v_buckets_1080_, v___x_1093_);
    v___x_1095_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5___redArg(v_a_1079_, v___x_1094_);
    return v___x_1095_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4___redArg___boxed(
    mut v_m_1096_: *mut crate::leanh::LeanObject,
    mut v_a_1097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1098_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4___redArg(v_m_1096_, v_a_1097_);
    crate::leanh::lean_dec_ref(v_a_1097_);
    crate::leanh::lean_dec_ref(v_m_1096_);
    return v_res_1098_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__0(
    mut v_00_u03b1_1099_: *mut crate::leanh::LeanObject,
    mut v_x_1100_: *mut crate::leanh::LeanObject,
    mut v___y_1101_: *mut crate::leanh::LeanObject,
    mut v___y_1102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = crate::leanh::lean_apply_1(v_x_1100_, crate::leanh::lean_box(0));
    v___x_1105_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1105_, 0, v___x_1104_);
    return v___x_1105_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__0___boxed(
    mut v_00_u03b1_1106_: *mut crate::leanh::LeanObject,
    mut v_x_1107_: *mut crate::leanh::LeanObject,
    mut v___y_1108_: *mut crate::leanh::LeanObject,
    mut v___y_1109_: *mut crate::leanh::LeanObject,
    mut v___y_1110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1111_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__0(v_00_u03b1_1106_, v_x_1107_, v___y_1108_, v___y_1109_);
    crate::leanh::lean_dec(v___y_1109_);
    crate::leanh::lean_dec_ref(v___y_1108_);
    return v_res_1111_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1117_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1118_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1118_, 0, v___x_1117_);
    return v___x_1118_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1119_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__3);
    v___x_1120_ = l_Lean_MessageData_ofFormat(v___x_1119_);
    return v___x_1120_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1121_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__4);
    v___x_1122_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__2;
    v___x_1123_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1123_, 0, v___x_1122_);
    crate::leanh::lean_ctor_set(v___x_1123_, 1, v___x_1121_);
    return v___x_1123_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg(
    mut v_ref_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__5);
    v___x_1127_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1127_, 0, v_ref_1124_);
    crate::leanh::lean_ctor_set(v___x_1127_, 1, v___x_1126_);
    v___x_1128_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1128_, 0, v___x_1127_);
    return v___x_1128_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___boxed(
    mut v_ref_1129_: *mut crate::leanh::LeanObject,
    mut v___y_1130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_1129_);
    return v_res_1131_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1132_ = crate::leanh::lean_box(0);
    v___x_1133_ = l_Lean_interruptExceptionId;
    v___x_1134_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1134_, 0, v___x_1133_);
    crate::leanh::lean_ctor_set(v___x_1134_, 1, v___x_1132_);
    return v___x_1134_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1136_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg___closed__0);
    v___x_1137_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1137_, 0, v___x_1136_);
    return v___x_1137_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg___boxed(
    mut v___y_1138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1139_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg();
    return v_res_1139_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6___redArg(
    mut v_x_1140_: *mut crate::leanh::LeanObject,
    mut v___y_1141_: *mut crate::leanh::LeanObject,
    mut v___y_1142_: *mut crate::leanh::LeanObject,
    mut v___y_1143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1150_: u8 = 0;
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1154_: u8 = 0;
    let mut v___y_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1162_: u8 = 0;
    let mut v___y_1163_: u8 = 0;
    let mut v___y_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1188_: u8 = 0;
    let mut v_cancelTk_x3f_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1190_: u8 = 0;
    let mut v_inheritedTraceOptions_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: u8 = 0;
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: u8 = 0;
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1203_: u8 = 0;
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1176_ = crate::leanh::lean_ctor_get(v___y_1142_, 0);
                v_fileMap_1177_ = crate::leanh::lean_ctor_get(v___y_1142_, 1);
                v_options_1178_ = crate::leanh::lean_ctor_get(v___y_1142_, 2);
                v_currRecDepth_1179_ = crate::leanh::lean_ctor_get(v___y_1142_, 3);
                v_maxRecDepth_1180_ = crate::leanh::lean_ctor_get(v___y_1142_, 4);
                v_ref_1181_ = crate::leanh::lean_ctor_get(v___y_1142_, 5);
                v_currNamespace_1182_ = crate::leanh::lean_ctor_get(v___y_1142_, 6);
                v_openDecls_1183_ = crate::leanh::lean_ctor_get(v___y_1142_, 7);
                v_initHeartbeats_1184_ = crate::leanh::lean_ctor_get(v___y_1142_, 8);
                v_maxHeartbeats_1185_ = crate::leanh::lean_ctor_get(v___y_1142_, 9);
                v_quotContext_1186_ = crate::leanh::lean_ctor_get(v___y_1142_, 10);
                v_currMacroScope_1187_ = crate::leanh::lean_ctor_get(v___y_1142_, 11);
                v_diag_1188_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1142_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1189_ = crate::leanh::lean_ctor_get(v___y_1142_, 12);
                v_suppressElabErrors_1190_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1142_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1191_ = crate::leanh::lean_ctor_get(v___y_1142_, 13);
                if crate::leanh::lean_obj_tag(v_cancelTk_x3f_1189_) == 1 {
                    v_val_1197_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_1189_, 0);
                    v___x_1198_ = l_IO_CancelToken_isSet(v_val_1197_);
                    if v___x_1198_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_1140_);
                        v___x_1199_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg();
                        v_a_1200_ = crate::leanh::lean_ctor_get(v___x_1199_, 0);
                        v_isSharedCheck_1207_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1199_)) as u8;
                        if v_isSharedCheck_1207_ == 0 {
                            v___x_1202_ = v___x_1199_;
                            v_isShared_1203_ = v_isSharedCheck_1207_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1200_);
                            crate::leanh::lean_dec(v___x_1199_);
                            v___x_1202_ = crate::leanh::lean_box(0);
                            v_isShared_1203_ = v_isSharedCheck_1207_;
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
                if crate::leanh::lean_obj_tag(v___y_1146_) == 0 {
                    return v___y_1146_;
                } else {
                    v_a_1147_ = crate::leanh::lean_ctor_get(v___y_1146_, 0);
                    v_isSharedCheck_1154_ = (!crate::leanh::lean_is_exclusive(v___y_1146_)) as u8;
                    if v_isSharedCheck_1154_ == 0 {
                        v___x_1149_ = v___y_1146_;
                        v_isShared_1150_ = v_isSharedCheck_1154_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1147_);
                        crate::leanh::lean_dec(v___y_1146_);
                        v___x_1149_ = crate::leanh::lean_box(0);
                        v_isShared_1150_ = v_isSharedCheck_1154_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1150_ == 0 {
                    v___x_1152_ = v___x_1149_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1153_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
                    v___x_1152_ = v_reuseFailAlloc_1153_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1152_;
            }
            4 => {
                v___x_1172_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1173_ = lean_nat_add(v___y_1157_, v___x_1172_);
                crate::leanh::lean_inc_ref(v___y_1168_);
                crate::leanh::lean_inc(v___y_1156_);
                crate::leanh::lean_inc(v___y_1171_);
                crate::leanh::lean_inc(v___y_1165_);
                crate::leanh::lean_inc(v___y_1161_);
                crate::leanh::lean_inc(v___y_1169_);
                crate::leanh::lean_inc(v___y_1159_);
                crate::leanh::lean_inc(v___y_1170_);
                crate::leanh::lean_inc(v___y_1160_);
                crate::leanh::lean_inc_ref(v___y_1158_);
                crate::leanh::lean_inc_ref(v___y_1167_);
                crate::leanh::lean_inc_ref(v___y_1164_);
                v___x_1174_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1174_, 0, v___y_1164_);
                crate::leanh::lean_ctor_set(v___x_1174_, 1, v___y_1167_);
                crate::leanh::lean_ctor_set(v___x_1174_, 2, v___y_1158_);
                crate::leanh::lean_ctor_set(v___x_1174_, 3, v___x_1173_);
                crate::leanh::lean_ctor_set(v___x_1174_, 4, v___y_1160_);
                crate::leanh::lean_ctor_set(v___x_1174_, 5, v___y_1166_);
                crate::leanh::lean_ctor_set(v___x_1174_, 6, v___y_1170_);
                crate::leanh::lean_ctor_set(v___x_1174_, 7, v___y_1159_);
                crate::leanh::lean_ctor_set(v___x_1174_, 8, v___y_1169_);
                crate::leanh::lean_ctor_set(v___x_1174_, 9, v___y_1161_);
                crate::leanh::lean_ctor_set(v___x_1174_, 10, v___y_1165_);
                crate::leanh::lean_ctor_set(v___x_1174_, 11, v___y_1171_);
                crate::leanh::lean_ctor_set(v___x_1174_, 12, v___y_1156_);
                crate::leanh::lean_ctor_set(v___x_1174_, 13, v___y_1168_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1174_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___y_1163_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1174_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_1162_,
                );
                crate::leanh::lean_inc(v___y_1143_);
                crate::leanh::lean_inc(v___y_1141_);
                v___x_1175_ = crate::leanh::lean_apply_4(
                    v_x_1140_,
                    v___y_1141_,
                    v___x_1174_,
                    v___y_1143_,
                    crate::leanh::lean_box(0),
                );
                v___y_1146_ = v___x_1175_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1193_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1194_ = lean_nat_dec_eq(v_maxRecDepth_1180_, v___x_1193_);
                if v___x_1194_ == 0 {
                    v___x_1195_ = lean_nat_dec_eq(v_currRecDepth_1179_, v_maxRecDepth_1180_);
                    if v___x_1195_ == 0 {
                        crate::leanh::lean_inc(v_ref_1181_);
                        v___y_1156_ = v_cancelTk_x3f_1189_;
                        v___y_1157_ = v_currRecDepth_1179_;
                        v___y_1158_ = v_options_1178_;
                        v___y_1159_ = v_openDecls_1183_;
                        v___y_1160_ = v_maxRecDepth_1180_;
                        v___y_1161_ = v_maxHeartbeats_1185_;
                        v___y_1162_ = v_suppressElabErrors_1190_;
                        v___y_1163_ = v_diag_1188_;
                        v___y_1164_ = v_fileName_1176_;
                        v___y_1165_ = v_quotContext_1186_;
                        v___y_1166_ = v_ref_1181_;
                        v___y_1167_ = v_fileMap_1177_;
                        v___y_1168_ = v_inheritedTraceOptions_1191_;
                        v___y_1169_ = v_initHeartbeats_1184_;
                        v___y_1170_ = v_currNamespace_1182_;
                        v___y_1171_ = v_currMacroScope_1187_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_1140_);
                        crate::leanh::lean_inc(v_ref_1181_);
                        v___x_1196_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_1181_);
                        v___y_1146_ = v___x_1196_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_ref_1181_);
                    v___y_1156_ = v_cancelTk_x3f_1189_;
                    v___y_1157_ = v_currRecDepth_1179_;
                    v___y_1158_ = v_options_1178_;
                    v___y_1159_ = v_openDecls_1183_;
                    v___y_1160_ = v_maxRecDepth_1180_;
                    v___y_1161_ = v_maxHeartbeats_1185_;
                    v___y_1162_ = v_suppressElabErrors_1190_;
                    v___y_1163_ = v_diag_1188_;
                    v___y_1164_ = v_fileName_1176_;
                    v___y_1165_ = v_quotContext_1186_;
                    v___y_1166_ = v_ref_1181_;
                    v___y_1167_ = v_fileMap_1177_;
                    v___y_1168_ = v_inheritedTraceOptions_1191_;
                    v___y_1169_ = v_initHeartbeats_1184_;
                    v___y_1170_ = v_currNamespace_1182_;
                    v___y_1171_ = v_currMacroScope_1187_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v_isShared_1203_ == 0 {
                    v___x_1205_ = v___x_1202_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1206_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
                    v___x_1205_ = v_reuseFailAlloc_1206_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6___redArg___boxed(
    mut v_x_1208_: *mut crate::leanh::LeanObject,
    mut v___y_1209_: *mut crate::leanh::LeanObject,
    mut v___y_1210_: *mut crate::leanh::LeanObject,
    mut v___y_1211_: *mut crate::leanh::LeanObject,
    mut v___y_1212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1213_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6___redArg(v_x_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
    crate::leanh::lean_dec(v___y_1211_);
    crate::leanh::lean_dec_ref(v___y_1210_);
    crate::leanh::lean_dec(v___y_1209_);
    return v_res_1213_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(
    mut v_x_1214_: *mut crate::leanh::LeanObject,
    mut v_x_1215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: u64 = 0;
    let mut v___x_1224_: u64 = 0;
    let mut v___x_1225_: u64 = 0;
    let mut v_fold_1226_: u64 = 0;
    let mut v___x_1227_: u64 = 0;
    let mut v___x_1228_: u64 = 0;
    let mut v___x_1229_: u64 = 0;
    let mut v___x_1230_: usize = 0;
    let mut v___x_1231_: usize = 0;
    let mut v___x_1232_: usize = 0;
    let mut v___x_1233_: usize = 0;
    let mut v___x_1234_: usize = 0;
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1215_) == 0 {
                    return v_x_1214_;
                } else {
                    v_key_1216_ = crate::leanh::lean_ctor_get(v_x_1215_, 0);
                    v_value_1217_ = crate::leanh::lean_ctor_get(v_x_1215_, 1);
                    v_tail_1218_ = crate::leanh::lean_ctor_get(v_x_1215_, 2);
                    v_isSharedCheck_1241_ = (!crate::leanh::lean_is_exclusive(v_x_1215_)) as u8;
                    if v_isSharedCheck_1241_ == 0 {
                        v___x_1220_ = v_x_1215_;
                        v_isShared_1221_ = v_isSharedCheck_1241_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1218_);
                        crate::leanh::lean_inc(v_value_1217_);
                        crate::leanh::lean_inc(v_key_1216_);
                        crate::leanh::lean_dec(v_x_1215_);
                        v___x_1220_ = crate::leanh::lean_box(0);
                        v_isShared_1221_ = v_isSharedCheck_1241_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1222_ = lean_array_get_size(v_x_1214_);
                v___x_1223_ = l_Lean_ExprStructEq_hash(v_key_1216_);
                v___x_1224_ = 32u64;
                v___x_1225_ = lean_uint64_shift_right(v___x_1223_, v___x_1224_);
                v_fold_1226_ = lean_uint64_xor(v___x_1223_, v___x_1225_);
                v___x_1227_ = 16u64;
                v___x_1228_ = lean_uint64_shift_right(v_fold_1226_, v___x_1227_);
                v___x_1229_ = lean_uint64_xor(v_fold_1226_, v___x_1228_);
                v___x_1230_ = lean_uint64_to_usize(v___x_1229_);
                v___x_1231_ = lean_usize_of_nat(v___x_1222_);
                v___x_1232_ = 1usize;
                v___x_1233_ = lean_usize_sub(v___x_1231_, v___x_1232_);
                v___x_1234_ = lean_usize_land(v___x_1230_, v___x_1233_);
                v___x_1235_ = lean_array_uget_borrowed(v_x_1214_, v___x_1234_);
                crate::leanh::lean_inc(v___x_1235_);
                if v_isShared_1221_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1220_, 2, v___x_1235_);
                    v___x_1237_ = v___x_1220_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1240_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_key_1216_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_value_1217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 2, v___x_1235_);
                    v___x_1237_ = v_reuseFailAlloc_1240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1238_ = lean_array_uset(v_x_1214_, v___x_1234_, v___x_1237_);
                v_x_1214_ = v___x_1238_;
                v_x_1215_ = v_tail_1218_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(
    mut v_i_1242_: *mut crate::leanh::LeanObject,
    mut v_source_1243_: *mut crate::leanh::LeanObject,
    mut v_target_1244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: u8 = 0;
    let mut v_es_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1245_ = lean_array_get_size(v_source_1243_);
                v___x_1246_ = lean_nat_dec_lt(v_i_1242_, v___x_1245_);
                if v___x_1246_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1243_);
                    crate::leanh::lean_dec(v_i_1242_);
                    return v_target_1244_;
                } else {
                    v_es_1247_ = lean_array_fget(v_source_1243_, v_i_1242_);
                    v___x_1248_ = crate::leanh::lean_box(0);
                    v_source_1249_ = lean_array_fset(v_source_1243_, v_i_1242_, v___x_1248_);
                    v_target_1250_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_target_1244_, v_es_1247_);
                    v___x_1251_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1252_ = lean_nat_add(v_i_1242_, v___x_1251_);
                    crate::leanh::lean_dec(v_i_1242_);
                    v_i_1242_ = v___x_1252_;
                    v_source_1243_ = v_source_1249_;
                    v_target_1244_ = v_target_1250_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12___redArg(
    mut v_data_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = lean_array_get_size(v_data_1254_);
    v___x_1256_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1257_ = lean_nat_mul(v___x_1255_, v___x_1256_);
    v___x_1258_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1259_ = crate::leanh::lean_box(0);
    v___x_1260_ = lean_mk_array(v_nbuckets_1257_, v___x_1259_);
    v___x_1261_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v___x_1258_, v_data_1254_, v___x_1260_);
    return v___x_1261_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__11___redArg(
    mut v_a_1262_: *mut crate::leanh::LeanObject,
    mut v_x_1263_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1264_: u8 = 0;
    let mut v_key_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1263_) == 0 {
                    v___x_1264_ = 0;
                    return v___x_1264_;
                } else {
                    v_key_1265_ = crate::leanh::lean_ctor_get(v_x_1263_, 0);
                    v_tail_1266_ = crate::leanh::lean_ctor_get(v_x_1263_, 2);
                    v___x_1267_ = l_Lean_ExprStructEq_beq(v_key_1265_, v_a_1262_);
                    if v___x_1267_ == 0 {
                        v_x_1263_ = v_tail_1266_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1267_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__11___redArg___boxed(
    mut v_a_1269_: *mut crate::leanh::LeanObject,
    mut v_x_1270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1271_: u8 = 0;
    let mut v_r_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1271_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__11___redArg(v_a_1269_, v_x_1270_);
    crate::leanh::lean_dec(v_x_1270_);
    crate::leanh::lean_dec_ref(v_a_1269_);
    v_r_1272_ = crate::leanh::lean_box((v_res_1271_) as usize);
    return v_r_1272_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__13___redArg(
    mut v_a_1273_: *mut crate::leanh::LeanObject,
    mut v_b_1274_: *mut crate::leanh::LeanObject,
    mut v_x_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1281_: u8 = 0;
    let mut v___x_1282_: u8 = 0;
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1275_) == 0 {
                    crate::leanh::lean_dec(v_b_1274_);
                    crate::leanh::lean_dec_ref(v_a_1273_);
                    return v_x_1275_;
                } else {
                    v_key_1276_ = crate::leanh::lean_ctor_get(v_x_1275_, 0);
                    v_value_1277_ = crate::leanh::lean_ctor_get(v_x_1275_, 1);
                    v_tail_1278_ = crate::leanh::lean_ctor_get(v_x_1275_, 2);
                    v_isSharedCheck_1290_ = (!crate::leanh::lean_is_exclusive(v_x_1275_)) as u8;
                    if v_isSharedCheck_1290_ == 0 {
                        v___x_1280_ = v_x_1275_;
                        v_isShared_1281_ = v_isSharedCheck_1290_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1278_);
                        crate::leanh::lean_inc(v_value_1277_);
                        crate::leanh::lean_inc(v_key_1276_);
                        crate::leanh::lean_dec(v_x_1275_);
                        v___x_1280_ = crate::leanh::lean_box(0);
                        v_isShared_1281_ = v_isSharedCheck_1290_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1282_ = l_Lean_ExprStructEq_beq(v_key_1276_, v_a_1273_);
                if v___x_1282_ == 0 {
                    v___x_1283_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__13___redArg(v_a_1273_, v_b_1274_, v_tail_1278_);
                    if v_isShared_1281_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1280_, 2, v___x_1283_);
                        v___x_1285_ = v___x_1280_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1286_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_key_1276_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_value_1277_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 2, v___x_1283_);
                        v___x_1285_ = v_reuseFailAlloc_1286_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1277_);
                    crate::leanh::lean_dec(v_key_1276_);
                    if v_isShared_1281_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1280_, 1, v_b_1274_);
                        crate::leanh::lean_ctor_set(v___x_1280_, 0, v_a_1273_);
                        v___x_1288_ = v___x_1280_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1289_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1273_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_b_1274_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_tail_1278_);
                        v___x_1288_ = v_reuseFailAlloc_1289_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1285_;
            }
            3 => {
                return v___x_1288_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7___redArg(
    mut v_m_1291_: *mut crate::leanh::LeanObject,
    mut v_a_1292_: *mut crate::leanh::LeanObject,
    mut v_b_1293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1298_: u8 = 0;
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: u64 = 0;
    let mut v___x_1301_: u64 = 0;
    let mut v___x_1302_: u64 = 0;
    let mut v_fold_1303_: u64 = 0;
    let mut v___x_1304_: u64 = 0;
    let mut v___x_1305_: u64 = 0;
    let mut v___x_1306_: u64 = 0;
    let mut v___x_1307_: usize = 0;
    let mut v___x_1308_: usize = 0;
    let mut v___x_1309_: usize = 0;
    let mut v___x_1310_: usize = 0;
    let mut v___x_1311_: usize = 0;
    let mut v_bkt_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: u8 = 0;
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: u8 = 0;
    let mut v_val_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1294_ = crate::leanh::lean_ctor_get(v_m_1291_, 0);
                v_buckets_1295_ = crate::leanh::lean_ctor_get(v_m_1291_, 1);
                v_isSharedCheck_1338_ = (!crate::leanh::lean_is_exclusive(v_m_1291_)) as u8;
                if v_isSharedCheck_1338_ == 0 {
                    v___x_1297_ = v_m_1291_;
                    v_isShared_1298_ = v_isSharedCheck_1338_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1295_);
                    crate::leanh::lean_inc(v_size_1294_);
                    crate::leanh::lean_dec(v_m_1291_);
                    v___x_1297_ = crate::leanh::lean_box(0);
                    v_isShared_1298_ = v_isSharedCheck_1338_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1299_ = lean_array_get_size(v_buckets_1295_);
                v___x_1300_ = l_Lean_ExprStructEq_hash(v_a_1292_);
                v___x_1301_ = 32u64;
                v___x_1302_ = lean_uint64_shift_right(v___x_1300_, v___x_1301_);
                v_fold_1303_ = lean_uint64_xor(v___x_1300_, v___x_1302_);
                v___x_1304_ = 16u64;
                v___x_1305_ = lean_uint64_shift_right(v_fold_1303_, v___x_1304_);
                v___x_1306_ = lean_uint64_xor(v_fold_1303_, v___x_1305_);
                v___x_1307_ = lean_uint64_to_usize(v___x_1306_);
                v___x_1308_ = lean_usize_of_nat(v___x_1299_);
                v___x_1309_ = 1usize;
                v___x_1310_ = lean_usize_sub(v___x_1308_, v___x_1309_);
                v___x_1311_ = lean_usize_land(v___x_1307_, v___x_1310_);
                v_bkt_1312_ = lean_array_uget_borrowed(v_buckets_1295_, v___x_1311_);
                v___x_1313_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__11___redArg(v_a_1292_, v_bkt_1312_);
                if v___x_1313_ == 0 {
                    v___x_1314_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1315_ = lean_nat_add(v_size_1294_, v___x_1314_);
                    crate::leanh::lean_dec(v_size_1294_);
                    crate::leanh::lean_inc(v_bkt_1312_);
                    v___x_1316_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1316_, 0, v_a_1292_);
                    crate::leanh::lean_ctor_set(v___x_1316_, 1, v_b_1293_);
                    crate::leanh::lean_ctor_set(v___x_1316_, 2, v_bkt_1312_);
                    v_buckets_x27_1317_ =
                        lean_array_uset(v_buckets_1295_, v___x_1311_, v___x_1316_);
                    v___x_1318_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1319_ = lean_nat_mul(v_size_x27_1315_, v___x_1318_);
                    v___x_1320_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1321_ = lean_nat_div(v___x_1319_, v___x_1320_);
                    crate::leanh::lean_dec(v___x_1319_);
                    v___x_1322_ = lean_array_get_size(v_buckets_x27_1317_);
                    v___x_1323_ = lean_nat_dec_le(v___x_1321_, v___x_1322_);
                    crate::leanh::lean_dec(v___x_1321_);
                    if v___x_1323_ == 0 {
                        v_val_1324_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12___redArg(v_buckets_x27_1317_);
                        if v_isShared_1298_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1297_, 1, v_val_1324_);
                            crate::leanh::lean_ctor_set(v___x_1297_, 0, v_size_x27_1315_);
                            v___x_1326_ = v___x_1297_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1327_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1327_,
                                0,
                                v_size_x27_1315_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_val_1324_);
                            v___x_1326_ = v_reuseFailAlloc_1327_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1298_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1297_, 1, v_buckets_x27_1317_);
                            crate::leanh::lean_ctor_set(v___x_1297_, 0, v_size_x27_1315_);
                            v___x_1329_ = v___x_1297_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1330_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1330_,
                                0,
                                v_size_x27_1315_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1330_,
                                1,
                                v_buckets_x27_1317_,
                            );
                            v___x_1329_ = v_reuseFailAlloc_1330_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1312_);
                    v___x_1331_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1332_ =
                        lean_array_uset(v_buckets_1295_, v___x_1311_, v___x_1331_);
                    v___x_1333_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__13___redArg(v_a_1292_, v_b_1293_, v_bkt_1312_);
                    v___x_1334_ = lean_array_uset(v_buckets_x27_1332_, v___x_1311_, v___x_1333_);
                    if v_isShared_1298_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1297_, 1, v___x_1334_);
                        v___x_1336_ = v___x_1297_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1337_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_size_1294_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1337_, 1, v___x_1334_);
                        v___x_1336_ = v_reuseFailAlloc_1337_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1326_;
            }
            3 => {
                return v___x_1329_;
            }
            4 => {
                return v___x_1336_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__2(
    mut v_a_1339_: *mut crate::leanh::LeanObject,
    mut v_e_1340_: *mut crate::leanh::LeanObject,
    mut v_a_1341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1343_ = lean_st_ref_take(v_a_1339_);
    v___x_1344_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7___redArg(v___x_1343_, v_e_1340_, v_a_1341_);
    v___x_1345_ = lean_st_ref_set(v_a_1339_, v___x_1344_);
    v___x_1346_ = crate::leanh::lean_box(0);
    return v___x_1346_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__2___boxed(
    mut v_a_1347_: *mut crate::leanh::LeanObject,
    mut v_e_1348_: *mut crate::leanh::LeanObject,
    mut v_a_1349_: *mut crate::leanh::LeanObject,
    mut v___y_1350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1351_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__2(v_a_1347_, v_e_1348_, v_a_1349_);
    crate::leanh::lean_dec(v_a_1347_);
    return v_res_1351_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__2(
    mut v_pre_1353_: *mut crate::leanh::LeanObject,
    mut v_post_1354_: *mut crate::leanh::LeanObject,
    mut v_sz_1355_: usize,
    mut v_i_1356_: usize,
    mut v_bs_1357_: *mut crate::leanh::LeanObject,
    mut v___y_1358_: *mut crate::leanh::LeanObject,
    mut v___y_1359_: *mut crate::leanh::LeanObject,
    mut v___y_1360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1362_: u8 = 0;
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: usize = 0;
    let mut v___x_1370_: usize = 0;
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1376_: u8 = 0;
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1362_ = lean_usize_dec_lt(v_i_1356_, v_sz_1355_);
                if v___x_1362_ == 0 {
                    crate::leanh::lean_dec_ref(v_post_1354_);
                    crate::leanh::lean_dec_ref(v_pre_1353_);
                    v___x_1363_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1363_, 0, v_bs_1357_);
                    return v___x_1363_;
                } else {
                    v_v_1364_ = lean_array_uget_borrowed(v_bs_1357_, v_i_1356_);
                    crate::leanh::lean_inc(v_v_1364_);
                    crate::leanh::lean_inc_ref(v_post_1354_);
                    crate::leanh::lean_inc_ref(v_pre_1353_);
                    v___x_1365_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1353_, v_post_1354_, v_v_1364_, v___y_1358_, v___y_1359_, v___y_1360_);
                    if crate::leanh::lean_obj_tag(v___x_1365_) == 0 {
                        v_a_1366_ = crate::leanh::lean_ctor_get(v___x_1365_, 0);
                        crate::leanh::lean_inc(v_a_1366_);
                        crate::leanh::lean_dec_ref_known(v___x_1365_, 1);
                        v___x_1367_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1368_ = lean_array_uset(v_bs_1357_, v_i_1356_, v___x_1367_);
                        v___x_1369_ = 1usize;
                        v___x_1370_ = lean_usize_add(v_i_1356_, v___x_1369_);
                        v___x_1371_ = lean_array_uset(v_bs_x27_1368_, v_i_1356_, v_a_1366_);
                        v_i_1356_ = v___x_1370_;
                        v_bs_1357_ = v___x_1371_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_1357_);
                        crate::leanh::lean_dec_ref(v_post_1354_);
                        crate::leanh::lean_dec_ref(v_pre_1353_);
                        v_a_1373_ = crate::leanh::lean_ctor_get(v___x_1365_, 0);
                        v_isSharedCheck_1380_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1365_)) as u8;
                        if v_isSharedCheck_1380_ == 0 {
                            v___x_1375_ = v___x_1365_;
                            v_isShared_1376_ = v_isSharedCheck_1380_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1373_);
                            crate::leanh::lean_dec(v___x_1365_);
                            v___x_1375_ = crate::leanh::lean_box(0);
                            v_isShared_1376_ = v_isSharedCheck_1380_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1376_ == 0 {
                    v___x_1378_ = v___x_1375_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
                    v___x_1378_ = v_reuseFailAlloc_1379_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__5(
    mut v_pre_1381_: *mut crate::leanh::LeanObject,
    mut v_post_1382_: *mut crate::leanh::LeanObject,
    mut v_x_1383_: *mut crate::leanh::LeanObject,
    mut v_x_1384_: *mut crate::leanh::LeanObject,
    mut v_x_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
    mut v___y_1387_: *mut crate::leanh::LeanObject,
    mut v___y_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1398_: usize = 0;
    let mut v___x_1399_: usize = 0;
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1411_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1383_) == 5 {
                    v_fn_1390_ = crate::leanh::lean_ctor_get(v_x_1383_, 0);
                    crate::leanh::lean_inc_ref(v_fn_1390_);
                    v_arg_1391_ = crate::leanh::lean_ctor_get(v_x_1383_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1391_);
                    crate::leanh::lean_dec_ref_known(v_x_1383_, 2);
                    v___x_1392_ = lean_array_set(v_x_1384_, v_x_1385_, v_arg_1391_);
                    v___x_1393_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1394_ = lean_nat_sub(v_x_1385_, v___x_1393_);
                    crate::leanh::lean_dec(v_x_1385_);
                    v_x_1383_ = v_fn_1390_;
                    v_x_1384_ = v___x_1392_;
                    v_x_1385_ = v___x_1394_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_1385_);
                    crate::leanh::lean_inc_ref(v_post_1382_);
                    crate::leanh::lean_inc_ref(v_pre_1381_);
                    v___x_1396_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1381_, v_post_1382_, v_x_1383_, v___y_1386_, v___y_1387_, v___y_1388_);
                    if crate::leanh::lean_obj_tag(v___x_1396_) == 0 {
                        v_a_1397_ = crate::leanh::lean_ctor_get(v___x_1396_, 0);
                        crate::leanh::lean_inc(v_a_1397_);
                        crate::leanh::lean_dec_ref_known(v___x_1396_, 1);
                        v_sz_1398_ = lean_array_size(v_x_1384_);
                        v___x_1399_ = 0usize;
                        crate::leanh::lean_inc_ref(v_post_1382_);
                        crate::leanh::lean_inc_ref(v_pre_1381_);
                        v___x_1400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__2(v_pre_1381_, v_post_1382_, v_sz_1398_, v___x_1399_, v_x_1384_, v___y_1386_, v___y_1387_, v___y_1388_);
                        if crate::leanh::lean_obj_tag(v___x_1400_) == 0 {
                            v_a_1401_ = crate::leanh::lean_ctor_get(v___x_1400_, 0);
                            crate::leanh::lean_inc(v_a_1401_);
                            crate::leanh::lean_dec_ref_known(v___x_1400_, 1);
                            v___x_1402_ = l_Lean_mkAppN(v_a_1397_, v_a_1401_);
                            crate::leanh::lean_dec(v_a_1401_);
                            v___x_1403_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1381_, v_post_1382_, v___x_1402_, v___y_1386_, v___y_1387_, v___y_1388_);
                            return v___x_1403_;
                        } else {
                            crate::leanh::lean_dec(v_a_1397_);
                            crate::leanh::lean_dec_ref(v_post_1382_);
                            crate::leanh::lean_dec_ref(v_pre_1381_);
                            v_a_1404_ = crate::leanh::lean_ctor_get(v___x_1400_, 0);
                            v_isSharedCheck_1411_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1400_)) as u8;
                            if v_isSharedCheck_1411_ == 0 {
                                v___x_1406_ = v___x_1400_;
                                v_isShared_1407_ = v_isSharedCheck_1411_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1404_);
                                crate::leanh::lean_dec(v___x_1400_);
                                v___x_1406_ = crate::leanh::lean_box(0);
                                v_isShared_1407_ = v_isSharedCheck_1411_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_1384_);
                        crate::leanh::lean_dec_ref(v_post_1382_);
                        crate::leanh::lean_dec_ref(v_pre_1381_);
                        return v___x_1396_;
                    }
                }
            }
            1 => {
                if v_isShared_1407_ == 0 {
                    v___x_1409_ = v___x_1406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1410_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
                    v___x_1409_ = v_reuseFailAlloc_1410_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1409_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__1(
    mut v___x_1412_: *mut crate::leanh::LeanObject,
    mut v_pre_1413_: *mut crate::leanh::LeanObject,
    mut v_e_1414_: *mut crate::leanh::LeanObject,
    mut v_post_1415_: *mut crate::leanh::LeanObject,
    mut v___y_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
    mut v___y_1418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1423_: u8 = 0;
    let mut v___y_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1428_: u8 = 0;
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: usize = 0;
    let mut v___x_1432_: usize = 0;
    let mut v___x_1433_: u8 = 0;
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1440_: u8 = 0;
    let mut v___y_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1443_: u8 = 0;
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1452_: u8 = 0;
    let mut v___y_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1456_: u8 = 0;
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: u8 = 0;
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v___y_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1474_: u8 = 0;
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: usize = 0;
    let mut v___x_1480_: usize = 0;
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: usize = 0;
    let mut v___x_1483_: usize = 0;
    let mut v___x_1484_: u8 = 0;
    let mut v_binderName_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1488_: u8 = 0;
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: usize = 0;
    let mut v___x_1494_: usize = 0;
    let mut v___x_1495_: u8 = 0;
    let mut v___x_1496_: usize = 0;
    let mut v___x_1497_: usize = 0;
    let mut v___x_1498_: u8 = 0;
    let mut v_declName_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1503_: u8 = 0;
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: usize = 0;
    let mut v___x_1511_: usize = 0;
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1513_: usize = 0;
    let mut v___x_1514_: usize = 0;
    let mut v___x_1515_: u8 = 0;
    let mut v_dummy_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: usize = 0;
    let mut v___x_1527_: usize = 0;
    let mut v___x_1528_: u8 = 0;
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: usize = 0;
    let mut v___x_1538_: usize = 0;
    let mut v___x_1539_: u8 = 0;
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1554_: u8 = 0;
    let mut v_a_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1558_: u8 = 0;
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1562_: u8 = 0;
    let mut v_a_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1566_: u8 = 0;
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1463_ = l_Lean_Core_checkSystem(v___x_1412_, v___y_1417_, v___y_1418_);
                if crate::leanh::lean_obj_tag(v___x_1463_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1463_, 1);
                    crate::leanh::lean_inc_ref(v_pre_1413_);
                    crate::leanh::lean_inc(v___y_1418_);
                    crate::leanh::lean_inc_ref(v___y_1417_);
                    crate::leanh::lean_inc_ref(v_e_1414_);
                    v___x_1464_ = crate::leanh::lean_apply_4(
                        v_pre_1413_,
                        v_e_1414_,
                        v___y_1417_,
                        v___y_1418_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_1464_) == 0 {
                        v_a_1465_ = crate::leanh::lean_ctor_get(v___x_1464_, 0);
                        v_isSharedCheck_1554_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1464_)) as u8;
                        if v_isSharedCheck_1554_ == 0 {
                            v___x_1467_ = v___x_1464_;
                            v_isShared_1468_ = v_isSharedCheck_1554_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1465_);
                            crate::leanh::lean_dec(v___x_1464_);
                            v___x_1467_ = crate::leanh::lean_box(0);
                            v_isShared_1468_ = v_isSharedCheck_1554_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_post_1415_);
                        crate::leanh::lean_dec_ref(v_e_1414_);
                        crate::leanh::lean_dec_ref(v_pre_1413_);
                        v_a_1555_ = crate::leanh::lean_ctor_get(v___x_1464_, 0);
                        v_isSharedCheck_1562_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1464_)) as u8;
                        if v_isSharedCheck_1562_ == 0 {
                            v___x_1557_ = v___x_1464_;
                            v_isShared_1558_ = v_isSharedCheck_1562_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1555_);
                            crate::leanh::lean_dec(v___x_1464_);
                            v___x_1557_ = crate::leanh::lean_box(0);
                            v_isShared_1558_ = v_isSharedCheck_1562_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_post_1415_);
                    crate::leanh::lean_dec_ref(v_e_1414_);
                    crate::leanh::lean_dec_ref(v_pre_1413_);
                    v_a_1563_ = crate::leanh::lean_ctor_get(v___x_1463_, 0);
                    v_isSharedCheck_1570_ = (!crate::leanh::lean_is_exclusive(v___x_1463_)) as u8;
                    if v_isSharedCheck_1570_ == 0 {
                        v___x_1565_ = v___x_1463_;
                        v_isShared_1566_ = v_isSharedCheck_1570_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1563_);
                        crate::leanh::lean_dec(v___x_1463_);
                        v___x_1565_ = crate::leanh::lean_box(0);
                        v_isShared_1566_ = v_isSharedCheck_1570_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1428_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1427_);
                    crate::leanh::lean_dec_ref(v___y_1422_);
                    v___x_1429_ = l_Lean_Expr_letE___override(
                        v___y_1421_,
                        v___y_1424_,
                        v___y_1426_,
                        v___y_1425_,
                        v___y_1423_,
                    );
                    v___x_1430_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___x_1429_, v___y_1416_, v___y_1417_, v___y_1418_);
                    return v___x_1430_;
                } else {
                    v___x_1431_ = lean_ptr_addr(v___y_1427_);
                    crate::leanh::lean_dec_ref(v___y_1427_);
                    v___x_1432_ = lean_ptr_addr(v___y_1425_);
                    v___x_1433_ = lean_usize_dec_eq(v___x_1431_, v___x_1432_);
                    if v___x_1433_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_1422_);
                        v___x_1434_ = l_Lean_Expr_letE___override(
                            v___y_1421_,
                            v___y_1424_,
                            v___y_1426_,
                            v___y_1425_,
                            v___y_1423_,
                        );
                        v___x_1435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___x_1434_, v___y_1416_, v___y_1417_, v___y_1418_);
                        return v___x_1435_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1426_);
                        crate::leanh::lean_dec_ref(v___y_1425_);
                        crate::leanh::lean_dec_ref(v___y_1424_);
                        crate::leanh::lean_dec(v___y_1421_);
                        v___x_1436_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___y_1422_, v___y_1416_, v___y_1417_, v___y_1418_);
                        return v___x_1436_;
                    }
                }
            }
            2 => {
                if v___y_1443_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1439_);
                    v___x_1444_ = l_Lean_Expr_lam___override(
                        v___y_1438_,
                        v___y_1442_,
                        v___y_1441_,
                        v___y_1440_,
                    );
                    v___x_1445_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___x_1444_, v___y_1416_, v___y_1417_, v___y_1418_);
                    return v___x_1445_;
                } else {
                    v___x_1446_ = l_Lean_instBEqBinderInfo_beq(v___y_1440_, v___y_1440_);
                    if v___x_1446_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_1439_);
                        v___x_1447_ = l_Lean_Expr_lam___override(
                            v___y_1438_,
                            v___y_1442_,
                            v___y_1441_,
                            v___y_1440_,
                        );
                        v___x_1448_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___x_1447_, v___y_1416_, v___y_1417_, v___y_1418_);
                        return v___x_1448_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1442_);
                        crate::leanh::lean_dec_ref(v___y_1441_);
                        crate::leanh::lean_dec(v___y_1438_);
                        v___x_1449_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___y_1439_, v___y_1416_, v___y_1417_, v___y_1418_);
                        return v___x_1449_;
                    }
                }
            }
            3 => {
                if v___y_1456_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1451_);
                    v___x_1457_ = l_Lean_Expr_forallE___override(
                        v___y_1453_,
                        v___y_1455_,
                        v___y_1454_,
                        v___y_1452_,
                    );
                    v___x_1458_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___x_1457_, v___y_1416_, v___y_1417_, v___y_1418_);
                    return v___x_1458_;
                } else {
                    v___x_1459_ = l_Lean_instBEqBinderInfo_beq(v___y_1452_, v___y_1452_);
                    if v___x_1459_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_1451_);
                        v___x_1460_ = l_Lean_Expr_forallE___override(
                            v___y_1453_,
                            v___y_1455_,
                            v___y_1454_,
                            v___y_1452_,
                        );
                        v___x_1461_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___x_1460_, v___y_1416_, v___y_1417_, v___y_1418_);
                        return v___x_1461_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1455_);
                        crate::leanh::lean_dec_ref(v___y_1454_);
                        crate::leanh::lean_dec(v___y_1453_);
                        v___x_1462_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___y_1451_, v___y_1416_, v___y_1417_, v___y_1418_);
                        return v___x_1462_;
                    }
                }
            }
            4 => match crate::leanh::lean_obj_tag(v_a_1465_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_post_1415_);
                    crate::leanh::lean_dec_ref(v_e_1414_);
                    crate::leanh::lean_dec_ref(v_pre_1413_);
                    v_e_1544_ = crate::leanh::lean_ctor_get(v_a_1465_, 0);
                    crate::leanh::lean_inc_ref(v_e_1544_);
                    crate::leanh::lean_dec_ref_known(v_a_1465_, 1);
                    if v_isShared_1468_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1467_, 0, v_e_1544_);
                        v___x_1546_ = v___x_1467_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1547_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_e_1544_);
                        v___x_1546_ = v_reuseFailAlloc_1547_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_1467_);
                    crate::leanh::lean_dec_ref(v_e_1414_);
                    v_e_1548_ = crate::leanh::lean_ctor_get(v_a_1465_, 0);
                    crate::leanh::lean_inc_ref(v_e_1548_);
                    crate::leanh::lean_dec_ref_known(v_a_1465_, 1);
                    crate::leanh::lean_inc_ref(v_post_1415_);
                    crate::leanh::lean_inc_ref(v_pre_1413_);
                    v___x_1549_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_e_1548_, v___y_1416_, v___y_1417_, v___y_1418_);
                    if crate::leanh::lean_obj_tag(v___x_1549_) == 0 {
                        v_a_1550_ = crate::leanh::lean_ctor_get(v___x_1549_, 0);
                        crate::leanh::lean_inc(v_a_1550_);
                        crate::leanh::lean_dec_ref_known(v___x_1549_, 1);
                        v___x_1551_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v_a_1550_, v___y_1416_, v___y_1417_, v___y_1418_);
                        return v___x_1551_;
                    } else {
                        crate::leanh::lean_dec_ref(v_post_1415_);
                        crate::leanh::lean_dec_ref(v_pre_1413_);
                        return v___x_1549_;
                    }
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_1467_);
                    v_e_x3f_1552_ = crate::leanh::lean_ctor_get(v_a_1465_, 0);
                    crate::leanh::lean_inc(v_e_x3f_1552_);
                    crate::leanh::lean_dec_ref_known(v_a_1465_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_1552_) == 0 {
                        v___y_1470_ = v_e_1414_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1414_);
                        v_val_1553_ = crate::leanh::lean_ctor_get(v_e_x3f_1552_, 0);
                        crate::leanh::lean_inc(v_val_1553_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_1552_, 1);
                        v___y_1470_ = v_val_1553_;
                        state = 5;
                        continue;
                    }
                }
            },
            5 => match crate::leanh::lean_obj_tag(v___y_1470_) {
                7 => {
                    v_binderName_1471_ = crate::leanh::lean_ctor_get(v___y_1470_, 0);
                    crate::leanh::lean_inc(v_binderName_1471_);
                    v_binderType_1472_ = crate::leanh::lean_ctor_get(v___y_1470_, 1);
                    v_body_1473_ = crate::leanh::lean_ctor_get(v___y_1470_, 2);
                    v_binderInfo_1474_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1470_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_1472_);
                    crate::leanh::lean_inc_ref(v_post_1415_);
                    crate::leanh::lean_inc_ref(v_pre_1413_);
                    v___x_1475_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_binderType_1472_, v___y_1416_, v___y_1417_, v___y_1418_);
                    if crate::leanh::lean_obj_tag(v___x_1475_) == 0 {
                        v_a_1476_ = crate::leanh::lean_ctor_get(v___x_1475_, 0);
                        crate::leanh::lean_inc(v_a_1476_);
                        crate::leanh::lean_dec_ref_known(v___x_1475_, 1);
                        crate::leanh::lean_inc_ref(v_body_1473_);
                        crate::leanh::lean_inc_ref(v_post_1415_);
                        crate::leanh::lean_inc_ref(v_pre_1413_);
                        v___x_1477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_body_1473_, v___y_1416_, v___y_1417_, v___y_1418_);
                        if crate::leanh::lean_obj_tag(v___x_1477_) == 0 {
                            v_a_1478_ = crate::leanh::lean_ctor_get(v___x_1477_, 0);
                            crate::leanh::lean_inc(v_a_1478_);
                            crate::leanh::lean_dec_ref_known(v___x_1477_, 1);
                            v___x_1479_ = lean_ptr_addr(v_binderType_1472_);
                            v___x_1480_ = lean_ptr_addr(v_a_1476_);
                            v___x_1481_ = lean_usize_dec_eq(v___x_1479_, v___x_1480_);
                            if v___x_1481_ == 0 {
                                v___y_1451_ = v___y_1470_;
                                v___y_1452_ = v_binderInfo_1474_;
                                v___y_1453_ = v_binderName_1471_;
                                v___y_1454_ = v_a_1478_;
                                v___y_1455_ = v_a_1476_;
                                v___y_1456_ = v___x_1481_;
                                state = 3;
                                continue;
                            } else {
                                v___x_1482_ = lean_ptr_addr(v_body_1473_);
                                v___x_1483_ = lean_ptr_addr(v_a_1478_);
                                v___x_1484_ = lean_usize_dec_eq(v___x_1482_, v___x_1483_);
                                v___y_1451_ = v___y_1470_;
                                v___y_1452_ = v_binderInfo_1474_;
                                v___y_1453_ = v_binderName_1471_;
                                v___y_1454_ = v_a_1478_;
                                v___y_1455_ = v_a_1476_;
                                v___y_1456_ = v___x_1484_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1476_);
                            crate::leanh::lean_dec_ref_known(v___y_1470_, 3);
                            crate::leanh::lean_dec(v_binderName_1471_);
                            crate::leanh::lean_dec_ref(v_post_1415_);
                            crate::leanh::lean_dec_ref(v_pre_1413_);
                            return v___x_1477_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_1470_, 3);
                        crate::leanh::lean_dec(v_binderName_1471_);
                        crate::leanh::lean_dec_ref(v_post_1415_);
                        crate::leanh::lean_dec_ref(v_pre_1413_);
                        return v___x_1475_;
                    }
                }
                6 => {
                    v_binderName_1485_ = crate::leanh::lean_ctor_get(v___y_1470_, 0);
                    crate::leanh::lean_inc(v_binderName_1485_);
                    v_binderType_1486_ = crate::leanh::lean_ctor_get(v___y_1470_, 1);
                    v_body_1487_ = crate::leanh::lean_ctor_get(v___y_1470_, 2);
                    v_binderInfo_1488_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1470_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_1486_);
                    crate::leanh::lean_inc_ref(v_post_1415_);
                    crate::leanh::lean_inc_ref(v_pre_1413_);
                    v___x_1489_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_binderType_1486_, v___y_1416_, v___y_1417_, v___y_1418_);
                    if crate::leanh::lean_obj_tag(v___x_1489_) == 0 {
                        v_a_1490_ = crate::leanh::lean_ctor_get(v___x_1489_, 0);
                        crate::leanh::lean_inc(v_a_1490_);
                        crate::leanh::lean_dec_ref_known(v___x_1489_, 1);
                        crate::leanh::lean_inc_ref(v_body_1487_);
                        crate::leanh::lean_inc_ref(v_post_1415_);
                        crate::leanh::lean_inc_ref(v_pre_1413_);
                        v___x_1491_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_body_1487_, v___y_1416_, v___y_1417_, v___y_1418_);
                        if crate::leanh::lean_obj_tag(v___x_1491_) == 0 {
                            v_a_1492_ = crate::leanh::lean_ctor_get(v___x_1491_, 0);
                            crate::leanh::lean_inc(v_a_1492_);
                            crate::leanh::lean_dec_ref_known(v___x_1491_, 1);
                            v___x_1493_ = lean_ptr_addr(v_binderType_1486_);
                            v___x_1494_ = lean_ptr_addr(v_a_1490_);
                            v___x_1495_ = lean_usize_dec_eq(v___x_1493_, v___x_1494_);
                            if v___x_1495_ == 0 {
                                v___y_1438_ = v_binderName_1485_;
                                v___y_1439_ = v___y_1470_;
                                v___y_1440_ = v_binderInfo_1488_;
                                v___y_1441_ = v_a_1492_;
                                v___y_1442_ = v_a_1490_;
                                v___y_1443_ = v___x_1495_;
                                state = 2;
                                continue;
                            } else {
                                v___x_1496_ = lean_ptr_addr(v_body_1487_);
                                v___x_1497_ = lean_ptr_addr(v_a_1492_);
                                v___x_1498_ = lean_usize_dec_eq(v___x_1496_, v___x_1497_);
                                v___y_1438_ = v_binderName_1485_;
                                v___y_1439_ = v___y_1470_;
                                v___y_1440_ = v_binderInfo_1488_;
                                v___y_1441_ = v_a_1492_;
                                v___y_1442_ = v_a_1490_;
                                v___y_1443_ = v___x_1498_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1490_);
                            crate::leanh::lean_dec(v_binderName_1485_);
                            crate::leanh::lean_dec_ref_known(v___y_1470_, 3);
                            crate::leanh::lean_dec_ref(v_post_1415_);
                            crate::leanh::lean_dec_ref(v_pre_1413_);
                            return v___x_1491_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_binderName_1485_);
                        crate::leanh::lean_dec_ref_known(v___y_1470_, 3);
                        crate::leanh::lean_dec_ref(v_post_1415_);
                        crate::leanh::lean_dec_ref(v_pre_1413_);
                        return v___x_1489_;
                    }
                }
                8 => {
                    v_declName_1499_ = crate::leanh::lean_ctor_get(v___y_1470_, 0);
                    crate::leanh::lean_inc(v_declName_1499_);
                    v_type_1500_ = crate::leanh::lean_ctor_get(v___y_1470_, 1);
                    v_value_1501_ = crate::leanh::lean_ctor_get(v___y_1470_, 2);
                    v_body_1502_ = crate::leanh::lean_ctor_get(v___y_1470_, 3);
                    crate::leanh::lean_inc_ref(v_body_1502_);
                    v_nondep_1503_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1470_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_type_1500_);
                    crate::leanh::lean_inc_ref(v_post_1415_);
                    crate::leanh::lean_inc_ref(v_pre_1413_);
                    v___x_1504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_type_1500_, v___y_1416_, v___y_1417_, v___y_1418_);
                    if crate::leanh::lean_obj_tag(v___x_1504_) == 0 {
                        v_a_1505_ = crate::leanh::lean_ctor_get(v___x_1504_, 0);
                        crate::leanh::lean_inc(v_a_1505_);
                        crate::leanh::lean_dec_ref_known(v___x_1504_, 1);
                        crate::leanh::lean_inc_ref(v_value_1501_);
                        crate::leanh::lean_inc_ref(v_post_1415_);
                        crate::leanh::lean_inc_ref(v_pre_1413_);
                        v___x_1506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_value_1501_, v___y_1416_, v___y_1417_, v___y_1418_);
                        if crate::leanh::lean_obj_tag(v___x_1506_) == 0 {
                            v_a_1507_ = crate::leanh::lean_ctor_get(v___x_1506_, 0);
                            crate::leanh::lean_inc(v_a_1507_);
                            crate::leanh::lean_dec_ref_known(v___x_1506_, 1);
                            crate::leanh::lean_inc_ref(v_body_1502_);
                            crate::leanh::lean_inc_ref(v_post_1415_);
                            crate::leanh::lean_inc_ref(v_pre_1413_);
                            v___x_1508_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_body_1502_, v___y_1416_, v___y_1417_, v___y_1418_);
                            if crate::leanh::lean_obj_tag(v___x_1508_) == 0 {
                                v_a_1509_ = crate::leanh::lean_ctor_get(v___x_1508_, 0);
                                crate::leanh::lean_inc(v_a_1509_);
                                crate::leanh::lean_dec_ref_known(v___x_1508_, 1);
                                v___x_1510_ = lean_ptr_addr(v_type_1500_);
                                v___x_1511_ = lean_ptr_addr(v_a_1505_);
                                v___x_1512_ = lean_usize_dec_eq(v___x_1510_, v___x_1511_);
                                if v___x_1512_ == 0 {
                                    v___y_1421_ = v_declName_1499_;
                                    v___y_1422_ = v___y_1470_;
                                    v___y_1423_ = v_nondep_1503_;
                                    v___y_1424_ = v_a_1505_;
                                    v___y_1425_ = v_a_1509_;
                                    v___y_1426_ = v_a_1507_;
                                    v___y_1427_ = v_body_1502_;
                                    v___y_1428_ = v___x_1512_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1513_ = lean_ptr_addr(v_value_1501_);
                                    v___x_1514_ = lean_ptr_addr(v_a_1507_);
                                    v___x_1515_ = lean_usize_dec_eq(v___x_1513_, v___x_1514_);
                                    v___y_1421_ = v_declName_1499_;
                                    v___y_1422_ = v___y_1470_;
                                    v___y_1423_ = v_nondep_1503_;
                                    v___y_1424_ = v_a_1505_;
                                    v___y_1425_ = v_a_1509_;
                                    v___y_1426_ = v_a_1507_;
                                    v___y_1427_ = v_body_1502_;
                                    v___y_1428_ = v___x_1515_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1507_);
                                crate::leanh::lean_dec(v_a_1505_);
                                crate::leanh::lean_dec_ref(v_body_1502_);
                                crate::leanh::lean_dec(v_declName_1499_);
                                crate::leanh::lean_dec_ref_known(v___y_1470_, 4);
                                crate::leanh::lean_dec_ref(v_post_1415_);
                                crate::leanh::lean_dec_ref(v_pre_1413_);
                                return v___x_1508_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1505_);
                            crate::leanh::lean_dec_ref(v_body_1502_);
                            crate::leanh::lean_dec_ref_known(v___y_1470_, 4);
                            crate::leanh::lean_dec(v_declName_1499_);
                            crate::leanh::lean_dec_ref(v_post_1415_);
                            crate::leanh::lean_dec_ref(v_pre_1413_);
                            return v___x_1506_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_1502_);
                        crate::leanh::lean_dec(v_declName_1499_);
                        crate::leanh::lean_dec_ref_known(v___y_1470_, 4);
                        crate::leanh::lean_dec_ref(v_post_1415_);
                        crate::leanh::lean_dec_ref(v_pre_1413_);
                        return v___x_1504_;
                    }
                }
                5 => {
                    v_dummy_1516_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_preprocess___lam__1___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_preprocess___lam__1___closed__0_once
                        ),
                        _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__0,
                    );
                    v_nargs_1517_ = l_Lean_Expr_getAppNumArgs(v___y_1470_);
                    crate::leanh::lean_inc(v_nargs_1517_);
                    v___x_1518_ = lean_mk_array(v_nargs_1517_, v_dummy_1516_);
                    v___x_1519_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1520_ = lean_nat_sub(v_nargs_1517_, v___x_1519_);
                    crate::leanh::lean_dec(v_nargs_1517_);
                    v___x_1521_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__5(v_pre_1413_, v_post_1415_, v___y_1470_, v___x_1518_, v___x_1520_, v___y_1416_, v___y_1417_, v___y_1418_);
                    return v___x_1521_;
                }
                10 => {
                    v_data_1522_ = crate::leanh::lean_ctor_get(v___y_1470_, 0);
                    v_expr_1523_ = crate::leanh::lean_ctor_get(v___y_1470_, 1);
                    crate::leanh::lean_inc_ref(v_expr_1523_);
                    crate::leanh::lean_inc_ref(v_post_1415_);
                    crate::leanh::lean_inc_ref(v_pre_1413_);
                    v___x_1524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_expr_1523_, v___y_1416_, v___y_1417_, v___y_1418_);
                    if crate::leanh::lean_obj_tag(v___x_1524_) == 0 {
                        v_a_1525_ = crate::leanh::lean_ctor_get(v___x_1524_, 0);
                        crate::leanh::lean_inc(v_a_1525_);
                        crate::leanh::lean_dec_ref_known(v___x_1524_, 1);
                        v___x_1526_ = lean_ptr_addr(v_expr_1523_);
                        v___x_1527_ = lean_ptr_addr(v_a_1525_);
                        v___x_1528_ = lean_usize_dec_eq(v___x_1526_, v___x_1527_);
                        if v___x_1528_ == 0 {
                            crate::leanh::lean_inc(v_data_1522_);
                            crate::leanh::lean_dec_ref_known(v___y_1470_, 2);
                            v___x_1529_ = l_Lean_Expr_mdata___override(v_data_1522_, v_a_1525_);
                            v___x_1530_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___x_1529_, v___y_1416_, v___y_1417_, v___y_1418_);
                            return v___x_1530_;
                        } else {
                            crate::leanh::lean_dec(v_a_1525_);
                            v___x_1531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___y_1470_, v___y_1416_, v___y_1417_, v___y_1418_);
                            return v___x_1531_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_1470_, 2);
                        crate::leanh::lean_dec_ref(v_post_1415_);
                        crate::leanh::lean_dec_ref(v_pre_1413_);
                        return v___x_1524_;
                    }
                }
                11 => {
                    v_typeName_1532_ = crate::leanh::lean_ctor_get(v___y_1470_, 0);
                    v_idx_1533_ = crate::leanh::lean_ctor_get(v___y_1470_, 1);
                    v_struct_1534_ = crate::leanh::lean_ctor_get(v___y_1470_, 2);
                    crate::leanh::lean_inc_ref(v_struct_1534_);
                    crate::leanh::lean_inc_ref(v_post_1415_);
                    crate::leanh::lean_inc_ref(v_pre_1413_);
                    v___x_1535_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_struct_1534_, v___y_1416_, v___y_1417_, v___y_1418_);
                    if crate::leanh::lean_obj_tag(v___x_1535_) == 0 {
                        v_a_1536_ = crate::leanh::lean_ctor_get(v___x_1535_, 0);
                        crate::leanh::lean_inc(v_a_1536_);
                        crate::leanh::lean_dec_ref_known(v___x_1535_, 1);
                        v___x_1537_ = lean_ptr_addr(v_struct_1534_);
                        v___x_1538_ = lean_ptr_addr(v_a_1536_);
                        v___x_1539_ = lean_usize_dec_eq(v___x_1537_, v___x_1538_);
                        if v___x_1539_ == 0 {
                            crate::leanh::lean_inc(v_idx_1533_);
                            crate::leanh::lean_inc(v_typeName_1532_);
                            crate::leanh::lean_dec_ref_known(v___y_1470_, 3);
                            v___x_1540_ = l_Lean_Expr_proj___override(
                                v_typeName_1532_,
                                v_idx_1533_,
                                v_a_1536_,
                            );
                            v___x_1541_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___x_1540_, v___y_1416_, v___y_1417_, v___y_1418_);
                            return v___x_1541_;
                        } else {
                            crate::leanh::lean_dec(v_a_1536_);
                            v___x_1542_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___y_1470_, v___y_1416_, v___y_1417_, v___y_1418_);
                            return v___x_1542_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_1470_, 3);
                        crate::leanh::lean_dec_ref(v_post_1415_);
                        crate::leanh::lean_dec_ref(v_pre_1413_);
                        return v___x_1535_;
                    }
                }
                _ => {
                    v___x_1543_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___y_1470_, v___y_1416_, v___y_1417_, v___y_1418_);
                    return v___x_1543_;
                }
            },
            6 => {
                return v___x_1546_;
            }
            7 => {
                if v_isShared_1558_ == 0 {
                    v___x_1560_ = v___x_1557_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1561_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
                    v___x_1560_ = v_reuseFailAlloc_1561_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1560_;
            }
            9 => {
                if v_isShared_1566_ == 0 {
                    v___x_1568_ = v___x_1565_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
                    v___x_1568_ = v_reuseFailAlloc_1569_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__1___boxed(
    mut v___x_1571_: *mut crate::leanh::LeanObject,
    mut v_pre_1572_: *mut crate::leanh::LeanObject,
    mut v_e_1573_: *mut crate::leanh::LeanObject,
    mut v_post_1574_: *mut crate::leanh::LeanObject,
    mut v___y_1575_: *mut crate::leanh::LeanObject,
    mut v___y_1576_: *mut crate::leanh::LeanObject,
    mut v___y_1577_: *mut crate::leanh::LeanObject,
    mut v___y_1578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1579_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__1(v___x_1571_, v_pre_1572_, v_e_1573_, v_post_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
    crate::leanh::lean_dec(v___y_1577_);
    crate::leanh::lean_dec_ref(v___y_1576_);
    crate::leanh::lean_dec(v___y_1575_);
    return v_res_1579_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(
    mut v_pre_1580_: *mut crate::leanh::LeanObject,
    mut v_post_1581_: *mut crate::leanh::LeanObject,
    mut v_e_1582_: *mut crate::leanh::LeanObject,
    mut v_a_1583_: *mut crate::leanh::LeanObject,
    mut v___y_1584_: *mut crate::leanh::LeanObject,
    mut v___y_1585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1592_: u8 = 0;
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1602_: u8 = 0;
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut v_unused_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1611_: u8 = 0;
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1615_: u8 = 0;
    let mut v_val_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut v_a_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1624_: u8 = 0;
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_1583_);
                v___x_1587_ = crate::leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_1587_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1587_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1587_, 2, v_a_1583_);
                v___x_1588_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__0(crate::leanh::lean_box(0), v___x_1587_, v___y_1584_, v___y_1585_);
                if crate::leanh::lean_obj_tag(v___x_1588_) == 0 {
                    v_a_1589_ = crate::leanh::lean_ctor_get(v___x_1588_, 0);
                    v_isSharedCheck_1620_ = (!crate::leanh::lean_is_exclusive(v___x_1588_)) as u8;
                    if v_isSharedCheck_1620_ == 0 {
                        v___x_1591_ = v___x_1588_;
                        v_isShared_1592_ = v_isSharedCheck_1620_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1589_);
                        crate::leanh::lean_dec(v___x_1588_);
                        v___x_1591_ = crate::leanh::lean_box(0);
                        v_isShared_1592_ = v_isSharedCheck_1620_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1582_);
                    crate::leanh::lean_dec_ref(v_post_1581_);
                    crate::leanh::lean_dec_ref(v_pre_1580_);
                    v_a_1621_ = crate::leanh::lean_ctor_get(v___x_1588_, 0);
                    v_isSharedCheck_1628_ = (!crate::leanh::lean_is_exclusive(v___x_1588_)) as u8;
                    if v_isSharedCheck_1628_ == 0 {
                        v___x_1623_ = v___x_1588_;
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1621_);
                        crate::leanh::lean_dec(v___x_1588_);
                        v___x_1623_ = crate::leanh::lean_box(0);
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1593_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4___redArg(v_a_1589_, v_e_1582_);
                crate::leanh::lean_dec(v_a_1589_);
                if crate::leanh::lean_obj_tag(v___x_1593_) == 0 {
                    crate::leanh::lean_del_object(v___x_1591_);
                    v___x_1594_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___closed__0;
                    crate::leanh::lean_inc_ref(v_e_1582_);
                    v___f_1595_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__1___boxed as *mut core::ffi::c_void, 8, 4);
                    crate::leanh::lean_closure_set(v___f_1595_, 0, v___x_1594_);
                    crate::leanh::lean_closure_set(v___f_1595_, 1, v_pre_1580_);
                    crate::leanh::lean_closure_set(v___f_1595_, 2, v_e_1582_);
                    crate::leanh::lean_closure_set(v___f_1595_, 3, v_post_1581_);
                    v___x_1596_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6___redArg(v___f_1595_, v_a_1583_, v___y_1584_, v___y_1585_);
                    if crate::leanh::lean_obj_tag(v___x_1596_) == 0 {
                        v_a_1597_ = crate::leanh::lean_ctor_get(v___x_1596_, 0);
                        crate::leanh::lean_inc_n(v_a_1597_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1596_, 1);
                        crate::leanh::lean_inc(v_a_1583_);
                        v___f_1598_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        crate::leanh::lean_closure_set(v___f_1598_, 0, v_a_1583_);
                        crate::leanh::lean_closure_set(v___f_1598_, 1, v_e_1582_);
                        crate::leanh::lean_closure_set(v___f_1598_, 2, v_a_1597_);
                        v___x_1599_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__0(crate::leanh::lean_box(0), v___f_1598_, v___y_1584_, v___y_1585_);
                        if crate::leanh::lean_obj_tag(v___x_1599_) == 0 {
                            v_isSharedCheck_1606_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1599_)) as u8;
                            if v_isSharedCheck_1606_ == 0 {
                                v_unused_1607_ = crate::leanh::lean_ctor_get(v___x_1599_, 0);
                                crate::leanh::lean_dec(v_unused_1607_);
                                v___x_1601_ = v___x_1599_;
                                v_isShared_1602_ = v_isSharedCheck_1606_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1599_);
                                v___x_1601_ = crate::leanh::lean_box(0);
                                v_isShared_1602_ = v_isSharedCheck_1606_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1597_);
                            v_a_1608_ = crate::leanh::lean_ctor_get(v___x_1599_, 0);
                            v_isSharedCheck_1615_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1599_)) as u8;
                            if v_isSharedCheck_1615_ == 0 {
                                v___x_1610_ = v___x_1599_;
                                v_isShared_1611_ = v_isSharedCheck_1615_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1608_);
                                crate::leanh::lean_dec(v___x_1599_);
                                v___x_1610_ = crate::leanh::lean_box(0);
                                v_isShared_1611_ = v_isSharedCheck_1615_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1582_);
                        return v___x_1596_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1582_);
                    crate::leanh::lean_dec_ref(v_post_1581_);
                    crate::leanh::lean_dec_ref(v_pre_1580_);
                    v_val_1616_ = crate::leanh::lean_ctor_get(v___x_1593_, 0);
                    crate::leanh::lean_inc(v_val_1616_);
                    crate::leanh::lean_dec_ref_known(v___x_1593_, 1);
                    if v_isShared_1592_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1591_, 0, v_val_1616_);
                        v___x_1618_ = v___x_1591_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1619_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_val_1616_);
                        v___x_1618_ = v_reuseFailAlloc_1619_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1602_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1601_, 0, v_a_1597_);
                    v___x_1604_ = v___x_1601_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1605_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1597_);
                    v___x_1604_ = v_reuseFailAlloc_1605_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1604_;
            }
            4 => {
                if v_isShared_1611_ == 0 {
                    v___x_1613_ = v___x_1610_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1614_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
                    v___x_1613_ = v_reuseFailAlloc_1614_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1613_;
            }
            6 => {
                return v___x_1618_;
            }
            7 => {
                if v_isShared_1624_ == 0 {
                    v___x_1626_ = v___x_1623_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
                    v___x_1626_ = v_reuseFailAlloc_1627_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(
    mut v_pre_1629_: *mut crate::leanh::LeanObject,
    mut v_post_1630_: *mut crate::leanh::LeanObject,
    mut v_e_1631_: *mut crate::leanh::LeanObject,
    mut v_a_1632_: *mut crate::leanh::LeanObject,
    mut v___y_1633_: *mut crate::leanh::LeanObject,
    mut v___y_1634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1640_: u8 = 0;
    let mut v_e_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1655_: u8 = 0;
    let mut v_a_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1659_: u8 = 0;
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_post_1630_);
                crate::leanh::lean_inc(v___y_1634_);
                crate::leanh::lean_inc_ref(v___y_1633_);
                crate::leanh::lean_inc_ref(v_e_1631_);
                v___x_1636_ = crate::leanh::lean_apply_4(
                    v_post_1630_,
                    v_e_1631_,
                    v___y_1633_,
                    v___y_1634_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1636_) == 0 {
                    v_a_1637_ = crate::leanh::lean_ctor_get(v___x_1636_, 0);
                    v_isSharedCheck_1655_ = (!crate::leanh::lean_is_exclusive(v___x_1636_)) as u8;
                    if v_isSharedCheck_1655_ == 0 {
                        v___x_1639_ = v___x_1636_;
                        v_isShared_1640_ = v_isSharedCheck_1655_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1637_);
                        crate::leanh::lean_dec(v___x_1636_);
                        v___x_1639_ = crate::leanh::lean_box(0);
                        v_isShared_1640_ = v_isSharedCheck_1655_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1631_);
                    crate::leanh::lean_dec_ref(v_post_1630_);
                    crate::leanh::lean_dec_ref(v_pre_1629_);
                    v_a_1656_ = crate::leanh::lean_ctor_get(v___x_1636_, 0);
                    v_isSharedCheck_1663_ = (!crate::leanh::lean_is_exclusive(v___x_1636_)) as u8;
                    if v_isSharedCheck_1663_ == 0 {
                        v___x_1658_ = v___x_1636_;
                        v_isShared_1659_ = v_isSharedCheck_1663_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1656_);
                        crate::leanh::lean_dec(v___x_1636_);
                        v___x_1658_ = crate::leanh::lean_box(0);
                        v_isShared_1659_ = v_isSharedCheck_1663_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_1637_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_e_1631_);
                    crate::leanh::lean_dec_ref(v_post_1630_);
                    crate::leanh::lean_dec_ref(v_pre_1629_);
                    v_e_1641_ = crate::leanh::lean_ctor_get(v_a_1637_, 0);
                    crate::leanh::lean_inc_ref(v_e_1641_);
                    crate::leanh::lean_dec_ref_known(v_a_1637_, 1);
                    if v_isShared_1640_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1639_, 0, v_e_1641_);
                        v___x_1643_ = v___x_1639_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1644_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_e_1641_);
                        v___x_1643_ = v_reuseFailAlloc_1644_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_1639_);
                    crate::leanh::lean_dec_ref(v_e_1631_);
                    v_e_1645_ = crate::leanh::lean_ctor_get(v_a_1637_, 0);
                    crate::leanh::lean_inc_ref(v_e_1645_);
                    crate::leanh::lean_dec_ref_known(v_a_1637_, 1);
                    v___x_1646_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1629_, v_post_1630_, v_e_1645_, v_a_1632_, v___y_1633_, v___y_1634_);
                    return v___x_1646_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_post_1630_);
                    crate::leanh::lean_dec_ref(v_pre_1629_);
                    v_e_x3f_1647_ = crate::leanh::lean_ctor_get(v_a_1637_, 0);
                    crate::leanh::lean_inc(v_e_x3f_1647_);
                    crate::leanh::lean_dec_ref_known(v_a_1637_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_1647_) == 0 {
                        if v_isShared_1640_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1639_, 0, v_e_1631_);
                            v___x_1649_ = v___x_1639_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1650_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_e_1631_);
                            v___x_1649_ = v_reuseFailAlloc_1650_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1631_);
                        v_val_1651_ = crate::leanh::lean_ctor_get(v_e_x3f_1647_, 0);
                        crate::leanh::lean_inc(v_val_1651_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_1647_, 1);
                        if v_isShared_1640_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1639_, 0, v_val_1651_);
                            v___x_1653_ = v___x_1639_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1654_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_val_1651_);
                            v___x_1653_ = v_reuseFailAlloc_1654_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_1643_;
            }
            3 => {
                return v___x_1649_;
            }
            4 => {
                return v___x_1653_;
            }
            5 => {
                if v_isShared_1659_ == 0 {
                    v___x_1661_ = v___x_1658_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1662_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
                    v___x_1661_ = v_reuseFailAlloc_1662_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1661_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3___boxed(
    mut v_pre_1664_: *mut crate::leanh::LeanObject,
    mut v_post_1665_: *mut crate::leanh::LeanObject,
    mut v_e_1666_: *mut crate::leanh::LeanObject,
    mut v_a_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1671_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1664_, v_post_1665_, v_e_1666_, v_a_1667_, v___y_1668_, v___y_1669_);
    crate::leanh::lean_dec(v___y_1669_);
    crate::leanh::lean_dec_ref(v___y_1668_);
    crate::leanh::lean_dec(v_a_1667_);
    return v_res_1671_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__2___boxed(
    mut v_pre_1672_: *mut crate::leanh::LeanObject,
    mut v_post_1673_: *mut crate::leanh::LeanObject,
    mut v_sz_1674_: *mut crate::leanh::LeanObject,
    mut v_i_1675_: *mut crate::leanh::LeanObject,
    mut v_bs_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1681_: usize = 0;
    let mut v_i_boxed_1682_: usize = 0;
    let mut v_res_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1681_ = crate::leanh::lean_unbox_usize(v_sz_1674_);
    crate::leanh::lean_dec(v_sz_1674_);
    v_i_boxed_1682_ = crate::leanh::lean_unbox_usize(v_i_1675_);
    crate::leanh::lean_dec(v_i_1675_);
    v_res_1683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__2(v_pre_1672_, v_post_1673_, v_sz_boxed_1681_, v_i_boxed_1682_, v_bs_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
    crate::leanh::lean_dec(v___y_1679_);
    crate::leanh::lean_dec_ref(v___y_1678_);
    crate::leanh::lean_dec(v___y_1677_);
    return v_res_1683_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__5___boxed(
    mut v_pre_1684_: *mut crate::leanh::LeanObject,
    mut v_post_1685_: *mut crate::leanh::LeanObject,
    mut v_x_1686_: *mut crate::leanh::LeanObject,
    mut v_x_1687_: *mut crate::leanh::LeanObject,
    mut v_x_1688_: *mut crate::leanh::LeanObject,
    mut v___y_1689_: *mut crate::leanh::LeanObject,
    mut v___y_1690_: *mut crate::leanh::LeanObject,
    mut v___y_1691_: *mut crate::leanh::LeanObject,
    mut v___y_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__5(v_pre_1684_, v_post_1685_, v_x_1686_, v_x_1687_, v_x_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
    crate::leanh::lean_dec(v___y_1691_);
    crate::leanh::lean_dec_ref(v___y_1690_);
    crate::leanh::lean_dec(v___y_1689_);
    return v_res_1693_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___boxed(
    mut v_pre_1694_: *mut crate::leanh::LeanObject,
    mut v_post_1695_: *mut crate::leanh::LeanObject,
    mut v_e_1696_: *mut crate::leanh::LeanObject,
    mut v_a_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1694_, v_post_1695_, v_e_1696_, v_a_1697_, v___y_1698_, v___y_1699_);
    crate::leanh::lean_dec(v___y_1699_);
    crate::leanh::lean_dec_ref(v___y_1698_);
    crate::leanh::lean_dec(v_a_1697_);
    return v_res_1701_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___lam__0(
    mut v_00_u03b1_1702_: *mut crate::leanh::LeanObject,
    mut v_x_1703_: *mut crate::leanh::LeanObject,
    mut v___y_1704_: *mut crate::leanh::LeanObject,
    mut v___y_1705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1707_ = crate::leanh::lean_apply_1(v_x_1703_, crate::leanh::lean_box(0));
    v___x_1708_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1708_, 0, v___x_1707_);
    return v___x_1708_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___lam__0___boxed(
    mut v_00_u03b1_1709_: *mut crate::leanh::LeanObject,
    mut v_x_1710_: *mut crate::leanh::LeanObject,
    mut v___y_1711_: *mut crate::leanh::LeanObject,
    mut v___y_1712_: *mut crate::leanh::LeanObject,
    mut v___y_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___lam__0(
        v_00_u03b1_1709_,
        v_x_1710_,
        v___y_1711_,
        v___y_1712_,
    );
    crate::leanh::lean_dec(v___y_1712_);
    crate::leanh::lean_dec_ref(v___y_1711_);
    return v_res_1714_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1715_ = crate::leanh::lean_box(0);
    v___x_1716_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1717_ = lean_mk_array(v___x_1716_, v___x_1715_);
    return v___x_1717_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1718_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__0_once
        ),
        _init_l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__0,
    );
    v___x_1719_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1720_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1720_, 0, v___x_1719_);
    crate::leanh::lean_ctor_set(v___x_1720_, 1, v___x_1718_);
    return v___x_1720_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1721_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__1_once
        ),
        _init_l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__1,
    );
    v___x_1722_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_1722_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1722_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1722_, 2, v___x_1721_);
    return v___x_1722_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1(
    mut v_input_1723_: *mut crate::leanh::LeanObject,
    mut v_pre_1724_: *mut crate::leanh::LeanObject,
    mut v_post_1725_: *mut crate::leanh::LeanObject,
    mut v___y_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1738_: u8 = 0;
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1742_: u8 = 0;
    let mut v_unused_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1729_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__2_once), _init_l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__2);
                v___x_1730_ =
                    l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___lam__0(
                        crate::leanh::lean_box(0),
                        v___x_1729_,
                        v___y_1726_,
                        v___y_1727_,
                    );
                v_a_1731_ = crate::leanh::lean_ctor_get(v___x_1730_, 0);
                crate::leanh::lean_inc(v_a_1731_);
                crate::leanh::lean_dec_ref(v___x_1730_);
                v___x_1732_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1724_, v_post_1725_, v_input_1723_, v_a_1731_, v___y_1726_, v___y_1727_);
                if crate::leanh::lean_obj_tag(v___x_1732_) == 0 {
                    v_a_1733_ = crate::leanh::lean_ctor_get(v___x_1732_, 0);
                    crate::leanh::lean_inc(v_a_1733_);
                    crate::leanh::lean_dec_ref_known(v___x_1732_, 1);
                    v___x_1734_ = crate::leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_1734_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_1734_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_1734_, 2, v_a_1731_);
                    v___x_1735_ = l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___lam__0(crate::leanh::lean_box(0), v___x_1734_, v___y_1726_, v___y_1727_);
                    v_isSharedCheck_1742_ = (!crate::leanh::lean_is_exclusive(v___x_1735_)) as u8;
                    if v_isSharedCheck_1742_ == 0 {
                        v_unused_1743_ = crate::leanh::lean_ctor_get(v___x_1735_, 0);
                        crate::leanh::lean_dec(v_unused_1743_);
                        v___x_1737_ = v___x_1735_;
                        v_isShared_1738_ = v_isSharedCheck_1742_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1735_);
                        v___x_1737_ = crate::leanh::lean_box(0);
                        v_isShared_1738_ = v_isSharedCheck_1742_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1731_);
                    return v___x_1732_;
                }
            }
            1 => {
                if v_isShared_1738_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1737_, 0, v_a_1733_);
                    v___x_1740_ = v___x_1737_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1741_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1733_);
                    v___x_1740_ = v_reuseFailAlloc_1741_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1740_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___boxed(
    mut v_input_1744_: *mut crate::leanh::LeanObject,
    mut v_pre_1745_: *mut crate::leanh::LeanObject,
    mut v_post_1746_: *mut crate::leanh::LeanObject,
    mut v___y_1747_: *mut crate::leanh::LeanObject,
    mut v___y_1748_: *mut crate::leanh::LeanObject,
    mut v___y_1749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1750_ = l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1(
        v_input_1744_,
        v_pre_1745_,
        v_post_1746_,
        v___y_1747_,
        v___y_1748_,
    );
    crate::leanh::lean_dec(v___y_1748_);
    crate::leanh::lean_dec_ref(v___y_1747_);
    return v_res_1750_;
}
pub unsafe fn l_Lean_Elab_Structural_preprocess(
    mut v_e_1752_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_1753_: *mut crate::leanh::LeanObject,
    mut v_numFixedParams_1754_: *mut crate::leanh::LeanObject,
    mut v_a_1755_: *mut crate::leanh::LeanObject,
    mut v_a_1756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_recFnNames_1753_);
    v___x_1758_ = l_Lean_Meta_unfoldIfArgIsAppOf(
        v_recFnNames_1753_,
        v_numFixedParams_1754_,
        v_e_1752_,
        v_a_1755_,
        v_a_1756_,
    );
    if crate::leanh::lean_obj_tag(v___x_1758_) == 0 {
        let mut v_a_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1759_ = crate::leanh::lean_ctor_get(v___x_1758_, 0);
        crate::leanh::lean_inc(v_a_1759_);
        crate::leanh::lean_dec_ref_known(v___x_1758_, 1);
        v___f_1760_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_Structural_preprocess___lam__0___boxed as *mut core::ffi::c_void,
            5,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1760_, 0, v_recFnNames_1753_);
        v___f_1761_ = l_Lean_Elab_Structural_preprocess___closed__0;
        v___x_1762_ = l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1(
            v_a_1759_,
            v___f_1760_,
            v___f_1761_,
            v_a_1755_,
            v_a_1756_,
        );
        return v___x_1762_;
    } else {
        crate::leanh::lean_dec_ref(v_recFnNames_1753_);
        return v___x_1758_;
    }
}
pub unsafe fn l_Lean_Elab_Structural_preprocess___boxed(
    mut v_e_1763_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_1764_: *mut crate::leanh::LeanObject,
    mut v_numFixedParams_1765_: *mut crate::leanh::LeanObject,
    mut v_a_1766_: *mut crate::leanh::LeanObject,
    mut v_a_1767_: *mut crate::leanh::LeanObject,
    mut v_a_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1769_ = l_Lean_Elab_Structural_preprocess(
        v_e_1763_,
        v_recFnNames_1764_,
        v_numFixedParams_1765_,
        v_a_1766_,
        v_a_1767_,
    );
    crate::leanh::lean_dec(v_a_1767_);
    crate::leanh::lean_dec_ref(v_a_1766_);
    return v_res_1769_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4(
    mut v_00_u03b2_1770_: *mut crate::leanh::LeanObject,
    mut v_m_1771_: *mut crate::leanh::LeanObject,
    mut v_a_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1773_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4___redArg(v_m_1771_, v_a_1772_);
    return v___x_1773_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4___boxed(
    mut v_00_u03b2_1774_: *mut crate::leanh::LeanObject,
    mut v_m_1775_: *mut crate::leanh::LeanObject,
    mut v_a_1776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1777_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4(v_00_u03b2_1774_, v_m_1775_, v_a_1776_);
    crate::leanh::lean_dec_ref(v_a_1776_);
    crate::leanh::lean_dec_ref(v_m_1775_);
    return v_res_1777_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8(
    mut v_00_u03b1_1778_: *mut crate::leanh::LeanObject,
    mut v_ref_1779_: *mut crate::leanh::LeanObject,
    mut v___y_1780_: *mut crate::leanh::LeanObject,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1783_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_1779_);
    return v___x_1783_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___boxed(
    mut v_00_u03b1_1784_: *mut crate::leanh::LeanObject,
    mut v_ref_1785_: *mut crate::leanh::LeanObject,
    mut v___y_1786_: *mut crate::leanh::LeanObject,
    mut v___y_1787_: *mut crate::leanh::LeanObject,
    mut v___y_1788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1789_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_1784_, v_ref_1785_, v___y_1786_, v___y_1787_);
    crate::leanh::lean_dec(v___y_1787_);
    crate::leanh::lean_dec_ref(v___y_1786_);
    return v_res_1789_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9(
    mut v_00_u03b1_1790_: *mut crate::leanh::LeanObject,
    mut v___y_1791_: *mut crate::leanh::LeanObject,
    mut v___y_1792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1794_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg();
    return v___x_1794_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___boxed(
    mut v_00_u03b1_1795_: *mut crate::leanh::LeanObject,
    mut v___y_1796_: *mut crate::leanh::LeanObject,
    mut v___y_1797_: *mut crate::leanh::LeanObject,
    mut v___y_1798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1799_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9(v_00_u03b1_1795_, v___y_1796_, v___y_1797_);
    crate::leanh::lean_dec(v___y_1797_);
    crate::leanh::lean_dec_ref(v___y_1796_);
    return v_res_1799_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6(
    mut v_00_u03b1_1800_: *mut crate::leanh::LeanObject,
    mut v_x_1801_: *mut crate::leanh::LeanObject,
    mut v___y_1802_: *mut crate::leanh::LeanObject,
    mut v___y_1803_: *mut crate::leanh::LeanObject,
    mut v___y_1804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1806_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6___redArg(v_x_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
    return v___x_1806_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6___boxed(
    mut v_00_u03b1_1807_: *mut crate::leanh::LeanObject,
    mut v_x_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1813_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6(v_00_u03b1_1807_, v_x_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
    crate::leanh::lean_dec(v___y_1811_);
    crate::leanh::lean_dec_ref(v___y_1810_);
    crate::leanh::lean_dec(v___y_1809_);
    return v_res_1813_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7(
    mut v_00_u03b2_1814_: *mut crate::leanh::LeanObject,
    mut v_m_1815_: *mut crate::leanh::LeanObject,
    mut v_a_1816_: *mut crate::leanh::LeanObject,
    mut v_b_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1818_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7___redArg(v_m_1815_, v_a_1816_, v_b_1817_);
    return v___x_1818_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5(
    mut v_00_u03b2_1819_: *mut crate::leanh::LeanObject,
    mut v_a_1820_: *mut crate::leanh::LeanObject,
    mut v_x_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1822_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5___redArg(v_a_1820_, v_x_1821_);
    return v___x_1822_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5___boxed(
    mut v_00_u03b2_1823_: *mut crate::leanh::LeanObject,
    mut v_a_1824_: *mut crate::leanh::LeanObject,
    mut v_x_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1826_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5(v_00_u03b2_1823_, v_a_1824_, v_x_1825_);
    crate::leanh::lean_dec(v_x_1825_);
    crate::leanh::lean_dec_ref(v_a_1824_);
    return v_res_1826_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__11(
    mut v_00_u03b2_1827_: *mut crate::leanh::LeanObject,
    mut v_a_1828_: *mut crate::leanh::LeanObject,
    mut v_x_1829_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1830_: u8 = 0;
    v___x_1830_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__11___redArg(v_a_1828_, v_x_1829_);
    return v___x_1830_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__11___boxed(
    mut v_00_u03b2_1831_: *mut crate::leanh::LeanObject,
    mut v_a_1832_: *mut crate::leanh::LeanObject,
    mut v_x_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1834_: u8 = 0;
    let mut v_r_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_1831_, v_a_1832_, v_x_1833_);
    crate::leanh::lean_dec(v_x_1833_);
    crate::leanh::lean_dec_ref(v_a_1832_);
    v_r_1835_ = crate::leanh::lean_box((v_res_1834_) as usize);
    return v_r_1835_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12(
    mut v_00_u03b2_1836_: *mut crate::leanh::LeanObject,
    mut v_data_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1838_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12___redArg(v_data_1837_);
    return v___x_1838_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__13(
    mut v_00_u03b2_1839_: *mut crate::leanh::LeanObject,
    mut v_a_1840_: *mut crate::leanh::LeanObject,
    mut v_b_1841_: *mut crate::leanh::LeanObject,
    mut v_x_1842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1843_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__13___redArg(v_a_1840_, v_b_1841_, v_x_1842_);
    return v___x_1843_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13(
    mut v_00_u03b2_1844_: *mut crate::leanh::LeanObject,
    mut v_i_1845_: *mut crate::leanh::LeanObject,
    mut v_source_1846_: *mut crate::leanh::LeanObject,
    mut v_target_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v_i_1845_, v_source_1846_, v_target_1847_);
    return v___x_1848_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14(
    mut v_00_u03b2_1849_: *mut crate::leanh::LeanObject,
    mut v_x_1850_: *mut crate::leanh::LeanObject,
    mut v_x_1851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1852_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_x_1850_, v_x_1851_);
    return v___x_1852_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_Structural_Preprocess(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_RecAppSyntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_Structural_Preprocess(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_Structural_Preprocess(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_RecAppSyntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Preprocess(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_Structural_Preprocess(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_Structural_Preprocess(builtin);
}
