// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.FloatRecApp
// Imports: Lean.Meta.Transform Lean.Elab.RecAppSyntax
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_set, lean_array_size,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_ptr_addr, lean_st_ref_set, lean_st_ref_take,
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
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_beta,
    l_Lean_Expr_forallE___override, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_isApp, l_Lean_Expr_isMData, l_Lean_Expr_lam___override,
    l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override,
    l_Lean_Expr_sort___override, l_Lean_ExprStructEq_beq, l_Lean_ExprStructEq_hash,
    l_Lean_instBEqBinderInfo_beq, l_Lean_mkAppN,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::Transform::{
    initialize_Lean_Meta_Transform, runtime_initialize_Lean_Meta_Transform,
};
pub static l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0___closed__0_value:
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
    m_fun: l_Lean_Core_instInhabitedCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_WF_floatRecApp___lam__0___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_Elab_WF_floatRecApp___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_floatRecApp___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_WF_floatRecApp___lam__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_WF_floatRecApp___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_WF_floatRecApp___lam__1___closed__1_value: leanh::LeanStringObject<
    39,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116,
        105, 111, 110, 46, 87, 70, 46, 70, 108, 111, 97, 116, 82, 101, 99, 65, 112, 112, 0,
    ],
};
static mut l_Lean_Elab_WF_floatRecApp___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_floatRecApp___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_WF_floatRecApp___lam__1___closed__2_value: leanh::LeanStringObject<
    25,
> = leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 87, 70, 46, 102, 108, 111, 97, 116, 82, 101, 99,
        65, 112, 112, 0,
    ],
};
static mut l_Lean_Elab_WF_floatRecApp___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_floatRecApp___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_WF_floatRecApp___lam__1___closed__3_value: leanh::LeanStringObject<
    34,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_WF_floatRecApp___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_floatRecApp___lam__1___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_WF_floatRecApp___lam__1___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_WF_floatRecApp___lam__1___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value) as *mut leanh::LeanObject,7310567555909517314 as *mut leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value) as *mut leanh::LeanObject,273128857561458264 as *mut leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_WF_floatRecApp___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_WF_floatRecApp___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_WF_floatRecApp___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_floatRecApp___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_WF_floatRecApp___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_WF_floatRecApp___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_WF_floatRecApp___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_floatRecApp___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0(
    mut v_msg_862_: *mut leanh::LeanObject,
    mut v___y_863_: *mut leanh::LeanObject,
    mut v___y_864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587__overap_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_866_ = l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0___closed__0;
    v___x_587__overap_867_ = lean_panic_fn_borrowed(v___f_866_, v_msg_862_);
    leanh::lean_inc(v___y_864_);
    leanh::lean_inc_ref(v___y_863_);
    v___x_868_ = leanh::lean_apply_3(
        v___x_587__overap_867_,
        v___y_863_,
        v___y_864_,
        leanh::lean_box(0),
    );
    return v___x_868_;
}
pub unsafe fn l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0___boxed(
    mut v_msg_869_: *mut leanh::LeanObject,
    mut v___y_870_: *mut leanh::LeanObject,
    mut v___y_871_: *mut leanh::LeanObject,
    mut v___y_872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_873_ =
        l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0(v_msg_869_, v___y_870_, v___y_871_);
    leanh::lean_dec(v___y_871_);
    leanh::lean_dec_ref(v___y_870_);
    return v_res_873_;
}
pub unsafe fn l_Lean_Elab_WF_floatRecApp___lam__0(
    mut v_x_876_: *mut leanh::LeanObject,
    mut v___y_877_: *mut leanh::LeanObject,
    mut v___y_878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_880_ = l_Lean_Elab_WF_floatRecApp___lam__0___closed__0;
    v___x_881_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_881_, 0, v___x_880_);
    return v___x_881_;
}
pub unsafe fn l_Lean_Elab_WF_floatRecApp___lam__0___boxed(
    mut v_x_882_: *mut leanh::LeanObject,
    mut v___y_883_: *mut leanh::LeanObject,
    mut v___y_884_: *mut leanh::LeanObject,
    mut v___y_885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_886_ = l_Lean_Elab_WF_floatRecApp___lam__0(v_x_882_, v___y_883_, v___y_884_);
    leanh::lean_dec(v___y_884_);
    leanh::lean_dec_ref(v___y_883_);
    leanh::lean_dec_ref(v_x_882_);
    return v_res_886_;
}
pub unsafe fn _init_l_Lean_Elab_WF_floatRecApp___lam__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_887_ = leanh::lean_box(0);
    v_dummy_888_ = l_Lean_Expr_sort___override(v___x_887_);
    return v_dummy_888_;
}
pub unsafe fn _init_l_Lean_Elab_WF_floatRecApp___lam__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_892_ = l_Lean_Elab_WF_floatRecApp___lam__1___closed__3;
    v___x_893_ = leanh::lean_unsigned_to_nat(39);
    v___x_894_ = leanh::lean_unsigned_to_nat(36);
    v___x_895_ = l_Lean_Elab_WF_floatRecApp___lam__1___closed__2;
    v___x_896_ = l_Lean_Elab_WF_floatRecApp___lam__1___closed__1;
    v___x_897_ =
        l_mkPanicMessageWithDecl(v___x_896_, v___x_895_, v___x_894_, v___x_893_, v___x_892_);
    return v___x_897_;
}
pub unsafe fn l_Lean_Elab_WF_floatRecApp___lam__1(
    mut v_e_898_: *mut leanh::LeanObject,
    mut v___y_899_: *mut leanh::LeanObject,
    mut v___y_900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_906_: u8 = 0;
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: u8 = 0;
    let mut v_dummy_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_926_: u8 = 0;
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_930_: u8 = 0;
    let mut v___x_931_: u8 = 0;
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_931_ = l_Lean_Expr_isApp(v_e_898_);
                if v___x_931_ == 0 {
                    v___y_906_ = v___x_931_;
                    state = 2;
                    continue;
                } else {
                    v___x_932_ = l_Lean_Expr_getAppFn(v_e_898_);
                    v___x_933_ = l_Lean_Expr_isMData(v___x_932_);
                    leanh::lean_dec_ref(v___x_932_);
                    v___y_906_ = v___x_933_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_903_ = l_Lean_Elab_WF_floatRecApp___lam__0___closed__0;
                v___x_904_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_904_, 0, v___x_903_);
                return v___x_904_;
            }
            2 => {
                if v___y_906_ == 0 {
                    leanh::lean_dec_ref(v_e_898_);
                    state = 1;
                    continue;
                } else {
                    v___x_907_ = l_Lean_Expr_getAppFn(v_e_898_);
                    if leanh::lean_obj_tag(v___x_907_) == 10 {
                        v_data_908_ = leanh::lean_ctor_get(v___x_907_, 0);
                        leanh::lean_inc(v_data_908_);
                        v_expr_909_ = leanh::lean_ctor_get(v___x_907_, 1);
                        leanh::lean_inc_ref(v_expr_909_);
                        leanh::lean_dec_ref_known(v___x_907_, 2);
                        v___x_910_ = l_Lean_MData_isRecApp(v_data_908_);
                        if v___x_910_ == 0 {
                            leanh::lean_dec_ref(v_expr_909_);
                            leanh::lean_dec(v_data_908_);
                            leanh::lean_dec_ref(v_e_898_);
                            state = 1;
                            continue;
                        } else {
                            v_dummy_911_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_WF_floatRecApp___lam__1___closed__0
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_WF_floatRecApp___lam__1___closed__0_once
                                ),
                                _init_l_Lean_Elab_WF_floatRecApp___lam__1___closed__0,
                            );
                            v_nargs_912_ = l_Lean_Expr_getAppNumArgs(v_e_898_);
                            leanh::lean_inc(v_nargs_912_);
                            v___x_913_ = lean_mk_array(v_nargs_912_, v_dummy_911_);
                            v___x_914_ = leanh::lean_unsigned_to_nat(1);
                            v___x_915_ = lean_nat_sub(v_nargs_912_, v___x_914_);
                            leanh::lean_dec(v_nargs_912_);
                            v___x_916_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                v_e_898_, v___x_913_, v___x_915_,
                            );
                            v___x_917_ = l_Lean_Expr_beta(v_expr_909_, v___x_916_);
                            v___x_918_ = l_Lean_Expr_mdata___override(v_data_908_, v___x_917_);
                            v___x_919_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_919_, 0, v___x_918_);
                            v___x_920_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_920_, 0, v___x_919_);
                            return v___x_920_;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_907_);
                        leanh::lean_dec_ref(v_e_898_);
                        v___x_921_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_WF_floatRecApp___lam__1___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_WF_floatRecApp___lam__1___closed__4_once
                            ),
                            _init_l_Lean_Elab_WF_floatRecApp___lam__1___closed__4,
                        );
                        v___x_922_ = l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0(
                            v___x_921_, v___y_899_, v___y_900_,
                        );
                        if leanh::lean_obj_tag(v___x_922_) == 0 {
                            leanh::lean_dec_ref_known(v___x_922_, 1);
                            state = 1;
                            continue;
                        } else {
                            v_a_923_ = leanh::lean_ctor_get(v___x_922_, 0);
                            v_isSharedCheck_930_ =
                                (!leanh::lean_is_exclusive(v___x_922_)) as u8;
                            if v_isSharedCheck_930_ == 0 {
                                v___x_925_ = v___x_922_;
                                v_isShared_926_ = v_isSharedCheck_930_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_923_);
                                leanh::lean_dec(v___x_922_);
                                v___x_925_ = leanh::lean_box(0);
                                v_isShared_926_ = v_isSharedCheck_930_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_926_ == 0 {
                    v___x_928_ = v___x_925_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_929_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
                    v___x_928_ = v_reuseFailAlloc_929_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_WF_floatRecApp___lam__1___boxed(
    mut v_e_934_: *mut leanh::LeanObject,
    mut v___y_935_: *mut leanh::LeanObject,
    mut v___y_936_: *mut leanh::LeanObject,
    mut v___y_937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_938_ = l_Lean_Elab_WF_floatRecApp___lam__1(v_e_934_, v___y_935_, v___y_936_);
    leanh::lean_dec(v___y_936_);
    leanh::lean_dec_ref(v___y_935_);
    return v_res_938_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(
    mut v_00_u03b1_939_: *mut leanh::LeanObject,
    mut v_x_940_: *mut leanh::LeanObject,
    mut v___y_941_: *mut leanh::LeanObject,
    mut v___y_942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = leanh::lean_apply_1(v_x_940_, leanh::lean_box(0));
    v___x_945_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_945_, 0, v___x_944_);
    return v___x_945_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0___boxed(
    mut v_00_u03b1_946_: *mut leanh::LeanObject,
    mut v_x_947_: *mut leanh::LeanObject,
    mut v___y_948_: *mut leanh::LeanObject,
    mut v___y_949_: *mut leanh::LeanObject,
    mut v___y_950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_951_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(
        v_00_u03b1_946_,
        v_x_947_,
        v___y_948_,
        v___y_949_,
    );
    leanh::lean_dec(v___y_949_);
    leanh::lean_dec_ref(v___y_948_);
    return v_res_951_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(
    mut v_a_952_: *mut leanh::LeanObject,
    mut v_x_953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: u8 = 0;
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_953_) == 0 {
                    v___x_954_ = leanh::lean_box(0);
                    return v___x_954_;
                } else {
                    v_key_955_ = leanh::lean_ctor_get(v_x_953_, 0);
                    v_value_956_ = leanh::lean_ctor_get(v_x_953_, 1);
                    v_tail_957_ = leanh::lean_ctor_get(v_x_953_, 2);
                    v___x_958_ = l_Lean_ExprStructEq_beq(v_key_955_, v_a_952_);
                    if v___x_958_ == 0 {
                        v_x_953_ = v_tail_957_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_956_);
                        v___x_960_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_960_, 0, v_value_956_);
                        return v___x_960_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg___boxed(
    mut v_a_961_: *mut leanh::LeanObject,
    mut v_x_962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_963_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(v_a_961_, v_x_962_);
    leanh::lean_dec(v_x_962_);
    leanh::lean_dec_ref(v_a_961_);
    return v_res_963_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(
    mut v_m_964_: *mut leanh::LeanObject,
    mut v_a_965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: u64 = 0;
    let mut v___x_969_: u64 = 0;
    let mut v___x_970_: u64 = 0;
    let mut v_fold_971_: u64 = 0;
    let mut v___x_972_: u64 = 0;
    let mut v___x_973_: u64 = 0;
    let mut v___x_974_: u64 = 0;
    let mut v___x_975_: usize = 0;
    let mut v___x_976_: usize = 0;
    let mut v___x_977_: usize = 0;
    let mut v___x_978_: usize = 0;
    let mut v___x_979_: usize = 0;
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_966_ = leanh::lean_ctor_get(v_m_964_, 1);
    v___x_967_ = lean_array_get_size(v_buckets_966_);
    v___x_968_ = l_Lean_ExprStructEq_hash(v_a_965_);
    v___x_969_ = 32u64;
    v___x_970_ = lean_uint64_shift_right(v___x_968_, v___x_969_);
    v_fold_971_ = lean_uint64_xor(v___x_968_, v___x_970_);
    v___x_972_ = 16u64;
    v___x_973_ = lean_uint64_shift_right(v_fold_971_, v___x_972_);
    v___x_974_ = lean_uint64_xor(v_fold_971_, v___x_973_);
    v___x_975_ = lean_uint64_to_usize(v___x_974_);
    v___x_976_ = lean_usize_of_nat(v___x_967_);
    v___x_977_ = 1usize;
    v___x_978_ = lean_usize_sub(v___x_976_, v___x_977_);
    v___x_979_ = lean_usize_land(v___x_975_, v___x_978_);
    v___x_980_ = lean_array_uget_borrowed(v_buckets_966_, v___x_979_);
    v___x_981_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(v_a_965_, v___x_980_);
    return v___x_981_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg___boxed(
    mut v_m_982_: *mut leanh::LeanObject,
    mut v_a_983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_984_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_m_982_, v_a_983_);
    leanh::lean_dec_ref(v_a_983_);
    leanh::lean_dec_ref(v_m_982_);
    return v_res_984_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(
    mut v_x_985_: *mut leanh::LeanObject,
    mut v_x_986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_992_: u8 = 0;
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: u64 = 0;
    let mut v___x_995_: u64 = 0;
    let mut v___x_996_: u64 = 0;
    let mut v_fold_997_: u64 = 0;
    let mut v___x_998_: u64 = 0;
    let mut v___x_999_: u64 = 0;
    let mut v___x_1000_: u64 = 0;
    let mut v___x_1001_: usize = 0;
    let mut v___x_1002_: usize = 0;
    let mut v___x_1003_: usize = 0;
    let mut v___x_1004_: usize = 0;
    let mut v___x_1005_: usize = 0;
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1012_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_986_) == 0 {
                    return v_x_985_;
                } else {
                    v_key_987_ = leanh::lean_ctor_get(v_x_986_, 0);
                    v_value_988_ = leanh::lean_ctor_get(v_x_986_, 1);
                    v_tail_989_ = leanh::lean_ctor_get(v_x_986_, 2);
                    v_isSharedCheck_1012_ = (!leanh::lean_is_exclusive(v_x_986_)) as u8;
                    if v_isSharedCheck_1012_ == 0 {
                        v___x_991_ = v_x_986_;
                        v_isShared_992_ = v_isSharedCheck_1012_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_989_);
                        leanh::lean_inc(v_value_988_);
                        leanh::lean_inc(v_key_987_);
                        leanh::lean_dec(v_x_986_);
                        v___x_991_ = leanh::lean_box(0);
                        v_isShared_992_ = v_isSharedCheck_1012_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_993_ = lean_array_get_size(v_x_985_);
                v___x_994_ = l_Lean_ExprStructEq_hash(v_key_987_);
                v___x_995_ = 32u64;
                v___x_996_ = lean_uint64_shift_right(v___x_994_, v___x_995_);
                v_fold_997_ = lean_uint64_xor(v___x_994_, v___x_996_);
                v___x_998_ = 16u64;
                v___x_999_ = lean_uint64_shift_right(v_fold_997_, v___x_998_);
                v___x_1000_ = lean_uint64_xor(v_fold_997_, v___x_999_);
                v___x_1001_ = lean_uint64_to_usize(v___x_1000_);
                v___x_1002_ = lean_usize_of_nat(v___x_993_);
                v___x_1003_ = 1usize;
                v___x_1004_ = lean_usize_sub(v___x_1002_, v___x_1003_);
                v___x_1005_ = lean_usize_land(v___x_1001_, v___x_1004_);
                v___x_1006_ = lean_array_uget_borrowed(v_x_985_, v___x_1005_);
                leanh::lean_inc(v___x_1006_);
                if v_isShared_992_ == 0 {
                    leanh::lean_ctor_set(v___x_991_, 2, v___x_1006_);
                    v___x_1008_ = v___x_991_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1011_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_key_987_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_value_988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1011_, 2, v___x_1006_);
                    v___x_1008_ = v_reuseFailAlloc_1011_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1009_ = lean_array_uset(v_x_985_, v___x_1005_, v___x_1008_);
                v_x_985_ = v___x_1009_;
                v_x_986_ = v_tail_989_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(
    mut v_i_1013_: *mut leanh::LeanObject,
    mut v_source_1014_: *mut leanh::LeanObject,
    mut v_target_1015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: u8 = 0;
    let mut v_es_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1016_ = lean_array_get_size(v_source_1014_);
                v___x_1017_ = lean_nat_dec_lt(v_i_1013_, v___x_1016_);
                if v___x_1017_ == 0 {
                    leanh::lean_dec_ref(v_source_1014_);
                    leanh::lean_dec(v_i_1013_);
                    return v_target_1015_;
                } else {
                    v_es_1018_ = lean_array_fget(v_source_1014_, v_i_1013_);
                    v___x_1019_ = leanh::lean_box(0);
                    v_source_1020_ = lean_array_fset(v_source_1014_, v_i_1013_, v___x_1019_);
                    v_target_1021_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_target_1015_, v_es_1018_);
                    v___x_1022_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1023_ = lean_nat_add(v_i_1013_, v___x_1022_);
                    leanh::lean_dec(v_i_1013_);
                    v_i_1013_ = v___x_1023_;
                    v_source_1014_ = v_source_1020_;
                    v_target_1015_ = v_target_1021_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(
    mut v_data_1025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1026_ = lean_array_get_size(v_data_1025_);
    v___x_1027_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1028_ = lean_nat_mul(v___x_1026_, v___x_1027_);
    v___x_1029_ = leanh::lean_unsigned_to_nat(0);
    v___x_1030_ = leanh::lean_box(0);
    v___x_1031_ = lean_mk_array(v_nbuckets_1028_, v___x_1030_);
    v___x_1032_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v___x_1029_, v_data_1025_, v___x_1031_);
    return v___x_1032_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(
    mut v_a_1033_: *mut leanh::LeanObject,
    mut v_x_1034_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1035_: u8 = 0;
    let mut v_key_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1034_) == 0 {
                    v___x_1035_ = 0;
                    return v___x_1035_;
                } else {
                    v_key_1036_ = leanh::lean_ctor_get(v_x_1034_, 0);
                    v_tail_1037_ = leanh::lean_ctor_get(v_x_1034_, 2);
                    v___x_1038_ = l_Lean_ExprStructEq_beq(v_key_1036_, v_a_1033_);
                    if v___x_1038_ == 0 {
                        v_x_1034_ = v_tail_1037_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1038_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg___boxed(
    mut v_a_1040_: *mut leanh::LeanObject,
    mut v_x_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1042_: u8 = 0;
    let mut v_r_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1042_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_a_1040_, v_x_1041_);
    leanh::lean_dec(v_x_1041_);
    leanh::lean_dec_ref(v_a_1040_);
    v_r_1043_ = leanh::lean_box((v_res_1042_) as usize);
    return v_r_1043_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13___redArg(
    mut v_a_1044_: *mut leanh::LeanObject,
    mut v_b_1045_: *mut leanh::LeanObject,
    mut v_x_1046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v___x_1053_: u8 = 0;
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1046_) == 0 {
                    leanh::lean_dec(v_b_1045_);
                    leanh::lean_dec_ref(v_a_1044_);
                    return v_x_1046_;
                } else {
                    v_key_1047_ = leanh::lean_ctor_get(v_x_1046_, 0);
                    v_value_1048_ = leanh::lean_ctor_get(v_x_1046_, 1);
                    v_tail_1049_ = leanh::lean_ctor_get(v_x_1046_, 2);
                    v_isSharedCheck_1061_ = (!leanh::lean_is_exclusive(v_x_1046_)) as u8;
                    if v_isSharedCheck_1061_ == 0 {
                        v___x_1051_ = v_x_1046_;
                        v_isShared_1052_ = v_isSharedCheck_1061_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1049_);
                        leanh::lean_inc(v_value_1048_);
                        leanh::lean_inc(v_key_1047_);
                        leanh::lean_dec(v_x_1046_);
                        v___x_1051_ = leanh::lean_box(0);
                        v_isShared_1052_ = v_isSharedCheck_1061_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1053_ = l_Lean_ExprStructEq_beq(v_key_1047_, v_a_1044_);
                if v___x_1053_ == 0 {
                    v___x_1054_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13___redArg(v_a_1044_, v_b_1045_, v_tail_1049_);
                    if v_isShared_1052_ == 0 {
                        leanh::lean_ctor_set(v___x_1051_, 2, v___x_1054_);
                        v___x_1056_ = v___x_1051_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1057_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_key_1047_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_value_1048_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1057_, 2, v___x_1054_);
                        v___x_1056_ = v_reuseFailAlloc_1057_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_1048_);
                    leanh::lean_dec(v_key_1047_);
                    if v_isShared_1052_ == 0 {
                        leanh::lean_ctor_set(v___x_1051_, 1, v_b_1045_);
                        leanh::lean_ctor_set(v___x_1051_, 0, v_a_1044_);
                        v___x_1059_ = v___x_1051_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1060_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1044_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_b_1045_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_tail_1049_);
                        v___x_1059_ = v_reuseFailAlloc_1060_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1056_;
            }
            3 => {
                return v___x_1059_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(
    mut v_m_1062_: *mut leanh::LeanObject,
    mut v_a_1063_: *mut leanh::LeanObject,
    mut v_b_1064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1069_: u8 = 0;
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: u64 = 0;
    let mut v___x_1072_: u64 = 0;
    let mut v___x_1073_: u64 = 0;
    let mut v_fold_1074_: u64 = 0;
    let mut v___x_1075_: u64 = 0;
    let mut v___x_1076_: u64 = 0;
    let mut v___x_1077_: u64 = 0;
    let mut v___x_1078_: usize = 0;
    let mut v___x_1079_: usize = 0;
    let mut v___x_1080_: usize = 0;
    let mut v___x_1081_: usize = 0;
    let mut v___x_1082_: usize = 0;
    let mut v_bkt_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: u8 = 0;
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: u8 = 0;
    let mut v_val_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1109_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1065_ = leanh::lean_ctor_get(v_m_1062_, 0);
                v_buckets_1066_ = leanh::lean_ctor_get(v_m_1062_, 1);
                v_isSharedCheck_1109_ = (!leanh::lean_is_exclusive(v_m_1062_)) as u8;
                if v_isSharedCheck_1109_ == 0 {
                    v___x_1068_ = v_m_1062_;
                    v_isShared_1069_ = v_isSharedCheck_1109_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1066_);
                    leanh::lean_inc(v_size_1065_);
                    leanh::lean_dec(v_m_1062_);
                    v___x_1068_ = leanh::lean_box(0);
                    v_isShared_1069_ = v_isSharedCheck_1109_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1070_ = lean_array_get_size(v_buckets_1066_);
                v___x_1071_ = l_Lean_ExprStructEq_hash(v_a_1063_);
                v___x_1072_ = 32u64;
                v___x_1073_ = lean_uint64_shift_right(v___x_1071_, v___x_1072_);
                v_fold_1074_ = lean_uint64_xor(v___x_1071_, v___x_1073_);
                v___x_1075_ = 16u64;
                v___x_1076_ = lean_uint64_shift_right(v_fold_1074_, v___x_1075_);
                v___x_1077_ = lean_uint64_xor(v_fold_1074_, v___x_1076_);
                v___x_1078_ = lean_uint64_to_usize(v___x_1077_);
                v___x_1079_ = lean_usize_of_nat(v___x_1070_);
                v___x_1080_ = 1usize;
                v___x_1081_ = lean_usize_sub(v___x_1079_, v___x_1080_);
                v___x_1082_ = lean_usize_land(v___x_1078_, v___x_1081_);
                v_bkt_1083_ = lean_array_uget_borrowed(v_buckets_1066_, v___x_1082_);
                v___x_1084_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_a_1063_, v_bkt_1083_);
                if v___x_1084_ == 0 {
                    v___x_1085_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1086_ = lean_nat_add(v_size_1065_, v___x_1085_);
                    leanh::lean_dec(v_size_1065_);
                    leanh::lean_inc(v_bkt_1083_);
                    v___x_1087_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1087_, 0, v_a_1063_);
                    leanh::lean_ctor_set(v___x_1087_, 1, v_b_1064_);
                    leanh::lean_ctor_set(v___x_1087_, 2, v_bkt_1083_);
                    v_buckets_x27_1088_ =
                        lean_array_uset(v_buckets_1066_, v___x_1082_, v___x_1087_);
                    v___x_1089_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1090_ = lean_nat_mul(v_size_x27_1086_, v___x_1089_);
                    v___x_1091_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1092_ = lean_nat_div(v___x_1090_, v___x_1091_);
                    leanh::lean_dec(v___x_1090_);
                    v___x_1093_ = lean_array_get_size(v_buckets_x27_1088_);
                    v___x_1094_ = lean_nat_dec_le(v___x_1092_, v___x_1093_);
                    leanh::lean_dec(v___x_1092_);
                    if v___x_1094_ == 0 {
                        v_val_1095_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(v_buckets_x27_1088_);
                        if v_isShared_1069_ == 0 {
                            leanh::lean_ctor_set(v___x_1068_, 1, v_val_1095_);
                            leanh::lean_ctor_set(v___x_1068_, 0, v_size_x27_1086_);
                            v___x_1097_ = v___x_1068_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1098_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1098_,
                                0,
                                v_size_x27_1086_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_val_1095_);
                            v___x_1097_ = v_reuseFailAlloc_1098_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1069_ == 0 {
                            leanh::lean_ctor_set(v___x_1068_, 1, v_buckets_x27_1088_);
                            leanh::lean_ctor_set(v___x_1068_, 0, v_size_x27_1086_);
                            v___x_1100_ = v___x_1068_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1101_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1101_,
                                0,
                                v_size_x27_1086_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1101_,
                                1,
                                v_buckets_x27_1088_,
                            );
                            v___x_1100_ = v_reuseFailAlloc_1101_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_1083_);
                    v___x_1102_ = leanh::lean_box(0);
                    v_buckets_x27_1103_ =
                        lean_array_uset(v_buckets_1066_, v___x_1082_, v___x_1102_);
                    v___x_1104_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13___redArg(v_a_1063_, v_b_1064_, v_bkt_1083_);
                    v___x_1105_ = lean_array_uset(v_buckets_x27_1103_, v___x_1082_, v___x_1104_);
                    if v_isShared_1069_ == 0 {
                        leanh::lean_ctor_set(v___x_1068_, 1, v___x_1105_);
                        v___x_1107_ = v___x_1068_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1108_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_size_1065_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1105_);
                        v___x_1107_ = v_reuseFailAlloc_1108_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1097_;
            }
            3 => {
                return v___x_1100_;
            }
            4 => {
                return v___x_1107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2(
    mut v_a_1110_: *mut leanh::LeanObject,
    mut v_e_1111_: *mut leanh::LeanObject,
    mut v_a_1112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1114_ = lean_st_ref_take(v_a_1110_);
    v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v___x_1114_, v_e_1111_, v_a_1112_);
    v___x_1116_ = lean_st_ref_set(v_a_1110_, v___x_1115_);
    v___x_1117_ = leanh::lean_box(0);
    return v___x_1117_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2___boxed(
    mut v_a_1118_: *mut leanh::LeanObject,
    mut v_e_1119_: *mut leanh::LeanObject,
    mut v_a_1120_: *mut leanh::LeanObject,
    mut v___y_1121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1122_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2(v_a_1118_, v_e_1119_, v_a_1120_);
    leanh::lean_dec(v_a_1118_);
    return v_res_1122_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(
    mut v_00_u03b1_1123_: *mut leanh::LeanObject,
    mut v_x_1124_: *mut leanh::LeanObject,
    mut v___y_1125_: *mut leanh::LeanObject,
    mut v___y_1126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ = leanh::lean_apply_1(v_x_1124_, leanh::lean_box(0));
    v___x_1129_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1129_, 0, v___x_1128_);
    return v___x_1129_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0___boxed(
    mut v_00_u03b1_1130_: *mut leanh::LeanObject,
    mut v_x_1131_: *mut leanh::LeanObject,
    mut v___y_1132_: *mut leanh::LeanObject,
    mut v___y_1133_: *mut leanh::LeanObject,
    mut v___y_1134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1135_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(v_00_u03b1_1130_, v_x_1131_, v___y_1132_, v___y_1133_);
    leanh::lean_dec(v___y_1133_);
    leanh::lean_dec_ref(v___y_1132_);
    return v_res_1135_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1141_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1142_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1142_, 0, v___x_1141_);
    return v___x_1142_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1143_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3);
    v___x_1144_ = l_Lean_MessageData_ofFormat(v___x_1143_);
    return v___x_1144_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1145_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4);
    v___x_1146_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__2;
    v___x_1147_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1147_, 0, v___x_1146_);
    leanh::lean_ctor_set(v___x_1147_, 1, v___x_1145_);
    return v___x_1147_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(
    mut v_ref_1148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5);
    v___x_1151_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1151_, 0, v_ref_1148_);
    leanh::lean_ctor_set(v___x_1151_, 1, v___x_1150_);
    v___x_1152_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1152_, 0, v___x_1151_);
    return v___x_1152_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___boxed(
    mut v_ref_1153_: *mut leanh::LeanObject,
    mut v___y_1154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_1153_);
    return v_res_1155_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1156_ = leanh::lean_box(0);
    v___x_1157_ = l_Lean_interruptExceptionId;
    v___x_1158_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1158_, 0, v___x_1157_);
    leanh::lean_ctor_set(v___x_1158_, 1, v___x_1156_);
    return v___x_1158_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1160_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0);
    v___x_1161_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1161_, 0, v___x_1160_);
    return v___x_1161_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___boxed(
    mut v___y_1162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1163_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
    return v_res_1163_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(
    mut v_x_1164_: *mut leanh::LeanObject,
    mut v___y_1165_: *mut leanh::LeanObject,
    mut v___y_1166_: *mut leanh::LeanObject,
    mut v___y_1167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1174_: u8 = 0;
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut v___y_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1184_: u8 = 0;
    let mut v___y_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1194_: u8 = 0;
    let mut v___y_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1212_: u8 = 0;
    let mut v_cancelTk_x3f_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1214_: u8 = 0;
    let mut v_inheritedTraceOptions_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: u8 = 0;
    let mut v___x_1219_: u8 = 0;
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: u8 = 0;
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1227_: u8 = 0;
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1200_ = leanh::lean_ctor_get(v___y_1166_, 0);
                v_fileMap_1201_ = leanh::lean_ctor_get(v___y_1166_, 1);
                v_options_1202_ = leanh::lean_ctor_get(v___y_1166_, 2);
                v_currRecDepth_1203_ = leanh::lean_ctor_get(v___y_1166_, 3);
                v_maxRecDepth_1204_ = leanh::lean_ctor_get(v___y_1166_, 4);
                v_ref_1205_ = leanh::lean_ctor_get(v___y_1166_, 5);
                v_currNamespace_1206_ = leanh::lean_ctor_get(v___y_1166_, 6);
                v_openDecls_1207_ = leanh::lean_ctor_get(v___y_1166_, 7);
                v_initHeartbeats_1208_ = leanh::lean_ctor_get(v___y_1166_, 8);
                v_maxHeartbeats_1209_ = leanh::lean_ctor_get(v___y_1166_, 9);
                v_quotContext_1210_ = leanh::lean_ctor_get(v___y_1166_, 10);
                v_currMacroScope_1211_ = leanh::lean_ctor_get(v___y_1166_, 11);
                v_diag_1212_ = leanh::lean_ctor_get_uint8(
                    v___y_1166_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1213_ = leanh::lean_ctor_get(v___y_1166_, 12);
                v_suppressElabErrors_1214_ = leanh::lean_ctor_get_uint8(
                    v___y_1166_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1215_ = leanh::lean_ctor_get(v___y_1166_, 13);
                if leanh::lean_obj_tag(v_cancelTk_x3f_1213_) == 1 {
                    v_val_1221_ = leanh::lean_ctor_get(v_cancelTk_x3f_1213_, 0);
                    v___x_1222_ = l_IO_CancelToken_isSet(v_val_1221_);
                    if v___x_1222_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_x_1164_);
                        v___x_1223_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
                        v_a_1224_ = leanh::lean_ctor_get(v___x_1223_, 0);
                        v_isSharedCheck_1231_ =
                            (!leanh::lean_is_exclusive(v___x_1223_)) as u8;
                        if v_isSharedCheck_1231_ == 0 {
                            v___x_1226_ = v___x_1223_;
                            v_isShared_1227_ = v_isSharedCheck_1231_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1224_);
                            leanh::lean_dec(v___x_1223_);
                            v___x_1226_ = leanh::lean_box(0);
                            v_isShared_1227_ = v_isSharedCheck_1231_;
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
                if leanh::lean_obj_tag(v___y_1170_) == 0 {
                    return v___y_1170_;
                } else {
                    v_a_1171_ = leanh::lean_ctor_get(v___y_1170_, 0);
                    v_isSharedCheck_1178_ = (!leanh::lean_is_exclusive(v___y_1170_)) as u8;
                    if v_isSharedCheck_1178_ == 0 {
                        v___x_1173_ = v___y_1170_;
                        v_isShared_1174_ = v_isSharedCheck_1178_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1171_);
                        leanh::lean_dec(v___y_1170_);
                        v___x_1173_ = leanh::lean_box(0);
                        v_isShared_1174_ = v_isSharedCheck_1178_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1174_ == 0 {
                    v___x_1176_ = v___x_1173_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1177_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
                    v___x_1176_ = v_reuseFailAlloc_1177_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1176_;
            }
            4 => {
                v___x_1196_ = leanh::lean_unsigned_to_nat(1);
                v___x_1197_ = lean_nat_add(v___y_1181_, v___x_1196_);
                leanh::lean_inc_ref(v___y_1195_);
                leanh::lean_inc(v___y_1182_);
                leanh::lean_inc(v___y_1185_);
                leanh::lean_inc(v___y_1186_);
                leanh::lean_inc(v___y_1189_);
                leanh::lean_inc(v___y_1191_);
                leanh::lean_inc(v___y_1180_);
                leanh::lean_inc(v___y_1193_);
                leanh::lean_inc(v___y_1188_);
                leanh::lean_inc_ref(v___y_1183_);
                leanh::lean_inc_ref(v___y_1192_);
                leanh::lean_inc_ref(v___y_1187_);
                v___x_1198_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_1198_, 0, v___y_1187_);
                leanh::lean_ctor_set(v___x_1198_, 1, v___y_1192_);
                leanh::lean_ctor_set(v___x_1198_, 2, v___y_1183_);
                leanh::lean_ctor_set(v___x_1198_, 3, v___x_1197_);
                leanh::lean_ctor_set(v___x_1198_, 4, v___y_1188_);
                leanh::lean_ctor_set(v___x_1198_, 5, v___y_1190_);
                leanh::lean_ctor_set(v___x_1198_, 6, v___y_1193_);
                leanh::lean_ctor_set(v___x_1198_, 7, v___y_1180_);
                leanh::lean_ctor_set(v___x_1198_, 8, v___y_1191_);
                leanh::lean_ctor_set(v___x_1198_, 9, v___y_1189_);
                leanh::lean_ctor_set(v___x_1198_, 10, v___y_1186_);
                leanh::lean_ctor_set(v___x_1198_, 11, v___y_1185_);
                leanh::lean_ctor_set(v___x_1198_, 12, v___y_1182_);
                leanh::lean_ctor_set(v___x_1198_, 13, v___y_1195_);
                leanh::lean_ctor_set_uint8(
                    v___x_1198_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___y_1184_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1198_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_1194_,
                );
                leanh::lean_inc(v___y_1167_);
                leanh::lean_inc(v___y_1165_);
                v___x_1199_ = leanh::lean_apply_4(
                    v_x_1164_,
                    v___y_1165_,
                    v___x_1198_,
                    v___y_1167_,
                    leanh::lean_box(0),
                );
                v___y_1170_ = v___x_1199_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1217_ = leanh::lean_unsigned_to_nat(0);
                v___x_1218_ = lean_nat_dec_eq(v_maxRecDepth_1204_, v___x_1217_);
                if v___x_1218_ == 0 {
                    v___x_1219_ = lean_nat_dec_eq(v_currRecDepth_1203_, v_maxRecDepth_1204_);
                    if v___x_1219_ == 0 {
                        leanh::lean_inc(v_ref_1205_);
                        v___y_1180_ = v_openDecls_1207_;
                        v___y_1181_ = v_currRecDepth_1203_;
                        v___y_1182_ = v_cancelTk_x3f_1213_;
                        v___y_1183_ = v_options_1202_;
                        v___y_1184_ = v_diag_1212_;
                        v___y_1185_ = v_currMacroScope_1211_;
                        v___y_1186_ = v_quotContext_1210_;
                        v___y_1187_ = v_fileName_1200_;
                        v___y_1188_ = v_maxRecDepth_1204_;
                        v___y_1189_ = v_maxHeartbeats_1209_;
                        v___y_1190_ = v_ref_1205_;
                        v___y_1191_ = v_initHeartbeats_1208_;
                        v___y_1192_ = v_fileMap_1201_;
                        v___y_1193_ = v_currNamespace_1206_;
                        v___y_1194_ = v_suppressElabErrors_1214_;
                        v___y_1195_ = v_inheritedTraceOptions_1215_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_x_1164_);
                        leanh::lean_inc(v_ref_1205_);
                        v___x_1220_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_1205_);
                        v___y_1170_ = v___x_1220_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_ref_1205_);
                    v___y_1180_ = v_openDecls_1207_;
                    v___y_1181_ = v_currRecDepth_1203_;
                    v___y_1182_ = v_cancelTk_x3f_1213_;
                    v___y_1183_ = v_options_1202_;
                    v___y_1184_ = v_diag_1212_;
                    v___y_1185_ = v_currMacroScope_1211_;
                    v___y_1186_ = v_quotContext_1210_;
                    v___y_1187_ = v_fileName_1200_;
                    v___y_1188_ = v_maxRecDepth_1204_;
                    v___y_1189_ = v_maxHeartbeats_1209_;
                    v___y_1190_ = v_ref_1205_;
                    v___y_1191_ = v_initHeartbeats_1208_;
                    v___y_1192_ = v_fileMap_1201_;
                    v___y_1193_ = v_currNamespace_1206_;
                    v___y_1194_ = v_suppressElabErrors_1214_;
                    v___y_1195_ = v_inheritedTraceOptions_1215_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v_isShared_1227_ == 0 {
                    v___x_1229_ = v___x_1226_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1230_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
                    v___x_1229_ = v_reuseFailAlloc_1230_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1229_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg___boxed(
    mut v_x_1232_: *mut leanh::LeanObject,
    mut v___y_1233_: *mut leanh::LeanObject,
    mut v___y_1234_: *mut leanh::LeanObject,
    mut v___y_1235_: *mut leanh::LeanObject,
    mut v___y_1236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1237_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v_x_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
    leanh::lean_dec(v___y_1235_);
    leanh::lean_dec_ref(v___y_1234_);
    leanh::lean_dec(v___y_1233_);
    return v_res_1237_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(
    mut v_pre_1239_: *mut leanh::LeanObject,
    mut v_post_1240_: *mut leanh::LeanObject,
    mut v_sz_1241_: usize,
    mut v_i_1242_: usize,
    mut v_bs_1243_: *mut leanh::LeanObject,
    mut v___y_1244_: *mut leanh::LeanObject,
    mut v___y_1245_: *mut leanh::LeanObject,
    mut v___y_1246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1248_: u8 = 0;
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: usize = 0;
    let mut v___x_1256_: usize = 0;
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1262_: u8 = 0;
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1266_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1248_ = lean_usize_dec_lt(v_i_1242_, v_sz_1241_);
                if v___x_1248_ == 0 {
                    leanh::lean_dec_ref(v_post_1240_);
                    leanh::lean_dec_ref(v_pre_1239_);
                    v___x_1249_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1249_, 0, v_bs_1243_);
                    return v___x_1249_;
                } else {
                    v_v_1250_ = lean_array_uget_borrowed(v_bs_1243_, v_i_1242_);
                    leanh::lean_inc(v_v_1250_);
                    leanh::lean_inc_ref(v_post_1240_);
                    leanh::lean_inc_ref(v_pre_1239_);
                    v___x_1251_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1239_, v_post_1240_, v_v_1250_, v___y_1244_, v___y_1245_, v___y_1246_);
                    if leanh::lean_obj_tag(v___x_1251_) == 0 {
                        v_a_1252_ = leanh::lean_ctor_get(v___x_1251_, 0);
                        leanh::lean_inc(v_a_1252_);
                        leanh::lean_dec_ref_known(v___x_1251_, 1);
                        v___x_1253_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1254_ = lean_array_uset(v_bs_1243_, v_i_1242_, v___x_1253_);
                        v___x_1255_ = 1usize;
                        v___x_1256_ = lean_usize_add(v_i_1242_, v___x_1255_);
                        v___x_1257_ = lean_array_uset(v_bs_x27_1254_, v_i_1242_, v_a_1252_);
                        v_i_1242_ = v___x_1256_;
                        v_bs_1243_ = v___x_1257_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_1243_);
                        leanh::lean_dec_ref(v_post_1240_);
                        leanh::lean_dec_ref(v_pre_1239_);
                        v_a_1259_ = leanh::lean_ctor_get(v___x_1251_, 0);
                        v_isSharedCheck_1266_ =
                            (!leanh::lean_is_exclusive(v___x_1251_)) as u8;
                        if v_isSharedCheck_1266_ == 0 {
                            v___x_1261_ = v___x_1251_;
                            v_isShared_1262_ = v_isSharedCheck_1266_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1259_);
                            leanh::lean_dec(v___x_1251_);
                            v___x_1261_ = leanh::lean_box(0);
                            v_isShared_1262_ = v_isSharedCheck_1266_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1262_ == 0 {
                    v___x_1264_ = v___x_1261_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1265_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
                    v___x_1264_ = v_reuseFailAlloc_1265_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1264_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(
    mut v_pre_1267_: *mut leanh::LeanObject,
    mut v_post_1268_: *mut leanh::LeanObject,
    mut v_x_1269_: *mut leanh::LeanObject,
    mut v_x_1270_: *mut leanh::LeanObject,
    mut v_x_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
    mut v___y_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1284_: usize = 0;
    let mut v___x_1285_: usize = 0;
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1293_: u8 = 0;
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1269_) == 5 {
                    v_fn_1276_ = leanh::lean_ctor_get(v_x_1269_, 0);
                    leanh::lean_inc_ref(v_fn_1276_);
                    v_arg_1277_ = leanh::lean_ctor_get(v_x_1269_, 1);
                    leanh::lean_inc_ref(v_arg_1277_);
                    leanh::lean_dec_ref_known(v_x_1269_, 2);
                    v___x_1278_ = lean_array_set(v_x_1270_, v_x_1271_, v_arg_1277_);
                    v___x_1279_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1280_ = lean_nat_sub(v_x_1271_, v___x_1279_);
                    leanh::lean_dec(v_x_1271_);
                    v_x_1269_ = v_fn_1276_;
                    v_x_1270_ = v___x_1278_;
                    v_x_1271_ = v___x_1280_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_1271_);
                    leanh::lean_inc_ref(v_post_1268_);
                    leanh::lean_inc_ref(v_pre_1267_);
                    v___x_1282_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1267_, v_post_1268_, v_x_1269_, v___y_1272_, v___y_1273_, v___y_1274_);
                    if leanh::lean_obj_tag(v___x_1282_) == 0 {
                        v_a_1283_ = leanh::lean_ctor_get(v___x_1282_, 0);
                        leanh::lean_inc(v_a_1283_);
                        leanh::lean_dec_ref_known(v___x_1282_, 1);
                        v_sz_1284_ = lean_array_size(v_x_1270_);
                        v___x_1285_ = 0usize;
                        leanh::lean_inc_ref(v_post_1268_);
                        leanh::lean_inc_ref(v_pre_1267_);
                        v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(v_pre_1267_, v_post_1268_, v_sz_1284_, v___x_1285_, v_x_1270_, v___y_1272_, v___y_1273_, v___y_1274_);
                        if leanh::lean_obj_tag(v___x_1286_) == 0 {
                            v_a_1287_ = leanh::lean_ctor_get(v___x_1286_, 0);
                            leanh::lean_inc(v_a_1287_);
                            leanh::lean_dec_ref_known(v___x_1286_, 1);
                            v___x_1288_ = l_Lean_mkAppN(v_a_1283_, v_a_1287_);
                            leanh::lean_dec(v_a_1287_);
                            v___x_1289_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1267_, v_post_1268_, v___x_1288_, v___y_1272_, v___y_1273_, v___y_1274_);
                            return v___x_1289_;
                        } else {
                            leanh::lean_dec(v_a_1283_);
                            leanh::lean_dec_ref(v_post_1268_);
                            leanh::lean_dec_ref(v_pre_1267_);
                            v_a_1290_ = leanh::lean_ctor_get(v___x_1286_, 0);
                            v_isSharedCheck_1297_ =
                                (!leanh::lean_is_exclusive(v___x_1286_)) as u8;
                            if v_isSharedCheck_1297_ == 0 {
                                v___x_1292_ = v___x_1286_;
                                v_isShared_1293_ = v_isSharedCheck_1297_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1290_);
                                leanh::lean_dec(v___x_1286_);
                                v___x_1292_ = leanh::lean_box(0);
                                v_isShared_1293_ = v_isSharedCheck_1297_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_1270_);
                        leanh::lean_dec_ref(v_post_1268_);
                        leanh::lean_dec_ref(v_pre_1267_);
                        return v___x_1282_;
                    }
                }
            }
            1 => {
                if v_isShared_1293_ == 0 {
                    v___x_1295_ = v___x_1292_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1296_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
                    v___x_1295_ = v_reuseFailAlloc_1296_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1295_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1(
    mut v___x_1298_: *mut leanh::LeanObject,
    mut v_pre_1299_: *mut leanh::LeanObject,
    mut v_e_1300_: *mut leanh::LeanObject,
    mut v_post_1301_: *mut leanh::LeanObject,
    mut v___y_1302_: *mut leanh::LeanObject,
    mut v___y_1303_: *mut leanh::LeanObject,
    mut v___y_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1310_: u8 = 0;
    let mut v___y_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1314_: u8 = 0;
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: usize = 0;
    let mut v___x_1318_: usize = 0;
    let mut v___x_1319_: u8 = 0;
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1327_: u8 = 0;
    let mut v___y_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1329_: u8 = 0;
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1340_: u8 = 0;
    let mut v___y_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1342_: u8 = 0;
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: u8 = 0;
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1354_: u8 = 0;
    let mut v___y_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1360_: u8 = 0;
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: usize = 0;
    let mut v___x_1366_: usize = 0;
    let mut v___x_1367_: u8 = 0;
    let mut v___x_1368_: usize = 0;
    let mut v___x_1369_: usize = 0;
    let mut v___x_1370_: u8 = 0;
    let mut v_binderName_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1374_: u8 = 0;
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: usize = 0;
    let mut v___x_1380_: usize = 0;
    let mut v___x_1381_: u8 = 0;
    let mut v___x_1382_: usize = 0;
    let mut v___x_1383_: usize = 0;
    let mut v___x_1384_: u8 = 0;
    let mut v_declName_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1389_: u8 = 0;
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: usize = 0;
    let mut v___x_1397_: usize = 0;
    let mut v___x_1398_: u8 = 0;
    let mut v___x_1399_: usize = 0;
    let mut v___x_1400_: usize = 0;
    let mut v___x_1401_: u8 = 0;
    let mut v_dummy_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: usize = 0;
    let mut v___x_1413_: usize = 0;
    let mut v___x_1414_: u8 = 0;
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: usize = 0;
    let mut v___x_1424_: usize = 0;
    let mut v___x_1425_: u8 = 0;
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1440_: u8 = 0;
    let mut v_a_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1444_: u8 = 0;
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1448_: u8 = 0;
    let mut v_a_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1452_: u8 = 0;
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1456_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1349_ = l_Lean_Core_checkSystem(v___x_1298_, v___y_1303_, v___y_1304_);
                if leanh::lean_obj_tag(v___x_1349_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1349_, 1);
                    leanh::lean_inc_ref(v_pre_1299_);
                    leanh::lean_inc(v___y_1304_);
                    leanh::lean_inc_ref(v___y_1303_);
                    leanh::lean_inc_ref(v_e_1300_);
                    v___x_1350_ = leanh::lean_apply_4(
                        v_pre_1299_,
                        v_e_1300_,
                        v___y_1303_,
                        v___y_1304_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1350_) == 0 {
                        v_a_1351_ = leanh::lean_ctor_get(v___x_1350_, 0);
                        v_isSharedCheck_1440_ =
                            (!leanh::lean_is_exclusive(v___x_1350_)) as u8;
                        if v_isSharedCheck_1440_ == 0 {
                            v___x_1353_ = v___x_1350_;
                            v_isShared_1354_ = v_isSharedCheck_1440_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1351_);
                            leanh::lean_dec(v___x_1350_);
                            v___x_1353_ = leanh::lean_box(0);
                            v_isShared_1354_ = v_isSharedCheck_1440_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_post_1301_);
                        leanh::lean_dec_ref(v_e_1300_);
                        leanh::lean_dec_ref(v_pre_1299_);
                        v_a_1441_ = leanh::lean_ctor_get(v___x_1350_, 0);
                        v_isSharedCheck_1448_ =
                            (!leanh::lean_is_exclusive(v___x_1350_)) as u8;
                        if v_isSharedCheck_1448_ == 0 {
                            v___x_1443_ = v___x_1350_;
                            v_isShared_1444_ = v_isSharedCheck_1448_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1441_);
                            leanh::lean_dec(v___x_1350_);
                            v___x_1443_ = leanh::lean_box(0);
                            v_isShared_1444_ = v_isSharedCheck_1448_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_post_1301_);
                    leanh::lean_dec_ref(v_e_1300_);
                    leanh::lean_dec_ref(v_pre_1299_);
                    v_a_1449_ = leanh::lean_ctor_get(v___x_1349_, 0);
                    v_isSharedCheck_1456_ = (!leanh::lean_is_exclusive(v___x_1349_)) as u8;
                    if v_isSharedCheck_1456_ == 0 {
                        v___x_1451_ = v___x_1349_;
                        v_isShared_1452_ = v_isSharedCheck_1456_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1449_);
                        leanh::lean_dec(v___x_1349_);
                        v___x_1451_ = leanh::lean_box(0);
                        v_isShared_1452_ = v_isSharedCheck_1456_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1314_ == 0 {
                    leanh::lean_dec_ref(v___y_1313_);
                    leanh::lean_dec_ref(v___y_1308_);
                    v___x_1315_ = l_Lean_Expr_letE___override(
                        v___y_1307_,
                        v___y_1312_,
                        v___y_1311_,
                        v___y_1309_,
                        v___y_1310_,
                    );
                    v___x_1316_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v___x_1315_, v___y_1302_, v___y_1303_, v___y_1304_);
                    return v___x_1316_;
                } else {
                    v___x_1317_ = lean_ptr_addr(v___y_1313_);
                    leanh::lean_dec_ref(v___y_1313_);
                    v___x_1318_ = lean_ptr_addr(v___y_1309_);
                    v___x_1319_ = lean_usize_dec_eq(v___x_1317_, v___x_1318_);
                    if v___x_1319_ == 0 {
                        leanh::lean_dec_ref(v___y_1308_);
                        v___x_1320_ = l_Lean_Expr_letE___override(
                            v___y_1307_,
                            v___y_1312_,
                            v___y_1311_,
                            v___y_1309_,
                            v___y_1310_,
                        );
                        v___x_1321_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v___x_1320_, v___y_1302_, v___y_1303_, v___y_1304_);
                        return v___x_1321_;
                    } else {
                        leanh::lean_dec_ref(v___y_1312_);
                        leanh::lean_dec_ref(v___y_1311_);
                        leanh::lean_dec_ref(v___y_1309_);
                        leanh::lean_dec(v___y_1307_);
                        v___x_1322_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v___y_1308_, v___y_1302_, v___y_1303_, v___y_1304_);
                        return v___x_1322_;
                    }
                }
            }
            2 => {
                if v___y_1329_ == 0 {
                    leanh::lean_dec_ref(v___y_1325_);
                    v___x_1330_ = l_Lean_Expr_lam___override(
                        v___y_1328_,
                        v___y_1326_,
                        v___y_1324_,
                        v___y_1327_,
                    );
                    v___x_1331_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v___x_1330_, v___y_1302_, v___y_1303_, v___y_1304_);
                    return v___x_1331_;
                } else {
                    v___x_1332_ = l_Lean_instBEqBinderInfo_beq(v___y_1327_, v___y_1327_);
                    if v___x_1332_ == 0 {
                        leanh::lean_dec_ref(v___y_1325_);
                        v___x_1333_ = l_Lean_Expr_lam___override(
                            v___y_1328_,
                            v___y_1326_,
                            v___y_1324_,
                            v___y_1327_,
                        );
                        v___x_1334_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v___x_1333_, v___y_1302_, v___y_1303_, v___y_1304_);
                        return v___x_1334_;
                    } else {
                        leanh::lean_dec(v___y_1328_);
                        leanh::lean_dec_ref(v___y_1326_);
                        leanh::lean_dec_ref(v___y_1324_);
                        v___x_1335_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v___y_1325_, v___y_1302_, v___y_1303_, v___y_1304_);
                        return v___x_1335_;
                    }
                }
            }
            3 => {
                if v___y_1342_ == 0 {
                    leanh::lean_dec_ref(v___y_1338_);
                    v___x_1343_ = l_Lean_Expr_forallE___override(
                        v___y_1337_,
                        v___y_1341_,
                        v___y_1339_,
                        v___y_1340_,
                    );
                    v___x_1344_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v___x_1343_, v___y_1302_, v___y_1303_, v___y_1304_);
                    return v___x_1344_;
                } else {
                    v___x_1345_ = l_Lean_instBEqBinderInfo_beq(v___y_1340_, v___y_1340_);
                    if v___x_1345_ == 0 {
                        leanh::lean_dec_ref(v___y_1338_);
                        v___x_1346_ = l_Lean_Expr_forallE___override(
                            v___y_1337_,
                            v___y_1341_,
                            v___y_1339_,
                            v___y_1340_,
                        );
                        v___x_1347_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v___x_1346_, v___y_1302_, v___y_1303_, v___y_1304_);
                        return v___x_1347_;
                    } else {
                        leanh::lean_dec_ref(v___y_1341_);
                        leanh::lean_dec_ref(v___y_1339_);
                        leanh::lean_dec(v___y_1337_);
                        v___x_1348_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v___y_1338_, v___y_1302_, v___y_1303_, v___y_1304_);
                        return v___x_1348_;
                    }
                }
            }
            4 => match leanh::lean_obj_tag(v_a_1351_) {
                0 => {
                    leanh::lean_dec_ref(v_post_1301_);
                    leanh::lean_dec_ref(v_e_1300_);
                    leanh::lean_dec_ref(v_pre_1299_);
                    v_e_1430_ = leanh::lean_ctor_get(v_a_1351_, 0);
                    leanh::lean_inc_ref(v_e_1430_);
                    leanh::lean_dec_ref_known(v_a_1351_, 1);
                    if v_isShared_1354_ == 0 {
                        leanh::lean_ctor_set(v___x_1353_, 0, v_e_1430_);
                        v___x_1432_ = v___x_1353_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1433_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_e_1430_);
                        v___x_1432_ = v_reuseFailAlloc_1433_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_1353_);
                    leanh::lean_dec_ref(v_e_1300_);
                    v_e_1434_ = leanh::lean_ctor_get(v_a_1351_, 0);
                    leanh::lean_inc_ref(v_e_1434_);
                    leanh::lean_dec_ref_known(v_a_1351_, 1);
                    leanh::lean_inc_ref(v_post_1301_);
                    leanh::lean_inc_ref(v_pre_1299_);
                    v___x_1435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1299_, v_post_1301_, v_e_1434_, v___y_1302_, v___y_1303_, v___y_1304_);
                    if leanh::lean_obj_tag(v___x_1435_) == 0 {
                        v_a_1436_ = leanh::lean_ctor_get(v___x_1435_, 0);
                        leanh::lean_inc(v_a_1436_);
                        leanh::lean_dec_ref_known(v___x_1435_, 1);
                        v___x_1437_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v_a_1436_, v___y_1302_, v___y_1303_, v___y_1304_);
                        return v___x_1437_;
                    } else {
                        leanh::lean_dec_ref(v_post_1301_);
                        leanh::lean_dec_ref(v_pre_1299_);
                        return v___x_1435_;
                    }
                }
                _ => {
                    leanh::lean_del_object(v___x_1353_);
                    v_e_x3f_1438_ = leanh::lean_ctor_get(v_a_1351_, 0);
                    leanh::lean_inc(v_e_x3f_1438_);
                    leanh::lean_dec_ref_known(v_a_1351_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_1438_) == 0 {
                        v___y_1356_ = v_e_1300_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_1300_);
                        v_val_1439_ = leanh::lean_ctor_get(v_e_x3f_1438_, 0);
                        leanh::lean_inc(v_val_1439_);
                        leanh::lean_dec_ref_known(v_e_x3f_1438_, 1);
                        v___y_1356_ = v_val_1439_;
                        state = 5;
                        continue;
                    }
                }
            },
            5 => match leanh::lean_obj_tag(v___y_1356_) {
                7 => {
                    v_binderName_1357_ = leanh::lean_ctor_get(v___y_1356_, 0);
                    leanh::lean_inc(v_binderName_1357_);
                    v_binderType_1358_ = leanh::lean_ctor_get(v___y_1356_, 1);
                    v_body_1359_ = leanh::lean_ctor_get(v___y_1356_, 2);
                    v_binderInfo_1360_ = leanh::lean_ctor_get_uint8(
                        v___y_1356_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_binderType_1358_);
                    leanh::lean_inc_ref(v_post_1301_);
                    leanh::lean_inc_ref(v_pre_1299_);
                    v___x_1361_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1299_, v_post_1301_, v_binderType_1358_, v___y_1302_, v___y_1303_, v___y_1304_);
                    if leanh::lean_obj_tag(v___x_1361_) == 0 {
                        v_a_1362_ = leanh::lean_ctor_get(v___x_1361_, 0);
                        leanh::lean_inc(v_a_1362_);
                        leanh::lean_dec_ref_known(v___x_1361_, 1);
                        leanh::lean_inc_ref(v_body_1359_);
                        leanh::lean_inc_ref(v_post_1301_);
                        leanh::lean_inc_ref(v_pre_1299_);
                        v___x_1363_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1299_, v_post_1301_, v_body_1359_, v___y_1302_, v___y_1303_, v___y_1304_);
                        if leanh::lean_obj_tag(v___x_1363_) == 0 {
                            v_a_1364_ = leanh::lean_ctor_get(v___x_1363_, 0);
                            leanh::lean_inc(v_a_1364_);
                            leanh::lean_dec_ref_known(v___x_1363_, 1);
                            v___x_1365_ = lean_ptr_addr(v_binderType_1358_);
                            v___x_1366_ = lean_ptr_addr(v_a_1362_);
                            v___x_1367_ = lean_usize_dec_eq(v___x_1365_, v___x_1366_);
                            if v___x_1367_ == 0 {
                                v___y_1337_ = v_binderName_1357_;
                                v___y_1338_ = v___y_1356_;
                                v___y_1339_ = v_a_1364_;
                                v___y_1340_ = v_binderInfo_1360_;
                                v___y_1341_ = v_a_1362_;
                                v___y_1342_ = v___x_1367_;
                                state = 3;
                                continue;
                            } else {
                                v___x_1368_ = lean_ptr_addr(v_body_1359_);
                                v___x_1369_ = lean_ptr_addr(v_a_1364_);
                                v___x_1370_ = lean_usize_dec_eq(v___x_1368_, v___x_1369_);
                                v___y_1337_ = v_binderName_1357_;
                                v___y_1338_ = v___y_1356_;
                                v___y_1339_ = v_a_1364_;
                                v___y_1340_ = v_binderInfo_1360_;
                                v___y_1341_ = v_a_1362_;
                                v___y_1342_ = v___x_1370_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1362_);
                            leanh::lean_dec(v_binderName_1357_);
                            leanh::lean_dec_ref_known(v___y_1356_, 3);
                            leanh::lean_dec_ref(v_post_1301_);
                            leanh::lean_dec_ref(v_pre_1299_);
                            return v___x_1363_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_1356_, 3);
                        leanh::lean_dec(v_binderName_1357_);
                        leanh::lean_dec_ref(v_post_1301_);
                        leanh::lean_dec_ref(v_pre_1299_);
                        return v___x_1361_;
                    }
                }
                6 => {
                    v_binderName_1371_ = leanh::lean_ctor_get(v___y_1356_, 0);
                    leanh::lean_inc(v_binderName_1371_);
                    v_binderType_1372_ = leanh::lean_ctor_get(v___y_1356_, 1);
                    v_body_1373_ = leanh::lean_ctor_get(v___y_1356_, 2);
                    v_binderInfo_1374_ = leanh::lean_ctor_get_uint8(
                        v___y_1356_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_binderType_1372_);
                    leanh::lean_inc_ref(v_post_1301_);
                    leanh::lean_inc_ref(v_pre_1299_);
                    v___x_1375_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1299_, v_post_1301_, v_binderType_1372_, v___y_1302_, v___y_1303_, v___y_1304_);
                    if leanh::lean_obj_tag(v___x_1375_) == 0 {
                        v_a_1376_ = leanh::lean_ctor_get(v___x_1375_, 0);
                        leanh::lean_inc(v_a_1376_);
                        leanh::lean_dec_ref_known(v___x_1375_, 1);
                        leanh::lean_inc_ref(v_body_1373_);
                        leanh::lean_inc_ref(v_post_1301_);
                        leanh::lean_inc_ref(v_pre_1299_);
                        v___x_1377_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1299_, v_post_1301_, v_body_1373_, v___y_1302_, v___y_1303_, v___y_1304_);
                        if leanh::lean_obj_tag(v___x_1377_) == 0 {
                            v_a_1378_ = leanh::lean_ctor_get(v___x_1377_, 0);
                            leanh::lean_inc(v_a_1378_);
                            leanh::lean_dec_ref_known(v___x_1377_, 1);
                            v___x_1379_ = lean_ptr_addr(v_binderType_1372_);
                            v___x_1380_ = lean_ptr_addr(v_a_1376_);
                            v___x_1381_ = lean_usize_dec_eq(v___x_1379_, v___x_1380_);
                            if v___x_1381_ == 0 {
                                v___y_1324_ = v_a_1378_;
                                v___y_1325_ = v___y_1356_;
                                v___y_1326_ = v_a_1376_;
                                v___y_1327_ = v_binderInfo_1374_;
                                v___y_1328_ = v_binderName_1371_;
                                v___y_1329_ = v___x_1381_;
                                state = 2;
                                continue;
                            } else {
                                v___x_1382_ = lean_ptr_addr(v_body_1373_);
                                v___x_1383_ = lean_ptr_addr(v_a_1378_);
                                v___x_1384_ = lean_usize_dec_eq(v___x_1382_, v___x_1383_);
                                v___y_1324_ = v_a_1378_;
                                v___y_1325_ = v___y_1356_;
                                v___y_1326_ = v_a_1376_;
                                v___y_1327_ = v_binderInfo_1374_;
                                v___y_1328_ = v_binderName_1371_;
                                v___y_1329_ = v___x_1384_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1376_);
                            leanh::lean_dec_ref_known(v___y_1356_, 3);
                            leanh::lean_dec(v_binderName_1371_);
                            leanh::lean_dec_ref(v_post_1301_);
                            leanh::lean_dec_ref(v_pre_1299_);
                            return v___x_1377_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_1356_, 3);
                        leanh::lean_dec(v_binderName_1371_);
                        leanh::lean_dec_ref(v_post_1301_);
                        leanh::lean_dec_ref(v_pre_1299_);
                        return v___x_1375_;
                    }
                }
                8 => {
                    v_declName_1385_ = leanh::lean_ctor_get(v___y_1356_, 0);
                    leanh::lean_inc(v_declName_1385_);
                    v_type_1386_ = leanh::lean_ctor_get(v___y_1356_, 1);
                    v_value_1387_ = leanh::lean_ctor_get(v___y_1356_, 2);
                    v_body_1388_ = leanh::lean_ctor_get(v___y_1356_, 3);
                    leanh::lean_inc_ref(v_body_1388_);
                    v_nondep_1389_ = leanh::lean_ctor_get_uint8(
                        v___y_1356_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_type_1386_);
                    leanh::lean_inc_ref(v_post_1301_);
                    leanh::lean_inc_ref(v_pre_1299_);
                    v___x_1390_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1299_, v_post_1301_, v_type_1386_, v___y_1302_, v___y_1303_, v___y_1304_);
                    if leanh::lean_obj_tag(v___x_1390_) == 0 {
                        v_a_1391_ = leanh::lean_ctor_get(v___x_1390_, 0);
                        leanh::lean_inc(v_a_1391_);
                        leanh::lean_dec_ref_known(v___x_1390_, 1);
                        leanh::lean_inc_ref(v_value_1387_);
                        leanh::lean_inc_ref(v_post_1301_);
                        leanh::lean_inc_ref(v_pre_1299_);
                        v___x_1392_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1299_, v_post_1301_, v_value_1387_, v___y_1302_, v___y_1303_, v___y_1304_);
                        if leanh::lean_obj_tag(v___x_1392_) == 0 {
                            v_a_1393_ = leanh::lean_ctor_get(v___x_1392_, 0);
                            leanh::lean_inc(v_a_1393_);
                            leanh::lean_dec_ref_known(v___x_1392_, 1);
                            leanh::lean_inc_ref(v_body_1388_);
                            leanh::lean_inc_ref(v_post_1301_);
                            leanh::lean_inc_ref(v_pre_1299_);
                            v___x_1394_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1299_, v_post_1301_, v_body_1388_, v___y_1302_, v___y_1303_, v___y_1304_);
                            if leanh::lean_obj_tag(v___x_1394_) == 0 {
                                v_a_1395_ = leanh::lean_ctor_get(v___x_1394_, 0);
                                leanh::lean_inc(v_a_1395_);
                                leanh::lean_dec_ref_known(v___x_1394_, 1);
                                v___x_1396_ = lean_ptr_addr(v_type_1386_);
                                v___x_1397_ = lean_ptr_addr(v_a_1391_);
                                v___x_1398_ = lean_usize_dec_eq(v___x_1396_, v___x_1397_);
                                if v___x_1398_ == 0 {
                                    v___y_1307_ = v_declName_1385_;
                                    v___y_1308_ = v___y_1356_;
                                    v___y_1309_ = v_a_1395_;
                                    v___y_1310_ = v_nondep_1389_;
                                    v___y_1311_ = v_a_1393_;
                                    v___y_1312_ = v_a_1391_;
                                    v___y_1313_ = v_body_1388_;
                                    v___y_1314_ = v___x_1398_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1399_ = lean_ptr_addr(v_value_1387_);
                                    v___x_1400_ = lean_ptr_addr(v_a_1393_);
                                    v___x_1401_ = lean_usize_dec_eq(v___x_1399_, v___x_1400_);
                                    v___y_1307_ = v_declName_1385_;
                                    v___y_1308_ = v___y_1356_;
                                    v___y_1309_ = v_a_1395_;
                                    v___y_1310_ = v_nondep_1389_;
                                    v___y_1311_ = v_a_1393_;
                                    v___y_1312_ = v_a_1391_;
                                    v___y_1313_ = v_body_1388_;
                                    v___y_1314_ = v___x_1401_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_1393_);
                                leanh::lean_dec(v_a_1391_);
                                leanh::lean_dec_ref(v_body_1388_);
                                leanh::lean_dec_ref_known(v___y_1356_, 4);
                                leanh::lean_dec(v_declName_1385_);
                                leanh::lean_dec_ref(v_post_1301_);
                                leanh::lean_dec_ref(v_pre_1299_);
                                return v___x_1394_;
                            }
                        } else {
                            leanh::lean_dec(v_a_1391_);
                            leanh::lean_dec_ref(v_body_1388_);
                            leanh::lean_dec(v_declName_1385_);
                            leanh::lean_dec_ref_known(v___y_1356_, 4);
                            leanh::lean_dec_ref(v_post_1301_);
                            leanh::lean_dec_ref(v_pre_1299_);
                            return v___x_1392_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_body_1388_);
                        leanh::lean_dec(v_declName_1385_);
                        leanh::lean_dec_ref_known(v___y_1356_, 4);
                        leanh::lean_dec_ref(v_post_1301_);
                        leanh::lean_dec_ref(v_pre_1299_);
                        return v___x_1390_;
                    }
                }
                5 => {
                    v_dummy_1402_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_WF_floatRecApp___lam__1___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_WF_floatRecApp___lam__1___closed__0_once
                        ),
                        _init_l_Lean_Elab_WF_floatRecApp___lam__1___closed__0,
                    );
                    v_nargs_1403_ = l_Lean_Expr_getAppNumArgs(v___y_1356_);
                    leanh::lean_inc(v_nargs_1403_);
                    v___x_1404_ = lean_mk_array(v_nargs_1403_, v_dummy_1402_);
                    v___x_1405_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1406_ = lean_nat_sub(v_nargs_1403_, v___x_1405_);
                    leanh::lean_dec(v_nargs_1403_);
                    v___x_1407_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(v_pre_1299_, v_post_1301_, v___y_1356_, v___x_1404_, v___x_1406_, v___y_1302_, v___y_1303_, v___y_1304_);
                    return v___x_1407_;
                }
                10 => {
                    v_data_1408_ = leanh::lean_ctor_get(v___y_1356_, 0);
                    v_expr_1409_ = leanh::lean_ctor_get(v___y_1356_, 1);
                    leanh::lean_inc_ref(v_expr_1409_);
                    leanh::lean_inc_ref(v_post_1301_);
                    leanh::lean_inc_ref(v_pre_1299_);
                    v___x_1410_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1299_, v_post_1301_, v_expr_1409_, v___y_1302_, v___y_1303_, v___y_1304_);
                    if leanh::lean_obj_tag(v___x_1410_) == 0 {
                        v_a_1411_ = leanh::lean_ctor_get(v___x_1410_, 0);
                        leanh::lean_inc(v_a_1411_);
                        leanh::lean_dec_ref_known(v___x_1410_, 1);
                        v___x_1412_ = lean_ptr_addr(v_expr_1409_);
                        v___x_1413_ = lean_ptr_addr(v_a_1411_);
                        v___x_1414_ = lean_usize_dec_eq(v___x_1412_, v___x_1413_);
                        if v___x_1414_ == 0 {
                            leanh::lean_inc(v_data_1408_);
                            leanh::lean_dec_ref_known(v___y_1356_, 2);
                            v___x_1415_ = l_Lean_Expr_mdata___override(v_data_1408_, v_a_1411_);
                            v___x_1416_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v___x_1415_, v___y_1302_, v___y_1303_, v___y_1304_);
                            return v___x_1416_;
                        } else {
                            leanh::lean_dec(v_a_1411_);
                            v___x_1417_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v___y_1356_, v___y_1302_, v___y_1303_, v___y_1304_);
                            return v___x_1417_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_1356_, 2);
                        leanh::lean_dec_ref(v_post_1301_);
                        leanh::lean_dec_ref(v_pre_1299_);
                        return v___x_1410_;
                    }
                }
                11 => {
                    v_typeName_1418_ = leanh::lean_ctor_get(v___y_1356_, 0);
                    v_idx_1419_ = leanh::lean_ctor_get(v___y_1356_, 1);
                    v_struct_1420_ = leanh::lean_ctor_get(v___y_1356_, 2);
                    leanh::lean_inc_ref(v_struct_1420_);
                    leanh::lean_inc_ref(v_post_1301_);
                    leanh::lean_inc_ref(v_pre_1299_);
                    v___x_1421_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1299_, v_post_1301_, v_struct_1420_, v___y_1302_, v___y_1303_, v___y_1304_);
                    if leanh::lean_obj_tag(v___x_1421_) == 0 {
                        v_a_1422_ = leanh::lean_ctor_get(v___x_1421_, 0);
                        leanh::lean_inc(v_a_1422_);
                        leanh::lean_dec_ref_known(v___x_1421_, 1);
                        v___x_1423_ = lean_ptr_addr(v_struct_1420_);
                        v___x_1424_ = lean_ptr_addr(v_a_1422_);
                        v___x_1425_ = lean_usize_dec_eq(v___x_1423_, v___x_1424_);
                        if v___x_1425_ == 0 {
                            leanh::lean_inc(v_idx_1419_);
                            leanh::lean_inc(v_typeName_1418_);
                            leanh::lean_dec_ref_known(v___y_1356_, 3);
                            v___x_1426_ = l_Lean_Expr_proj___override(
                                v_typeName_1418_,
                                v_idx_1419_,
                                v_a_1422_,
                            );
                            v___x_1427_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v___x_1426_, v___y_1302_, v___y_1303_, v___y_1304_);
                            return v___x_1427_;
                        } else {
                            leanh::lean_dec(v_a_1422_);
                            v___x_1428_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v___y_1356_, v___y_1302_, v___y_1303_, v___y_1304_);
                            return v___x_1428_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_1356_, 3);
                        leanh::lean_dec_ref(v_post_1301_);
                        leanh::lean_dec_ref(v_pre_1299_);
                        return v___x_1421_;
                    }
                }
                _ => {
                    v___x_1429_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1299_, v_post_1301_, v___y_1356_, v___y_1302_, v___y_1303_, v___y_1304_);
                    return v___x_1429_;
                }
            },
            6 => {
                return v___x_1432_;
            }
            7 => {
                if v_isShared_1444_ == 0 {
                    v___x_1446_ = v___x_1443_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1447_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
                    v___x_1446_ = v_reuseFailAlloc_1447_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1446_;
            }
            9 => {
                if v_isShared_1452_ == 0 {
                    v___x_1454_ = v___x_1451_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1455_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
                    v___x_1454_ = v_reuseFailAlloc_1455_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1___boxed(
    mut v___x_1457_: *mut leanh::LeanObject,
    mut v_pre_1458_: *mut leanh::LeanObject,
    mut v_e_1459_: *mut leanh::LeanObject,
    mut v_post_1460_: *mut leanh::LeanObject,
    mut v___y_1461_: *mut leanh::LeanObject,
    mut v___y_1462_: *mut leanh::LeanObject,
    mut v___y_1463_: *mut leanh::LeanObject,
    mut v___y_1464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1465_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1(v___x_1457_, v_pre_1458_, v_e_1459_, v_post_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
    leanh::lean_dec(v___y_1463_);
    leanh::lean_dec_ref(v___y_1462_);
    leanh::lean_dec(v___y_1461_);
    return v_res_1465_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(
    mut v_pre_1466_: *mut leanh::LeanObject,
    mut v_post_1467_: *mut leanh::LeanObject,
    mut v_e_1468_: *mut leanh::LeanObject,
    mut v_a_1469_: *mut leanh::LeanObject,
    mut v___y_1470_: *mut leanh::LeanObject,
    mut v___y_1471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1478_: u8 = 0;
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1488_: u8 = 0;
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut v_unused_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1497_: u8 = 0;
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut v_val_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1506_: u8 = 0;
    let mut v_a_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1510_: u8 = 0;
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_1469_);
                v___x_1473_ = leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___x_1473_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1473_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1473_, 2, v_a_1469_);
                v___x_1474_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(leanh::lean_box(0), v___x_1473_, v___y_1470_, v___y_1471_);
                if leanh::lean_obj_tag(v___x_1474_) == 0 {
                    v_a_1475_ = leanh::lean_ctor_get(v___x_1474_, 0);
                    v_isSharedCheck_1506_ = (!leanh::lean_is_exclusive(v___x_1474_)) as u8;
                    if v_isSharedCheck_1506_ == 0 {
                        v___x_1477_ = v___x_1474_;
                        v_isShared_1478_ = v_isSharedCheck_1506_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1475_);
                        leanh::lean_dec(v___x_1474_);
                        v___x_1477_ = leanh::lean_box(0);
                        v_isShared_1478_ = v_isSharedCheck_1506_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1468_);
                    leanh::lean_dec_ref(v_post_1467_);
                    leanh::lean_dec_ref(v_pre_1466_);
                    v_a_1507_ = leanh::lean_ctor_get(v___x_1474_, 0);
                    v_isSharedCheck_1514_ = (!leanh::lean_is_exclusive(v___x_1474_)) as u8;
                    if v_isSharedCheck_1514_ == 0 {
                        v___x_1509_ = v___x_1474_;
                        v_isShared_1510_ = v_isSharedCheck_1514_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1507_);
                        leanh::lean_dec(v___x_1474_);
                        v___x_1509_ = leanh::lean_box(0);
                        v_isShared_1510_ = v_isSharedCheck_1514_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1479_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_a_1475_, v_e_1468_);
                leanh::lean_dec(v_a_1475_);
                if leanh::lean_obj_tag(v___x_1479_) == 0 {
                    leanh::lean_del_object(v___x_1477_);
                    v___x_1480_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___closed__0;
                    leanh::lean_inc_ref(v_e_1468_);
                    v___f_1481_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1___boxed as *mut core::ffi::c_void, 8, 4);
                    leanh::lean_closure_set(v___f_1481_, 0, v___x_1480_);
                    leanh::lean_closure_set(v___f_1481_, 1, v_pre_1466_);
                    leanh::lean_closure_set(v___f_1481_, 2, v_e_1468_);
                    leanh::lean_closure_set(v___f_1481_, 3, v_post_1467_);
                    v___x_1482_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v___f_1481_, v_a_1469_, v___y_1470_, v___y_1471_);
                    if leanh::lean_obj_tag(v___x_1482_) == 0 {
                        v_a_1483_ = leanh::lean_ctor_get(v___x_1482_, 0);
                        leanh::lean_inc_n(v_a_1483_, 2);
                        leanh::lean_dec_ref_known(v___x_1482_, 1);
                        leanh::lean_inc(v_a_1469_);
                        v___f_1484_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        leanh::lean_closure_set(v___f_1484_, 0, v_a_1469_);
                        leanh::lean_closure_set(v___f_1484_, 1, v_e_1468_);
                        leanh::lean_closure_set(v___f_1484_, 2, v_a_1483_);
                        v___x_1485_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(leanh::lean_box(0), v___f_1484_, v___y_1470_, v___y_1471_);
                        if leanh::lean_obj_tag(v___x_1485_) == 0 {
                            v_isSharedCheck_1492_ =
                                (!leanh::lean_is_exclusive(v___x_1485_)) as u8;
                            if v_isSharedCheck_1492_ == 0 {
                                v_unused_1493_ = leanh::lean_ctor_get(v___x_1485_, 0);
                                leanh::lean_dec(v_unused_1493_);
                                v___x_1487_ = v___x_1485_;
                                v_isShared_1488_ = v_isSharedCheck_1492_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1485_);
                                v___x_1487_ = leanh::lean_box(0);
                                v_isShared_1488_ = v_isSharedCheck_1492_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1483_);
                            v_a_1494_ = leanh::lean_ctor_get(v___x_1485_, 0);
                            v_isSharedCheck_1501_ =
                                (!leanh::lean_is_exclusive(v___x_1485_)) as u8;
                            if v_isSharedCheck_1501_ == 0 {
                                v___x_1496_ = v___x_1485_;
                                v_isShared_1497_ = v_isSharedCheck_1501_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1494_);
                                leanh::lean_dec(v___x_1485_);
                                v___x_1496_ = leanh::lean_box(0);
                                v_isShared_1497_ = v_isSharedCheck_1501_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_1468_);
                        return v___x_1482_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1468_);
                    leanh::lean_dec_ref(v_post_1467_);
                    leanh::lean_dec_ref(v_pre_1466_);
                    v_val_1502_ = leanh::lean_ctor_get(v___x_1479_, 0);
                    leanh::lean_inc(v_val_1502_);
                    leanh::lean_dec_ref_known(v___x_1479_, 1);
                    if v_isShared_1478_ == 0 {
                        leanh::lean_ctor_set(v___x_1477_, 0, v_val_1502_);
                        v___x_1504_ = v___x_1477_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1505_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_val_1502_);
                        v___x_1504_ = v_reuseFailAlloc_1505_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1488_ == 0 {
                    leanh::lean_ctor_set(v___x_1487_, 0, v_a_1483_);
                    v___x_1490_ = v___x_1487_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1491_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1483_);
                    v___x_1490_ = v_reuseFailAlloc_1491_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1490_;
            }
            4 => {
                if v_isShared_1497_ == 0 {
                    v___x_1499_ = v___x_1496_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
                    v___x_1499_ = v_reuseFailAlloc_1500_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1499_;
            }
            6 => {
                return v___x_1504_;
            }
            7 => {
                if v_isShared_1510_ == 0 {
                    v___x_1512_ = v___x_1509_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1513_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
                    v___x_1512_ = v_reuseFailAlloc_1513_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(
    mut v_pre_1515_: *mut leanh::LeanObject,
    mut v_post_1516_: *mut leanh::LeanObject,
    mut v_e_1517_: *mut leanh::LeanObject,
    mut v_a_1518_: *mut leanh::LeanObject,
    mut v___y_1519_: *mut leanh::LeanObject,
    mut v___y_1520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1526_: u8 = 0;
    let mut v_e_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut v_a_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1545_: u8 = 0;
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1549_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_post_1516_);
                leanh::lean_inc(v___y_1520_);
                leanh::lean_inc_ref(v___y_1519_);
                leanh::lean_inc_ref(v_e_1517_);
                v___x_1522_ = leanh::lean_apply_4(
                    v_post_1516_,
                    v_e_1517_,
                    v___y_1519_,
                    v___y_1520_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1522_) == 0 {
                    v_a_1523_ = leanh::lean_ctor_get(v___x_1522_, 0);
                    v_isSharedCheck_1541_ = (!leanh::lean_is_exclusive(v___x_1522_)) as u8;
                    if v_isSharedCheck_1541_ == 0 {
                        v___x_1525_ = v___x_1522_;
                        v_isShared_1526_ = v_isSharedCheck_1541_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1523_);
                        leanh::lean_dec(v___x_1522_);
                        v___x_1525_ = leanh::lean_box(0);
                        v_isShared_1526_ = v_isSharedCheck_1541_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1517_);
                    leanh::lean_dec_ref(v_post_1516_);
                    leanh::lean_dec_ref(v_pre_1515_);
                    v_a_1542_ = leanh::lean_ctor_get(v___x_1522_, 0);
                    v_isSharedCheck_1549_ = (!leanh::lean_is_exclusive(v___x_1522_)) as u8;
                    if v_isSharedCheck_1549_ == 0 {
                        v___x_1544_ = v___x_1522_;
                        v_isShared_1545_ = v_isSharedCheck_1549_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1542_);
                        leanh::lean_dec(v___x_1522_);
                        v___x_1544_ = leanh::lean_box(0);
                        v_isShared_1545_ = v_isSharedCheck_1549_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match leanh::lean_obj_tag(v_a_1523_) {
                0 => {
                    leanh::lean_dec_ref(v_e_1517_);
                    leanh::lean_dec_ref(v_post_1516_);
                    leanh::lean_dec_ref(v_pre_1515_);
                    v_e_1527_ = leanh::lean_ctor_get(v_a_1523_, 0);
                    leanh::lean_inc_ref(v_e_1527_);
                    leanh::lean_dec_ref_known(v_a_1523_, 1);
                    if v_isShared_1526_ == 0 {
                        leanh::lean_ctor_set(v___x_1525_, 0, v_e_1527_);
                        v___x_1529_ = v___x_1525_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1530_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_e_1527_);
                        v___x_1529_ = v_reuseFailAlloc_1530_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_1525_);
                    leanh::lean_dec_ref(v_e_1517_);
                    v_e_1531_ = leanh::lean_ctor_get(v_a_1523_, 0);
                    leanh::lean_inc_ref(v_e_1531_);
                    leanh::lean_dec_ref_known(v_a_1523_, 1);
                    v___x_1532_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1515_, v_post_1516_, v_e_1531_, v_a_1518_, v___y_1519_, v___y_1520_);
                    return v___x_1532_;
                }
                _ => {
                    leanh::lean_dec_ref(v_post_1516_);
                    leanh::lean_dec_ref(v_pre_1515_);
                    v_e_x3f_1533_ = leanh::lean_ctor_get(v_a_1523_, 0);
                    leanh::lean_inc(v_e_x3f_1533_);
                    leanh::lean_dec_ref_known(v_a_1523_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_1533_) == 0 {
                        if v_isShared_1526_ == 0 {
                            leanh::lean_ctor_set(v___x_1525_, 0, v_e_1517_);
                            v___x_1535_ = v___x_1525_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1536_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_e_1517_);
                            v___x_1535_ = v_reuseFailAlloc_1536_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_1517_);
                        v_val_1537_ = leanh::lean_ctor_get(v_e_x3f_1533_, 0);
                        leanh::lean_inc(v_val_1537_);
                        leanh::lean_dec_ref_known(v_e_x3f_1533_, 1);
                        if v_isShared_1526_ == 0 {
                            leanh::lean_ctor_set(v___x_1525_, 0, v_val_1537_);
                            v___x_1539_ = v___x_1525_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1540_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_val_1537_);
                            v___x_1539_ = v_reuseFailAlloc_1540_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_1529_;
            }
            3 => {
                return v___x_1535_;
            }
            4 => {
                return v___x_1539_;
            }
            5 => {
                if v_isShared_1545_ == 0 {
                    v___x_1547_ = v___x_1544_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1548_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
                    v___x_1547_ = v_reuseFailAlloc_1548_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1547_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3___boxed(
    mut v_pre_1550_: *mut leanh::LeanObject,
    mut v_post_1551_: *mut leanh::LeanObject,
    mut v_e_1552_: *mut leanh::LeanObject,
    mut v_a_1553_: *mut leanh::LeanObject,
    mut v___y_1554_: *mut leanh::LeanObject,
    mut v___y_1555_: *mut leanh::LeanObject,
    mut v___y_1556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1557_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_1550_, v_post_1551_, v_e_1552_, v_a_1553_, v___y_1554_, v___y_1555_);
    leanh::lean_dec(v___y_1555_);
    leanh::lean_dec_ref(v___y_1554_);
    leanh::lean_dec(v_a_1553_);
    return v_res_1557_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2___boxed(
    mut v_pre_1558_: *mut leanh::LeanObject,
    mut v_post_1559_: *mut leanh::LeanObject,
    mut v_sz_1560_: *mut leanh::LeanObject,
    mut v_i_1561_: *mut leanh::LeanObject,
    mut v_bs_1562_: *mut leanh::LeanObject,
    mut v___y_1563_: *mut leanh::LeanObject,
    mut v___y_1564_: *mut leanh::LeanObject,
    mut v___y_1565_: *mut leanh::LeanObject,
    mut v___y_1566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1567_: usize = 0;
    let mut v_i_boxed_1568_: usize = 0;
    let mut v_res_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1567_ = leanh::lean_unbox_usize(v_sz_1560_);
    leanh::lean_dec(v_sz_1560_);
    v_i_boxed_1568_ = leanh::lean_unbox_usize(v_i_1561_);
    leanh::lean_dec(v_i_1561_);
    v_res_1569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(v_pre_1558_, v_post_1559_, v_sz_boxed_1567_, v_i_boxed_1568_, v_bs_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
    leanh::lean_dec(v___y_1565_);
    leanh::lean_dec_ref(v___y_1564_);
    leanh::lean_dec(v___y_1563_);
    return v_res_1569_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5___boxed(
    mut v_pre_1570_: *mut leanh::LeanObject,
    mut v_post_1571_: *mut leanh::LeanObject,
    mut v_x_1572_: *mut leanh::LeanObject,
    mut v_x_1573_: *mut leanh::LeanObject,
    mut v_x_1574_: *mut leanh::LeanObject,
    mut v___y_1575_: *mut leanh::LeanObject,
    mut v___y_1576_: *mut leanh::LeanObject,
    mut v___y_1577_: *mut leanh::LeanObject,
    mut v___y_1578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1579_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(v_pre_1570_, v_post_1571_, v_x_1572_, v_x_1573_, v_x_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
    leanh::lean_dec(v___y_1577_);
    leanh::lean_dec_ref(v___y_1576_);
    leanh::lean_dec(v___y_1575_);
    return v_res_1579_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___boxed(
    mut v_pre_1580_: *mut leanh::LeanObject,
    mut v_post_1581_: *mut leanh::LeanObject,
    mut v_e_1582_: *mut leanh::LeanObject,
    mut v_a_1583_: *mut leanh::LeanObject,
    mut v___y_1584_: *mut leanh::LeanObject,
    mut v___y_1585_: *mut leanh::LeanObject,
    mut v___y_1586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1587_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1580_, v_post_1581_, v_e_1582_, v_a_1583_, v___y_1584_, v___y_1585_);
    leanh::lean_dec(v___y_1585_);
    leanh::lean_dec_ref(v___y_1584_);
    leanh::lean_dec(v_a_1583_);
    return v_res_1587_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1588_ = leanh::lean_box(0);
    v___x_1589_ = leanh::lean_unsigned_to_nat(16);
    v___x_1590_ = lean_mk_array(v___x_1589_, v___x_1588_);
    return v___x_1590_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0_once
        ),
        _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0,
    );
    v___x_1592_ = leanh::lean_unsigned_to_nat(0);
    v___x_1593_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1593_, 0, v___x_1592_);
    leanh::lean_ctor_set(v___x_1593_, 1, v___x_1591_);
    return v___x_1593_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1_once
        ),
        _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1,
    );
    v___x_1595_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_1595_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1595_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1595_, 2, v___x_1594_);
    return v___x_1595_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(
    mut v_input_1596_: *mut leanh::LeanObject,
    mut v_pre_1597_: *mut leanh::LeanObject,
    mut v_post_1598_: *mut leanh::LeanObject,
    mut v___y_1599_: *mut leanh::LeanObject,
    mut v___y_1600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1611_: u8 = 0;
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1615_: u8 = 0;
    let mut v_unused_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1602_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2_once), _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2);
                v___x_1603_ =
                    l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(
                        leanh::lean_box(0),
                        v___x_1602_,
                        v___y_1599_,
                        v___y_1600_,
                    );
                v_a_1604_ = leanh::lean_ctor_get(v___x_1603_, 0);
                leanh::lean_inc(v_a_1604_);
                leanh::lean_dec_ref(v___x_1603_);
                v___x_1605_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_1597_, v_post_1598_, v_input_1596_, v_a_1604_, v___y_1599_, v___y_1600_);
                if leanh::lean_obj_tag(v___x_1605_) == 0 {
                    v_a_1606_ = leanh::lean_ctor_get(v___x_1605_, 0);
                    leanh::lean_inc(v_a_1606_);
                    leanh::lean_dec_ref_known(v___x_1605_, 1);
                    v___x_1607_ = leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___x_1607_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_1607_, 1, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_1607_, 2, v_a_1604_);
                    v___x_1608_ =
                        l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(
                            leanh::lean_box(0),
                            v___x_1607_,
                            v___y_1599_,
                            v___y_1600_,
                        );
                    v_isSharedCheck_1615_ = (!leanh::lean_is_exclusive(v___x_1608_)) as u8;
                    if v_isSharedCheck_1615_ == 0 {
                        v_unused_1616_ = leanh::lean_ctor_get(v___x_1608_, 0);
                        leanh::lean_dec(v_unused_1616_);
                        v___x_1610_ = v___x_1608_;
                        v_isShared_1611_ = v_isSharedCheck_1615_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1608_);
                        v___x_1610_ = leanh::lean_box(0);
                        v_isShared_1611_ = v_isSharedCheck_1615_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1604_);
                    return v___x_1605_;
                }
            }
            1 => {
                if v_isShared_1611_ == 0 {
                    leanh::lean_ctor_set(v___x_1610_, 0, v_a_1606_);
                    v___x_1613_ = v___x_1610_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1614_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1606_);
                    v___x_1613_ = v_reuseFailAlloc_1614_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1613_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___boxed(
    mut v_input_1617_: *mut leanh::LeanObject,
    mut v_pre_1618_: *mut leanh::LeanObject,
    mut v_post_1619_: *mut leanh::LeanObject,
    mut v___y_1620_: *mut leanh::LeanObject,
    mut v___y_1621_: *mut leanh::LeanObject,
    mut v___y_1622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1623_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(
        v_input_1617_,
        v_pre_1618_,
        v_post_1619_,
        v___y_1620_,
        v___y_1621_,
    );
    leanh::lean_dec(v___y_1621_);
    leanh::lean_dec_ref(v___y_1620_);
    return v_res_1623_;
}
pub unsafe fn l_Lean_Elab_WF_floatRecApp(
    mut v_e_1626_: *mut leanh::LeanObject,
    mut v_a_1627_: *mut leanh::LeanObject,
    mut v_a_1628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1630_ = l_Lean_Elab_WF_floatRecApp___closed__0;
    v___f_1631_ = l_Lean_Elab_WF_floatRecApp___closed__1;
    v___x_1632_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(
        v_e_1626_,
        v___f_1630_,
        v___f_1631_,
        v_a_1627_,
        v_a_1628_,
    );
    return v___x_1632_;
}
pub unsafe fn l_Lean_Elab_WF_floatRecApp___boxed(
    mut v_e_1633_: *mut leanh::LeanObject,
    mut v_a_1634_: *mut leanh::LeanObject,
    mut v_a_1635_: *mut leanh::LeanObject,
    mut v_a_1636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1637_ = l_Lean_Elab_WF_floatRecApp(v_e_1633_, v_a_1634_, v_a_1635_);
    leanh::lean_dec(v_a_1635_);
    leanh::lean_dec_ref(v_a_1634_);
    return v_res_1637_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4(
    mut v_00_u03b2_1638_: *mut leanh::LeanObject,
    mut v_m_1639_: *mut leanh::LeanObject,
    mut v_a_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1641_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_m_1639_, v_a_1640_);
    return v___x_1641_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___boxed(
    mut v_00_u03b2_1642_: *mut leanh::LeanObject,
    mut v_m_1643_: *mut leanh::LeanObject,
    mut v_a_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1645_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4(v_00_u03b2_1642_, v_m_1643_, v_a_1644_);
    leanh::lean_dec_ref(v_a_1644_);
    leanh::lean_dec_ref(v_m_1643_);
    return v_res_1645_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8(
    mut v_00_u03b1_1646_: *mut leanh::LeanObject,
    mut v_ref_1647_: *mut leanh::LeanObject,
    mut v___y_1648_: *mut leanh::LeanObject,
    mut v___y_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_1647_);
    return v___x_1651_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___boxed(
    mut v_00_u03b1_1652_: *mut leanh::LeanObject,
    mut v_ref_1653_: *mut leanh::LeanObject,
    mut v___y_1654_: *mut leanh::LeanObject,
    mut v___y_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1657_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_1652_, v_ref_1653_, v___y_1654_, v___y_1655_);
    leanh::lean_dec(v___y_1655_);
    leanh::lean_dec_ref(v___y_1654_);
    return v_res_1657_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9(
    mut v_00_u03b1_1658_: *mut leanh::LeanObject,
    mut v___y_1659_: *mut leanh::LeanObject,
    mut v___y_1660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1662_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
    return v___x_1662_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___boxed(
    mut v_00_u03b1_1663_: *mut leanh::LeanObject,
    mut v___y_1664_: *mut leanh::LeanObject,
    mut v___y_1665_: *mut leanh::LeanObject,
    mut v___y_1666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1667_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9(v_00_u03b1_1663_, v___y_1664_, v___y_1665_);
    leanh::lean_dec(v___y_1665_);
    leanh::lean_dec_ref(v___y_1664_);
    return v_res_1667_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6(
    mut v_00_u03b1_1668_: *mut leanh::LeanObject,
    mut v_x_1669_: *mut leanh::LeanObject,
    mut v___y_1670_: *mut leanh::LeanObject,
    mut v___y_1671_: *mut leanh::LeanObject,
    mut v___y_1672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v_x_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
    return v___x_1674_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___boxed(
    mut v_00_u03b1_1675_: *mut leanh::LeanObject,
    mut v_x_1676_: *mut leanh::LeanObject,
    mut v___y_1677_: *mut leanh::LeanObject,
    mut v___y_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
    mut v___y_1680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1681_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6(v_00_u03b1_1675_, v_x_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
    leanh::lean_dec(v___y_1679_);
    leanh::lean_dec_ref(v___y_1678_);
    leanh::lean_dec(v___y_1677_);
    return v_res_1681_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7(
    mut v_00_u03b2_1682_: *mut leanh::LeanObject,
    mut v_m_1683_: *mut leanh::LeanObject,
    mut v_a_1684_: *mut leanh::LeanObject,
    mut v_b_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1686_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v_m_1683_, v_a_1684_, v_b_1685_);
    return v___x_1686_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(
    mut v_00_u03b2_1687_: *mut leanh::LeanObject,
    mut v_a_1688_: *mut leanh::LeanObject,
    mut v_x_1689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1690_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(v_a_1688_, v_x_1689_);
    return v___x_1690_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___boxed(
    mut v_00_u03b2_1691_: *mut leanh::LeanObject,
    mut v_a_1692_: *mut leanh::LeanObject,
    mut v_x_1693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1694_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(v_00_u03b2_1691_, v_a_1692_, v_x_1693_);
    leanh::lean_dec(v_x_1693_);
    leanh::lean_dec_ref(v_a_1692_);
    return v_res_1694_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11(
    mut v_00_u03b2_1695_: *mut leanh::LeanObject,
    mut v_a_1696_: *mut leanh::LeanObject,
    mut v_x_1697_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1698_: u8 = 0;
    v___x_1698_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_a_1696_, v_x_1697_);
    return v___x_1698_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___boxed(
    mut v_00_u03b2_1699_: *mut leanh::LeanObject,
    mut v_a_1700_: *mut leanh::LeanObject,
    mut v_x_1701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1702_: u8 = 0;
    let mut v_r_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_1699_, v_a_1700_, v_x_1701_);
    leanh::lean_dec(v_x_1701_);
    leanh::lean_dec_ref(v_a_1700_);
    v_r_1703_ = leanh::lean_box((v_res_1702_) as usize);
    return v_r_1703_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12(
    mut v_00_u03b2_1704_: *mut leanh::LeanObject,
    mut v_data_1705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(v_data_1705_);
    return v___x_1706_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13(
    mut v_00_u03b2_1707_: *mut leanh::LeanObject,
    mut v_a_1708_: *mut leanh::LeanObject,
    mut v_b_1709_: *mut leanh::LeanObject,
    mut v_x_1710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13___redArg(v_a_1708_, v_b_1709_, v_x_1710_);
    return v___x_1711_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13(
    mut v_00_u03b2_1712_: *mut leanh::LeanObject,
    mut v_i_1713_: *mut leanh::LeanObject,
    mut v_source_1714_: *mut leanh::LeanObject,
    mut v_target_1715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v_i_1713_, v_source_1714_, v_target_1715_);
    return v___x_1716_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14(
    mut v_00_u03b2_1717_: *mut leanh::LeanObject,
    mut v_x_1718_: *mut leanh::LeanObject,
    mut v_x_1719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1720_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_x_1718_, v_x_1719_);
    return v___x_1720_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_RecAppSyntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Transform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_RecAppSyntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin);
}