// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Preprocess
// Imports: Lean.Elab.RecAppSyntax Lean.Meta.WHNF
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_maxRecDepthErrorMessage};
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
    lean_array_fget, lean_array_get_size, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Util::FindExpr::lean_find_expr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_panic___at___00Lean_Elab_Structural_preprocess_spec__0___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instInhabitedCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Elab_Structural_preprocess_spec__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Elab_Structural_preprocess_spec__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Structural_preprocess___lam__0___closed__0_value: LeanCtorObject<1> =
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
static mut l_Lean_Elab_Structural_preprocess___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_preprocess___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Structural_preprocess___lam__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_preprocess___lam__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_preprocess___lam__1___closed__1_value: LeanStringObject<46> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 46,
        m_capacity: 46,
        m_length: 45,
        m_data: [
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105,
            116, 105, 111, 110, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108, 46, 80, 114,
            101, 112, 114, 111, 99, 101, 115, 115, 0,
        ],
    };
static mut l_Lean_Elab_Structural_preprocess___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_preprocess___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Structural_preprocess___lam__1___closed__2_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97,
            108, 46, 112, 114, 101, 112, 114, 111, 99, 101, 115, 115, 0,
        ],
    };
static mut l_Lean_Elab_Structural_preprocess___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_preprocess___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Structural_preprocess___lam__1___closed__3_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Elab_Structural_preprocess___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_preprocess___lam__1___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Structural_preprocess___lam__1___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_preprocess___lam__1___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___closed__0_value) as *mut LeanObject;
static mut l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_preprocess___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Structural_preprocess___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Structural_preprocess___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_preprocess___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce_spec__0_spec__0(
    mut v_a_927_: *mut LeanObject,
    mut v_as_928_: *mut LeanObject,
    mut v_i_929_: usize,
    mut v_stop_930_: usize,
) -> u8 {
    let mut v___x_931_: u8 = 0;
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_938_: *mut LeanObject,
    mut v_as_939_: *mut LeanObject,
    mut v_i_940_: *mut LeanObject,
    mut v_stop_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_942_: usize = 0;
    let mut v_stop_boxed_943_: usize = 0;
    let mut v_res_944_: u8 = 0;
    let mut v_r_945_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_942_ = lean_unbox_usize(v_i_940_);
    lean_dec(v_i_940_);
    v_stop_boxed_943_ = lean_unbox_usize(v_stop_941_);
    lean_dec(v_stop_941_);
    v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce_spec__0_spec__0(v_a_938_, v_as_939_, v_i_boxed_942_, v_stop_boxed_943_);
    lean_dec_ref(v_as_939_);
    lean_dec(v_a_938_);
    v_r_945_ = lean_box((v_res_944_) as usize);
    return v_r_945_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce_spec__0(
    mut v_as_946_: *mut LeanObject,
    mut v_a_947_: *mut LeanObject,
) -> u8 {
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: u8 = 0;
    v___x_948_ = lean_unsigned_to_nat(0);
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
    mut v_as_954_: *mut LeanObject,
    mut v_a_955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_956_: u8 = 0;
    let mut v_r_957_: *mut LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce_spec__0(v_as_954_, v_a_955_);
    lean_dec(v_a_955_);
    lean_dec_ref(v_as_954_);
    v_r_957_ = lean_box((v_res_956_) as usize);
    return v_r_957_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lam__0(
    mut v___x_958_: u8,
    mut v_recFnNames_959_: *mut LeanObject,
    mut v_e_960_: *mut LeanObject,
) -> u8 {
    let mut v___x_961_: u8 = 0;
    v___x_961_ = l_Lean_Expr_isConst(v_e_960_);
    if v___x_961_ == 0 {
        return v___x_958_;
    } else {
        let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_963_: u8 = 0;
        v___x_962_ = l_Lean_Expr_constName_x21(v_e_960_);
        v___x_963_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce_spec__0(v_recFnNames_959_, v___x_962_);
        lean_dec(v___x_962_);
        return v___x_963_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lam__0___boxed(
    mut v___x_964_: *mut LeanObject,
    mut v_recFnNames_965_: *mut LeanObject,
    mut v_e_966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_324__boxed_967_: u8 = 0;
    let mut v_res_968_: u8 = 0;
    let mut v_r_969_: *mut LeanObject = core::ptr::null_mut();
    v___x_324__boxed_967_ = (lean_unbox(v___x_964_) as u8);
    v_res_968_ = l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lam__0(v___x_324__boxed_967_, v_recFnNames_965_, v_e_966_);
    lean_dec_ref(v_e_966_);
    lean_dec_ref(v_recFnNames_965_);
    v_r_969_ = lean_box((v_res_968_) as usize);
    return v_r_969_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(
    mut v_e_970_: *mut LeanObject,
    mut v_recFnNames_971_: *mut LeanObject,
) -> u8 {
    let mut v___x_972_: u8 = 0;
    let mut v___x_973_: u8 = 0;
    v___x_972_ = 0;
    v___x_973_ = l_Lean_Expr_isHeadBetaTarget(v_e_970_, v___x_972_);
    if v___x_973_ == 0 {
        lean_dec_ref(v_recFnNames_971_);
        return v___x_972_;
    } else {
        let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_975_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
        v___x_974_ = lean_box((v___x_972_) as usize);
        v___f_975_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
        lean_closure_set(v___f_975_, 0, v___x_974_);
        lean_closure_set(v___f_975_, 1, v_recFnNames_971_);
        v___x_976_ = l_Lean_Expr_getAppFn(v_e_970_);
        v___x_977_ = lean_find_expr(v___f_975_, v___x_976_);
        lean_dec_ref(v___x_976_);
        lean_dec_ref(v___f_975_);
        if lean_obj_tag(v___x_977_) == 0 {
            return v___x_972_;
        } else {
            lean_dec_ref_known(v___x_977_, 1);
            return v___x_973_;
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___boxed(
    mut v_e_978_: *mut LeanObject,
    mut v_recFnNames_979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_980_: u8 = 0;
    let mut v_r_981_: *mut LeanObject = core::ptr::null_mut();
    v_res_980_ = l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(v_e_978_, v_recFnNames_979_);
    lean_dec_ref(v_e_978_);
    v_r_981_ = lean_box((v_res_980_) as usize);
    return v_r_981_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_preprocess_spec__0(
    mut v_msg_983_: *mut LeanObject,
    mut v___y_984_: *mut LeanObject,
    mut v___y_985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840__overap_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    v___f_987_ = l_panic___at___00Lean_Elab_Structural_preprocess_spec__0___closed__0;
    v___x_840__overap_988_ = lean_panic_fn_borrowed(v___f_987_, v_msg_983_);
    lean_inc(v___y_985_);
    lean_inc_ref(v___y_984_);
    v___x_989_ = lean_apply_3(v___x_840__overap_988_, v___y_984_, v___y_985_, lean_box(0));
    return v___x_989_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_preprocess_spec__0___boxed(
    mut v_msg_990_: *mut LeanObject,
    mut v___y_991_: *mut LeanObject,
    mut v___y_992_: *mut LeanObject,
    mut v___y_993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_994_: *mut LeanObject = core::ptr::null_mut();
    v_res_994_ = l_panic___at___00Lean_Elab_Structural_preprocess_spec__0(
        v_msg_990_, v___y_991_, v___y_992_,
    );
    lean_dec(v___y_992_);
    lean_dec_ref(v___y_991_);
    return v_res_994_;
}
pub unsafe fn l_Lean_Elab_Structural_preprocess___lam__0(
    mut v_recFnNames_997_: *mut LeanObject,
    mut v_e_998_: *mut LeanObject,
    mut v___y_999_: *mut LeanObject,
    mut v___y_1000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1002_: u8 = 0;
    v___x_1002_ = l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(v_e_998_, v_recFnNames_997_);
    if v___x_1002_ == 0 {
        let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_e_998_);
        v___x_1003_ = l_Lean_Elab_Structural_preprocess___lam__0___closed__0;
        v___x_1004_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1004_, 0, v___x_1003_);
        return v___x_1004_;
    } else {
        let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
        v___x_1005_ = l_Lean_Expr_headBeta(v_e_998_);
        v___x_1006_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1006_, 0, v___x_1005_);
        v___x_1007_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1007_, 0, v___x_1006_);
        return v___x_1007_;
    }
}
pub unsafe fn l_Lean_Elab_Structural_preprocess___lam__0___boxed(
    mut v_recFnNames_1008_: *mut LeanObject,
    mut v_e_1009_: *mut LeanObject,
    mut v___y_1010_: *mut LeanObject,
    mut v___y_1011_: *mut LeanObject,
    mut v___y_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1013_: *mut LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Lean_Elab_Structural_preprocess___lam__0(
        v_recFnNames_1008_,
        v_e_1009_,
        v___y_1010_,
        v___y_1011_,
    );
    lean_dec(v___y_1011_);
    lean_dec_ref(v___y_1010_);
    return v_res_1013_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__0() -> *mut LeanObject {
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1015_: *mut LeanObject = core::ptr::null_mut();
    v___x_1014_ = lean_box(0);
    v_dummy_1015_ = l_Lean_Expr_sort___override(v___x_1014_);
    return v_dummy_1015_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__4() -> *mut LeanObject {
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    v___x_1019_ = l_Lean_Elab_Structural_preprocess___lam__1___closed__3;
    v___x_1020_ = lean_unsigned_to_nat(39);
    v___x_1021_ = lean_unsigned_to_nat(56);
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
    mut v_e_1025_: *mut LeanObject,
    mut v___y_1026_: *mut LeanObject,
    mut v___y_1027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1033_: u8 = 0;
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: u8 = 0;
    let mut v_dummy_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1053_: u8 = 0;
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1057_: u8 = 0;
    let mut v___x_1058_: u8 = 0;
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_dec_ref(v___x_1059_);
                    v___y_1033_ = v___x_1060_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1030_ = l_Lean_Elab_Structural_preprocess___lam__0___closed__0;
                v___x_1031_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1031_, 0, v___x_1030_);
                return v___x_1031_;
            }
            2 => {
                if v___y_1033_ == 0 {
                    lean_dec_ref(v_e_1025_);
                    state = 1;
                    continue;
                } else {
                    v___x_1034_ = l_Lean_Expr_getAppFn(v_e_1025_);
                    if lean_obj_tag(v___x_1034_) == 10 {
                        v_data_1035_ = lean_ctor_get(v___x_1034_, 0);
                        lean_inc(v_data_1035_);
                        v_expr_1036_ = lean_ctor_get(v___x_1034_, 1);
                        lean_inc_ref(v_expr_1036_);
                        lean_dec_ref_known(v___x_1034_, 2);
                        v___x_1037_ = l_Lean_MData_isRecApp(v_data_1035_);
                        if v___x_1037_ == 0 {
                            lean_dec_ref(v_expr_1036_);
                            lean_dec(v_data_1035_);
                            lean_dec_ref(v_e_1025_);
                            state = 1;
                            continue;
                        } else {
                            v_dummy_1038_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Structural_preprocess___lam__1___closed__0
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Structural_preprocess___lam__1___closed__0_once
                                ),
                                _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__0,
                            );
                            v_nargs_1039_ = l_Lean_Expr_getAppNumArgs(v_e_1025_);
                            lean_inc(v_nargs_1039_);
                            v___x_1040_ = lean_mk_array(v_nargs_1039_, v_dummy_1038_);
                            v___x_1041_ = lean_unsigned_to_nat(1);
                            v___x_1042_ = lean_nat_sub(v_nargs_1039_, v___x_1041_);
                            lean_dec(v_nargs_1039_);
                            v___x_1043_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                v_e_1025_,
                                v___x_1040_,
                                v___x_1042_,
                            );
                            v___x_1044_ = l_Lean_Expr_beta(v_expr_1036_, v___x_1043_);
                            v___x_1045_ = l_Lean_Expr_mdata___override(v_data_1035_, v___x_1044_);
                            v___x_1046_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1046_, 0, v___x_1045_);
                            v___x_1047_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1047_, 0, v___x_1046_);
                            return v___x_1047_;
                        }
                    } else {
                        lean_dec_ref(v___x_1034_);
                        lean_dec_ref(v_e_1025_);
                        v___x_1048_ = lean_obj_once(
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
                        if lean_obj_tag(v___x_1049_) == 0 {
                            lean_dec_ref_known(v___x_1049_, 1);
                            state = 1;
                            continue;
                        } else {
                            v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
                            v_isSharedCheck_1057_ = (!lean_is_exclusive(v___x_1049_)) as u8;
                            if v_isSharedCheck_1057_ == 0 {
                                v___x_1052_ = v___x_1049_;
                                v_isShared_1053_ = v_isSharedCheck_1057_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1050_);
                                lean_dec(v___x_1049_);
                                v___x_1052_ = lean_box(0);
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
                    v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
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
    mut v_e_1061_: *mut LeanObject,
    mut v___y_1062_: *mut LeanObject,
    mut v___y_1063_: *mut LeanObject,
    mut v___y_1064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1065_: *mut LeanObject = core::ptr::null_mut();
    v_res_1065_ = l_Lean_Elab_Structural_preprocess___lam__1(v_e_1061_, v___y_1062_, v___y_1063_);
    lean_dec(v___y_1063_);
    lean_dec_ref(v___y_1062_);
    return v_res_1065_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5___redArg(
    mut v_a_1066_: *mut LeanObject,
    mut v_x_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: u8 = 0;
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1067_) == 0 {
                    v___x_1068_ = lean_box(0);
                    return v___x_1068_;
                } else {
                    v_key_1069_ = lean_ctor_get(v_x_1067_, 0);
                    v_value_1070_ = lean_ctor_get(v_x_1067_, 1);
                    v_tail_1071_ = lean_ctor_get(v_x_1067_, 2);
                    v___x_1072_ = l_Lean_ExprStructEq_beq(v_key_1069_, v_a_1066_);
                    if v___x_1072_ == 0 {
                        v_x_1067_ = v_tail_1071_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_1070_);
                        v___x_1074_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1074_, 0, v_value_1070_);
                        return v___x_1074_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5___redArg___boxed(
    mut v_a_1075_: *mut LeanObject,
    mut v_x_1076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1077_: *mut LeanObject = core::ptr::null_mut();
    v_res_1077_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5___redArg(v_a_1075_, v_x_1076_);
    lean_dec(v_x_1076_);
    lean_dec_ref(v_a_1075_);
    return v_res_1077_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4___redArg(
    mut v_m_1078_: *mut LeanObject,
    mut v_a_1079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_1080_ = lean_ctor_get(v_m_1078_, 1);
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
    mut v_m_1096_: *mut LeanObject,
    mut v_a_1097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1098_: *mut LeanObject = core::ptr::null_mut();
    v_res_1098_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4___redArg(v_m_1096_, v_a_1097_);
    lean_dec_ref(v_a_1097_);
    lean_dec_ref(v_m_1096_);
    return v_res_1098_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__0(
    mut v_00_u03b1_1099_: *mut LeanObject,
    mut v_x_1100_: *mut LeanObject,
    mut v___y_1101_: *mut LeanObject,
    mut v___y_1102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    v___x_1104_ = lean_apply_1(v_x_1100_, lean_box(0));
    v___x_1105_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1105_, 0, v___x_1104_);
    return v___x_1105_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__0___boxed(
    mut v_00_u03b1_1106_: *mut LeanObject,
    mut v_x_1107_: *mut LeanObject,
    mut v___y_1108_: *mut LeanObject,
    mut v___y_1109_: *mut LeanObject,
    mut v___y_1110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1111_: *mut LeanObject = core::ptr::null_mut();
    v_res_1111_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__0(v_00_u03b1_1106_, v_x_1107_, v___y_1108_, v___y_1109_);
    lean_dec(v___y_1109_);
    lean_dec_ref(v___y_1108_);
    return v_res_1111_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    v___x_1117_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1118_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1118_, 0, v___x_1117_);
    return v___x_1118_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    v___x_1119_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__3);
    v___x_1120_ = l_Lean_MessageData_ofFormat(v___x_1119_);
    return v___x_1120_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    v___x_1121_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__4);
    v___x_1122_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__2;
    v___x_1123_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_1123_, 0, v___x_1122_);
    lean_ctor_set(v___x_1123_, 1, v___x_1121_);
    return v___x_1123_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg(
    mut v_ref_1124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    v___x_1126_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___closed__5);
    v___x_1127_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1127_, 0, v_ref_1124_);
    lean_ctor_set(v___x_1127_, 1, v___x_1126_);
    v___x_1128_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1128_, 0, v___x_1127_);
    return v___x_1128_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg___boxed(
    mut v_ref_1129_: *mut LeanObject,
    mut v___y_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1131_: *mut LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_1129_);
    return v_res_1131_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    v___x_1132_ = lean_box(0);
    v___x_1133_ = l_Lean_interruptExceptionId;
    v___x_1134_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1134_, 0, v___x_1133_);
    lean_ctor_set(v___x_1134_, 1, v___x_1132_);
    return v___x_1134_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg()
-> *mut LeanObject {
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    v___x_1136_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg___closed__0);
    v___x_1137_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1137_, 0, v___x_1136_);
    return v___x_1137_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg___boxed(
    mut v___y_1138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1139_: *mut LeanObject = core::ptr::null_mut();
    v_res_1139_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg();
    return v_res_1139_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6___redArg(
    mut v_x_1140_: *mut LeanObject,
    mut v___y_1141_: *mut LeanObject,
    mut v___y_1142_: *mut LeanObject,
    mut v___y_1143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1150_: u8 = 0;
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1154_: u8 = 0;
    let mut v___y_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1162_: u8 = 0;
    let mut v___y_1163_: u8 = 0;
    let mut v___y_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1188_: u8 = 0;
    let mut v_cancelTk_x3f_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1190_: u8 = 0;
    let mut v_inheritedTraceOptions_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: u8 = 0;
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: u8 = 0;
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1203_: u8 = 0;
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1176_ = lean_ctor_get(v___y_1142_, 0);
                v_fileMap_1177_ = lean_ctor_get(v___y_1142_, 1);
                v_options_1178_ = lean_ctor_get(v___y_1142_, 2);
                v_currRecDepth_1179_ = lean_ctor_get(v___y_1142_, 3);
                v_maxRecDepth_1180_ = lean_ctor_get(v___y_1142_, 4);
                v_ref_1181_ = lean_ctor_get(v___y_1142_, 5);
                v_currNamespace_1182_ = lean_ctor_get(v___y_1142_, 6);
                v_openDecls_1183_ = lean_ctor_get(v___y_1142_, 7);
                v_initHeartbeats_1184_ = lean_ctor_get(v___y_1142_, 8);
                v_maxHeartbeats_1185_ = lean_ctor_get(v___y_1142_, 9);
                v_quotContext_1186_ = lean_ctor_get(v___y_1142_, 10);
                v_currMacroScope_1187_ = lean_ctor_get(v___y_1142_, 11);
                v_diag_1188_ = lean_ctor_get_uint8(
                    v___y_1142_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1189_ = lean_ctor_get(v___y_1142_, 12);
                v_suppressElabErrors_1190_ = lean_ctor_get_uint8(
                    v___y_1142_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1191_ = lean_ctor_get(v___y_1142_, 13);
                if lean_obj_tag(v_cancelTk_x3f_1189_) == 1 {
                    v_val_1197_ = lean_ctor_get(v_cancelTk_x3f_1189_, 0);
                    v___x_1198_ = l_IO_CancelToken_isSet(v_val_1197_);
                    if v___x_1198_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        lean_dec_ref(v_x_1140_);
                        v___x_1199_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg();
                        v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
                        v_isSharedCheck_1207_ = (!lean_is_exclusive(v___x_1199_)) as u8;
                        if v_isSharedCheck_1207_ == 0 {
                            v___x_1202_ = v___x_1199_;
                            v_isShared_1203_ = v_isSharedCheck_1207_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1200_);
                            lean_dec(v___x_1199_);
                            v___x_1202_ = lean_box(0);
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
                if lean_obj_tag(v___y_1146_) == 0 {
                    return v___y_1146_;
                } else {
                    v_a_1147_ = lean_ctor_get(v___y_1146_, 0);
                    v_isSharedCheck_1154_ = (!lean_is_exclusive(v___y_1146_)) as u8;
                    if v_isSharedCheck_1154_ == 0 {
                        v___x_1149_ = v___y_1146_;
                        v_isShared_1150_ = v_isSharedCheck_1154_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1147_);
                        lean_dec(v___y_1146_);
                        v___x_1149_ = lean_box(0);
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
                    v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
                    v___x_1152_ = v_reuseFailAlloc_1153_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1152_;
            }
            4 => {
                v___x_1172_ = lean_unsigned_to_nat(1);
                v___x_1173_ = lean_nat_add(v___y_1157_, v___x_1172_);
                lean_inc_ref(v___y_1168_);
                lean_inc(v___y_1156_);
                lean_inc(v___y_1171_);
                lean_inc(v___y_1165_);
                lean_inc(v___y_1161_);
                lean_inc(v___y_1169_);
                lean_inc(v___y_1159_);
                lean_inc(v___y_1170_);
                lean_inc(v___y_1160_);
                lean_inc_ref(v___y_1158_);
                lean_inc_ref(v___y_1167_);
                lean_inc_ref(v___y_1164_);
                v___x_1174_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_1174_, 0, v___y_1164_);
                lean_ctor_set(v___x_1174_, 1, v___y_1167_);
                lean_ctor_set(v___x_1174_, 2, v___y_1158_);
                lean_ctor_set(v___x_1174_, 3, v___x_1173_);
                lean_ctor_set(v___x_1174_, 4, v___y_1160_);
                lean_ctor_set(v___x_1174_, 5, v___y_1166_);
                lean_ctor_set(v___x_1174_, 6, v___y_1170_);
                lean_ctor_set(v___x_1174_, 7, v___y_1159_);
                lean_ctor_set(v___x_1174_, 8, v___y_1169_);
                lean_ctor_set(v___x_1174_, 9, v___y_1161_);
                lean_ctor_set(v___x_1174_, 10, v___y_1165_);
                lean_ctor_set(v___x_1174_, 11, v___y_1171_);
                lean_ctor_set(v___x_1174_, 12, v___y_1156_);
                lean_ctor_set(v___x_1174_, 13, v___y_1168_);
                lean_ctor_set_uint8(
                    v___x_1174_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___y_1163_,
                );
                lean_ctor_set_uint8(
                    v___x_1174_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v___y_1162_,
                );
                lean_inc(v___y_1143_);
                lean_inc(v___y_1141_);
                v___x_1175_ = lean_apply_4(
                    v_x_1140_,
                    v___y_1141_,
                    v___x_1174_,
                    v___y_1143_,
                    lean_box(0),
                );
                v___y_1146_ = v___x_1175_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1193_ = lean_unsigned_to_nat(0);
                v___x_1194_ = lean_nat_dec_eq(v_maxRecDepth_1180_, v___x_1193_);
                if v___x_1194_ == 0 {
                    v___x_1195_ = lean_nat_dec_eq(v_currRecDepth_1179_, v_maxRecDepth_1180_);
                    if v___x_1195_ == 0 {
                        lean_inc(v_ref_1181_);
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
                        lean_dec_ref(v_x_1140_);
                        lean_inc(v_ref_1181_);
                        v___x_1196_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_1181_);
                        v___y_1146_ = v___x_1196_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_inc(v_ref_1181_);
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
                    v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
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
    mut v_x_1208_: *mut LeanObject,
    mut v___y_1209_: *mut LeanObject,
    mut v___y_1210_: *mut LeanObject,
    mut v___y_1211_: *mut LeanObject,
    mut v___y_1212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1213_: *mut LeanObject = core::ptr::null_mut();
    v_res_1213_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6___redArg(v_x_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
    lean_dec(v___y_1211_);
    lean_dec_ref(v___y_1210_);
    lean_dec(v___y_1209_);
    return v_res_1213_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(
    mut v_x_1214_: *mut LeanObject,
    mut v_x_1215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1215_) == 0 {
                    return v_x_1214_;
                } else {
                    v_key_1216_ = lean_ctor_get(v_x_1215_, 0);
                    v_value_1217_ = lean_ctor_get(v_x_1215_, 1);
                    v_tail_1218_ = lean_ctor_get(v_x_1215_, 2);
                    v_isSharedCheck_1241_ = (!lean_is_exclusive(v_x_1215_)) as u8;
                    if v_isSharedCheck_1241_ == 0 {
                        v___x_1220_ = v_x_1215_;
                        v_isShared_1221_ = v_isSharedCheck_1241_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1218_);
                        lean_inc(v_value_1217_);
                        lean_inc(v_key_1216_);
                        lean_dec(v_x_1215_);
                        v___x_1220_ = lean_box(0);
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
                lean_inc(v___x_1235_);
                if v_isShared_1221_ == 0 {
                    lean_ctor_set(v___x_1220_, 2, v___x_1235_);
                    v___x_1237_ = v___x_1220_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_key_1216_);
                    lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_value_1217_);
                    lean_ctor_set(v_reuseFailAlloc_1240_, 2, v___x_1235_);
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
    mut v_i_1242_: *mut LeanObject,
    mut v_source_1243_: *mut LeanObject,
    mut v_target_1244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: u8 = 0;
    let mut v_es_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1245_ = lean_array_get_size(v_source_1243_);
                v___x_1246_ = lean_nat_dec_lt(v_i_1242_, v___x_1245_);
                if v___x_1246_ == 0 {
                    lean_dec_ref(v_source_1243_);
                    lean_dec(v_i_1242_);
                    return v_target_1244_;
                } else {
                    v_es_1247_ = lean_array_fget(v_source_1243_, v_i_1242_);
                    v___x_1248_ = lean_box(0);
                    v_source_1249_ = lean_array_fset(v_source_1243_, v_i_1242_, v___x_1248_);
                    v_target_1250_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_target_1244_, v_es_1247_);
                    v___x_1251_ = lean_unsigned_to_nat(1);
                    v___x_1252_ = lean_nat_add(v_i_1242_, v___x_1251_);
                    lean_dec(v_i_1242_);
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
    mut v_data_1254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    v___x_1255_ = lean_array_get_size(v_data_1254_);
    v___x_1256_ = lean_unsigned_to_nat(2);
    v_nbuckets_1257_ = lean_nat_mul(v___x_1255_, v___x_1256_);
    v___x_1258_ = lean_unsigned_to_nat(0);
    v___x_1259_ = lean_box(0);
    v___x_1260_ = lean_mk_array(v_nbuckets_1257_, v___x_1259_);
    v___x_1261_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v___x_1258_, v_data_1254_, v___x_1260_);
    return v___x_1261_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__11___redArg(
    mut v_a_1262_: *mut LeanObject,
    mut v_x_1263_: *mut LeanObject,
) -> u8 {
    let mut v___x_1264_: u8 = 0;
    let mut v_key_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1263_) == 0 {
                    v___x_1264_ = 0;
                    return v___x_1264_;
                } else {
                    v_key_1265_ = lean_ctor_get(v_x_1263_, 0);
                    v_tail_1266_ = lean_ctor_get(v_x_1263_, 2);
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
    mut v_a_1269_: *mut LeanObject,
    mut v_x_1270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1271_: u8 = 0;
    let mut v_r_1272_: *mut LeanObject = core::ptr::null_mut();
    v_res_1271_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__11___redArg(v_a_1269_, v_x_1270_);
    lean_dec(v_x_1270_);
    lean_dec_ref(v_a_1269_);
    v_r_1272_ = lean_box((v_res_1271_) as usize);
    return v_r_1272_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__13___redArg(
    mut v_a_1273_: *mut LeanObject,
    mut v_b_1274_: *mut LeanObject,
    mut v_x_1275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1281_: u8 = 0;
    let mut v___x_1282_: u8 = 0;
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1275_) == 0 {
                    lean_dec(v_b_1274_);
                    lean_dec_ref(v_a_1273_);
                    return v_x_1275_;
                } else {
                    v_key_1276_ = lean_ctor_get(v_x_1275_, 0);
                    v_value_1277_ = lean_ctor_get(v_x_1275_, 1);
                    v_tail_1278_ = lean_ctor_get(v_x_1275_, 2);
                    v_isSharedCheck_1290_ = (!lean_is_exclusive(v_x_1275_)) as u8;
                    if v_isSharedCheck_1290_ == 0 {
                        v___x_1280_ = v_x_1275_;
                        v_isShared_1281_ = v_isSharedCheck_1290_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1278_);
                        lean_inc(v_value_1277_);
                        lean_inc(v_key_1276_);
                        lean_dec(v_x_1275_);
                        v___x_1280_ = lean_box(0);
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
                        lean_ctor_set(v___x_1280_, 2, v___x_1283_);
                        v___x_1285_ = v___x_1280_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_key_1276_);
                        lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_value_1277_);
                        lean_ctor_set(v_reuseFailAlloc_1286_, 2, v___x_1283_);
                        v___x_1285_ = v_reuseFailAlloc_1286_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_1277_);
                    lean_dec(v_key_1276_);
                    if v_isShared_1281_ == 0 {
                        lean_ctor_set(v___x_1280_, 1, v_b_1274_);
                        lean_ctor_set(v___x_1280_, 0, v_a_1273_);
                        v___x_1288_ = v___x_1280_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1273_);
                        lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_b_1274_);
                        lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_tail_1278_);
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
    mut v_m_1291_: *mut LeanObject,
    mut v_a_1292_: *mut LeanObject,
    mut v_b_1293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1298_: u8 = 0;
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: u8 = 0;
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: u8 = 0;
    let mut v_val_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1294_ = lean_ctor_get(v_m_1291_, 0);
                v_buckets_1295_ = lean_ctor_get(v_m_1291_, 1);
                v_isSharedCheck_1338_ = (!lean_is_exclusive(v_m_1291_)) as u8;
                if v_isSharedCheck_1338_ == 0 {
                    v___x_1297_ = v_m_1291_;
                    v_isShared_1298_ = v_isSharedCheck_1338_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_1295_);
                    lean_inc(v_size_1294_);
                    lean_dec(v_m_1291_);
                    v___x_1297_ = lean_box(0);
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
                    v___x_1314_ = lean_unsigned_to_nat(1);
                    v_size_x27_1315_ = lean_nat_add(v_size_1294_, v___x_1314_);
                    lean_dec(v_size_1294_);
                    lean_inc(v_bkt_1312_);
                    v___x_1316_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1316_, 0, v_a_1292_);
                    lean_ctor_set(v___x_1316_, 1, v_b_1293_);
                    lean_ctor_set(v___x_1316_, 2, v_bkt_1312_);
                    v_buckets_x27_1317_ =
                        lean_array_uset(v_buckets_1295_, v___x_1311_, v___x_1316_);
                    v___x_1318_ = lean_unsigned_to_nat(4);
                    v___x_1319_ = lean_nat_mul(v_size_x27_1315_, v___x_1318_);
                    v___x_1320_ = lean_unsigned_to_nat(3);
                    v___x_1321_ = lean_nat_div(v___x_1319_, v___x_1320_);
                    lean_dec(v___x_1319_);
                    v___x_1322_ = lean_array_get_size(v_buckets_x27_1317_);
                    v___x_1323_ = lean_nat_dec_le(v___x_1321_, v___x_1322_);
                    lean_dec(v___x_1321_);
                    if v___x_1323_ == 0 {
                        v_val_1324_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12___redArg(v_buckets_x27_1317_);
                        if v_isShared_1298_ == 0 {
                            lean_ctor_set(v___x_1297_, 1, v_val_1324_);
                            lean_ctor_set(v___x_1297_, 0, v_size_x27_1315_);
                            v___x_1326_ = v___x_1297_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_size_x27_1315_);
                            lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_val_1324_);
                            v___x_1326_ = v_reuseFailAlloc_1327_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1298_ == 0 {
                            lean_ctor_set(v___x_1297_, 1, v_buckets_x27_1317_);
                            lean_ctor_set(v___x_1297_, 0, v_size_x27_1315_);
                            v___x_1329_ = v___x_1297_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_size_x27_1315_);
                            lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_buckets_x27_1317_);
                            v___x_1329_ = v_reuseFailAlloc_1330_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1312_);
                    v___x_1331_ = lean_box(0);
                    v_buckets_x27_1332_ =
                        lean_array_uset(v_buckets_1295_, v___x_1311_, v___x_1331_);
                    v___x_1333_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__13___redArg(v_a_1292_, v_b_1293_, v_bkt_1312_);
                    v___x_1334_ = lean_array_uset(v_buckets_x27_1332_, v___x_1311_, v___x_1333_);
                    if v_isShared_1298_ == 0 {
                        lean_ctor_set(v___x_1297_, 1, v___x_1334_);
                        v___x_1336_ = v___x_1297_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_size_1294_);
                        lean_ctor_set(v_reuseFailAlloc_1337_, 1, v___x_1334_);
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
    mut v_a_1339_: *mut LeanObject,
    mut v_e_1340_: *mut LeanObject,
    mut v_a_1341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    v___x_1343_ = lean_st_ref_take(v_a_1339_);
    v___x_1344_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7___redArg(v___x_1343_, v_e_1340_, v_a_1341_);
    v___x_1345_ = lean_st_ref_set(v_a_1339_, v___x_1344_);
    v___x_1346_ = lean_box(0);
    return v___x_1346_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__2___boxed(
    mut v_a_1347_: *mut LeanObject,
    mut v_e_1348_: *mut LeanObject,
    mut v_a_1349_: *mut LeanObject,
    mut v___y_1350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1351_: *mut LeanObject = core::ptr::null_mut();
    v_res_1351_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__2(v_a_1347_, v_e_1348_, v_a_1349_);
    lean_dec(v_a_1347_);
    return v_res_1351_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__2(
    mut v_pre_1353_: *mut LeanObject,
    mut v_post_1354_: *mut LeanObject,
    mut v_sz_1355_: usize,
    mut v_i_1356_: usize,
    mut v_bs_1357_: *mut LeanObject,
    mut v___y_1358_: *mut LeanObject,
    mut v___y_1359_: *mut LeanObject,
    mut v___y_1360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1362_: u8 = 0;
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: usize = 0;
    let mut v___x_1370_: usize = 0;
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1376_: u8 = 0;
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1362_ = lean_usize_dec_lt(v_i_1356_, v_sz_1355_);
                if v___x_1362_ == 0 {
                    lean_dec_ref(v_post_1354_);
                    lean_dec_ref(v_pre_1353_);
                    v___x_1363_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1363_, 0, v_bs_1357_);
                    return v___x_1363_;
                } else {
                    v_v_1364_ = lean_array_uget_borrowed(v_bs_1357_, v_i_1356_);
                    lean_inc(v_v_1364_);
                    lean_inc_ref(v_post_1354_);
                    lean_inc_ref(v_pre_1353_);
                    v___x_1365_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1353_, v_post_1354_, v_v_1364_, v___y_1358_, v___y_1359_, v___y_1360_);
                    if lean_obj_tag(v___x_1365_) == 0 {
                        v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
                        lean_inc(v_a_1366_);
                        lean_dec_ref_known(v___x_1365_, 1);
                        v___x_1367_ = lean_unsigned_to_nat(0);
                        v_bs_x27_1368_ = lean_array_uset(v_bs_1357_, v_i_1356_, v___x_1367_);
                        v___x_1369_ = 1usize;
                        v___x_1370_ = lean_usize_add(v_i_1356_, v___x_1369_);
                        v___x_1371_ = lean_array_uset(v_bs_x27_1368_, v_i_1356_, v_a_1366_);
                        v_i_1356_ = v___x_1370_;
                        v_bs_1357_ = v___x_1371_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_1357_);
                        lean_dec_ref(v_post_1354_);
                        lean_dec_ref(v_pre_1353_);
                        v_a_1373_ = lean_ctor_get(v___x_1365_, 0);
                        v_isSharedCheck_1380_ = (!lean_is_exclusive(v___x_1365_)) as u8;
                        if v_isSharedCheck_1380_ == 0 {
                            v___x_1375_ = v___x_1365_;
                            v_isShared_1376_ = v_isSharedCheck_1380_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1373_);
                            lean_dec(v___x_1365_);
                            v___x_1375_ = lean_box(0);
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
                    v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
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
    mut v_pre_1381_: *mut LeanObject,
    mut v_post_1382_: *mut LeanObject,
    mut v_x_1383_: *mut LeanObject,
    mut v_x_1384_: *mut LeanObject,
    mut v_x_1385_: *mut LeanObject,
    mut v___y_1386_: *mut LeanObject,
    mut v___y_1387_: *mut LeanObject,
    mut v___y_1388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1398_: usize = 0;
    let mut v___x_1399_: usize = 0;
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1411_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1383_) == 5 {
                    v_fn_1390_ = lean_ctor_get(v_x_1383_, 0);
                    lean_inc_ref(v_fn_1390_);
                    v_arg_1391_ = lean_ctor_get(v_x_1383_, 1);
                    lean_inc_ref(v_arg_1391_);
                    lean_dec_ref_known(v_x_1383_, 2);
                    v___x_1392_ = lean_array_set(v_x_1384_, v_x_1385_, v_arg_1391_);
                    v___x_1393_ = lean_unsigned_to_nat(1);
                    v___x_1394_ = lean_nat_sub(v_x_1385_, v___x_1393_);
                    lean_dec(v_x_1385_);
                    v_x_1383_ = v_fn_1390_;
                    v_x_1384_ = v___x_1392_;
                    v_x_1385_ = v___x_1394_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_1385_);
                    lean_inc_ref(v_post_1382_);
                    lean_inc_ref(v_pre_1381_);
                    v___x_1396_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1381_, v_post_1382_, v_x_1383_, v___y_1386_, v___y_1387_, v___y_1388_);
                    if lean_obj_tag(v___x_1396_) == 0 {
                        v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
                        lean_inc(v_a_1397_);
                        lean_dec_ref_known(v___x_1396_, 1);
                        v_sz_1398_ = lean_array_size(v_x_1384_);
                        v___x_1399_ = 0usize;
                        lean_inc_ref(v_post_1382_);
                        lean_inc_ref(v_pre_1381_);
                        v___x_1400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__2(v_pre_1381_, v_post_1382_, v_sz_1398_, v___x_1399_, v_x_1384_, v___y_1386_, v___y_1387_, v___y_1388_);
                        if lean_obj_tag(v___x_1400_) == 0 {
                            v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
                            lean_inc(v_a_1401_);
                            lean_dec_ref_known(v___x_1400_, 1);
                            v___x_1402_ = l_Lean_mkAppN(v_a_1397_, v_a_1401_);
                            lean_dec(v_a_1401_);
                            v___x_1403_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1381_, v_post_1382_, v___x_1402_, v___y_1386_, v___y_1387_, v___y_1388_);
                            return v___x_1403_;
                        } else {
                            lean_dec(v_a_1397_);
                            lean_dec_ref(v_post_1382_);
                            lean_dec_ref(v_pre_1381_);
                            v_a_1404_ = lean_ctor_get(v___x_1400_, 0);
                            v_isSharedCheck_1411_ = (!lean_is_exclusive(v___x_1400_)) as u8;
                            if v_isSharedCheck_1411_ == 0 {
                                v___x_1406_ = v___x_1400_;
                                v_isShared_1407_ = v_isSharedCheck_1411_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1404_);
                                lean_dec(v___x_1400_);
                                v___x_1406_ = lean_box(0);
                                v_isShared_1407_ = v_isSharedCheck_1411_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_x_1384_);
                        lean_dec_ref(v_post_1382_);
                        lean_dec_ref(v_pre_1381_);
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
                    v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
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
    mut v___x_1412_: *mut LeanObject,
    mut v_pre_1413_: *mut LeanObject,
    mut v_e_1414_: *mut LeanObject,
    mut v_post_1415_: *mut LeanObject,
    mut v___y_1416_: *mut LeanObject,
    mut v___y_1417_: *mut LeanObject,
    mut v___y_1418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1423_: u8 = 0;
    let mut v___y_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1428_: u8 = 0;
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: usize = 0;
    let mut v___x_1432_: usize = 0;
    let mut v___x_1433_: u8 = 0;
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1440_: u8 = 0;
    let mut v___y_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1443_: u8 = 0;
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1452_: u8 = 0;
    let mut v___y_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1456_: u8 = 0;
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: u8 = 0;
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v___y_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1474_: u8 = 0;
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: usize = 0;
    let mut v___x_1480_: usize = 0;
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: usize = 0;
    let mut v___x_1483_: usize = 0;
    let mut v___x_1484_: u8 = 0;
    let mut v_binderName_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1488_: u8 = 0;
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: usize = 0;
    let mut v___x_1494_: usize = 0;
    let mut v___x_1495_: u8 = 0;
    let mut v___x_1496_: usize = 0;
    let mut v___x_1497_: usize = 0;
    let mut v___x_1498_: u8 = 0;
    let mut v_declName_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_1503_: u8 = 0;
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: usize = 0;
    let mut v___x_1511_: usize = 0;
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1513_: usize = 0;
    let mut v___x_1514_: usize = 0;
    let mut v___x_1515_: u8 = 0;
    let mut v_dummy_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: usize = 0;
    let mut v___x_1527_: usize = 0;
    let mut v___x_1528_: u8 = 0;
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: usize = 0;
    let mut v___x_1538_: usize = 0;
    let mut v___x_1539_: u8 = 0;
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1554_: u8 = 0;
    let mut v_a_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1558_: u8 = 0;
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1562_: u8 = 0;
    let mut v_a_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1566_: u8 = 0;
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1463_ = l_Lean_Core_checkSystem(v___x_1412_, v___y_1417_, v___y_1418_);
                if lean_obj_tag(v___x_1463_) == 0 {
                    lean_dec_ref_known(v___x_1463_, 1);
                    lean_inc_ref(v_pre_1413_);
                    lean_inc(v___y_1418_);
                    lean_inc_ref(v___y_1417_);
                    lean_inc_ref(v_e_1414_);
                    v___x_1464_ = lean_apply_4(
                        v_pre_1413_,
                        v_e_1414_,
                        v___y_1417_,
                        v___y_1418_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1464_) == 0 {
                        v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
                        v_isSharedCheck_1554_ = (!lean_is_exclusive(v___x_1464_)) as u8;
                        if v_isSharedCheck_1554_ == 0 {
                            v___x_1467_ = v___x_1464_;
                            v_isShared_1468_ = v_isSharedCheck_1554_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_1465_);
                            lean_dec(v___x_1464_);
                            v___x_1467_ = lean_box(0);
                            v_isShared_1468_ = v_isSharedCheck_1554_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_post_1415_);
                        lean_dec_ref(v_e_1414_);
                        lean_dec_ref(v_pre_1413_);
                        v_a_1555_ = lean_ctor_get(v___x_1464_, 0);
                        v_isSharedCheck_1562_ = (!lean_is_exclusive(v___x_1464_)) as u8;
                        if v_isSharedCheck_1562_ == 0 {
                            v___x_1557_ = v___x_1464_;
                            v_isShared_1558_ = v_isSharedCheck_1562_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1555_);
                            lean_dec(v___x_1464_);
                            v___x_1557_ = lean_box(0);
                            v_isShared_1558_ = v_isSharedCheck_1562_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_post_1415_);
                    lean_dec_ref(v_e_1414_);
                    lean_dec_ref(v_pre_1413_);
                    v_a_1563_ = lean_ctor_get(v___x_1463_, 0);
                    v_isSharedCheck_1570_ = (!lean_is_exclusive(v___x_1463_)) as u8;
                    if v_isSharedCheck_1570_ == 0 {
                        v___x_1565_ = v___x_1463_;
                        v_isShared_1566_ = v_isSharedCheck_1570_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1563_);
                        lean_dec(v___x_1463_);
                        v___x_1565_ = lean_box(0);
                        v_isShared_1566_ = v_isSharedCheck_1570_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1428_ == 0 {
                    lean_dec_ref(v___y_1427_);
                    lean_dec_ref(v___y_1422_);
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
                    lean_dec_ref(v___y_1427_);
                    v___x_1432_ = lean_ptr_addr(v___y_1425_);
                    v___x_1433_ = lean_usize_dec_eq(v___x_1431_, v___x_1432_);
                    if v___x_1433_ == 0 {
                        lean_dec_ref(v___y_1422_);
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
                        lean_dec_ref(v___y_1426_);
                        lean_dec_ref(v___y_1425_);
                        lean_dec_ref(v___y_1424_);
                        lean_dec(v___y_1421_);
                        v___x_1436_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___y_1422_, v___y_1416_, v___y_1417_, v___y_1418_);
                        return v___x_1436_;
                    }
                }
            }
            2 => {
                if v___y_1443_ == 0 {
                    lean_dec_ref(v___y_1439_);
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
                        lean_dec_ref(v___y_1439_);
                        v___x_1447_ = l_Lean_Expr_lam___override(
                            v___y_1438_,
                            v___y_1442_,
                            v___y_1441_,
                            v___y_1440_,
                        );
                        v___x_1448_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___x_1447_, v___y_1416_, v___y_1417_, v___y_1418_);
                        return v___x_1448_;
                    } else {
                        lean_dec_ref(v___y_1442_);
                        lean_dec_ref(v___y_1441_);
                        lean_dec(v___y_1438_);
                        v___x_1449_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___y_1439_, v___y_1416_, v___y_1417_, v___y_1418_);
                        return v___x_1449_;
                    }
                }
            }
            3 => {
                if v___y_1456_ == 0 {
                    lean_dec_ref(v___y_1451_);
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
                        lean_dec_ref(v___y_1451_);
                        v___x_1460_ = l_Lean_Expr_forallE___override(
                            v___y_1453_,
                            v___y_1455_,
                            v___y_1454_,
                            v___y_1452_,
                        );
                        v___x_1461_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___x_1460_, v___y_1416_, v___y_1417_, v___y_1418_);
                        return v___x_1461_;
                    } else {
                        lean_dec_ref(v___y_1455_);
                        lean_dec_ref(v___y_1454_);
                        lean_dec(v___y_1453_);
                        v___x_1462_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___y_1451_, v___y_1416_, v___y_1417_, v___y_1418_);
                        return v___x_1462_;
                    }
                }
            }
            4 => match lean_obj_tag(v_a_1465_) {
                0 => {
                    lean_dec_ref(v_post_1415_);
                    lean_dec_ref(v_e_1414_);
                    lean_dec_ref(v_pre_1413_);
                    v_e_1544_ = lean_ctor_get(v_a_1465_, 0);
                    lean_inc_ref(v_e_1544_);
                    lean_dec_ref_known(v_a_1465_, 1);
                    if v_isShared_1468_ == 0 {
                        lean_ctor_set(v___x_1467_, 0, v_e_1544_);
                        v___x_1546_ = v___x_1467_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_e_1544_);
                        v___x_1546_ = v_reuseFailAlloc_1547_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    lean_del_object(v___x_1467_);
                    lean_dec_ref(v_e_1414_);
                    v_e_1548_ = lean_ctor_get(v_a_1465_, 0);
                    lean_inc_ref(v_e_1548_);
                    lean_dec_ref_known(v_a_1465_, 1);
                    lean_inc_ref(v_post_1415_);
                    lean_inc_ref(v_pre_1413_);
                    v___x_1549_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_e_1548_, v___y_1416_, v___y_1417_, v___y_1418_);
                    if lean_obj_tag(v___x_1549_) == 0 {
                        v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
                        lean_inc(v_a_1550_);
                        lean_dec_ref_known(v___x_1549_, 1);
                        v___x_1551_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v_a_1550_, v___y_1416_, v___y_1417_, v___y_1418_);
                        return v___x_1551_;
                    } else {
                        lean_dec_ref(v_post_1415_);
                        lean_dec_ref(v_pre_1413_);
                        return v___x_1549_;
                    }
                }
                _ => {
                    lean_del_object(v___x_1467_);
                    v_e_x3f_1552_ = lean_ctor_get(v_a_1465_, 0);
                    lean_inc(v_e_x3f_1552_);
                    lean_dec_ref_known(v_a_1465_, 1);
                    if lean_obj_tag(v_e_x3f_1552_) == 0 {
                        v___y_1470_ = v_e_1414_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec_ref(v_e_1414_);
                        v_val_1553_ = lean_ctor_get(v_e_x3f_1552_, 0);
                        lean_inc(v_val_1553_);
                        lean_dec_ref_known(v_e_x3f_1552_, 1);
                        v___y_1470_ = v_val_1553_;
                        state = 5;
                        continue;
                    }
                }
            },
            5 => match lean_obj_tag(v___y_1470_) {
                7 => {
                    v_binderName_1471_ = lean_ctor_get(v___y_1470_, 0);
                    lean_inc(v_binderName_1471_);
                    v_binderType_1472_ = lean_ctor_get(v___y_1470_, 1);
                    v_body_1473_ = lean_ctor_get(v___y_1470_, 2);
                    v_binderInfo_1474_ = lean_ctor_get_uint8(
                        v___y_1470_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc_ref(v_binderType_1472_);
                    lean_inc_ref(v_post_1415_);
                    lean_inc_ref(v_pre_1413_);
                    v___x_1475_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_binderType_1472_, v___y_1416_, v___y_1417_, v___y_1418_);
                    if lean_obj_tag(v___x_1475_) == 0 {
                        v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
                        lean_inc(v_a_1476_);
                        lean_dec_ref_known(v___x_1475_, 1);
                        lean_inc_ref(v_body_1473_);
                        lean_inc_ref(v_post_1415_);
                        lean_inc_ref(v_pre_1413_);
                        v___x_1477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_body_1473_, v___y_1416_, v___y_1417_, v___y_1418_);
                        if lean_obj_tag(v___x_1477_) == 0 {
                            v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
                            lean_inc(v_a_1478_);
                            lean_dec_ref_known(v___x_1477_, 1);
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
                            lean_dec(v_a_1476_);
                            lean_dec_ref_known(v___y_1470_, 3);
                            lean_dec(v_binderName_1471_);
                            lean_dec_ref(v_post_1415_);
                            lean_dec_ref(v_pre_1413_);
                            return v___x_1477_;
                        }
                    } else {
                        lean_dec_ref_known(v___y_1470_, 3);
                        lean_dec(v_binderName_1471_);
                        lean_dec_ref(v_post_1415_);
                        lean_dec_ref(v_pre_1413_);
                        return v___x_1475_;
                    }
                }
                6 => {
                    v_binderName_1485_ = lean_ctor_get(v___y_1470_, 0);
                    lean_inc(v_binderName_1485_);
                    v_binderType_1486_ = lean_ctor_get(v___y_1470_, 1);
                    v_body_1487_ = lean_ctor_get(v___y_1470_, 2);
                    v_binderInfo_1488_ = lean_ctor_get_uint8(
                        v___y_1470_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc_ref(v_binderType_1486_);
                    lean_inc_ref(v_post_1415_);
                    lean_inc_ref(v_pre_1413_);
                    v___x_1489_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_binderType_1486_, v___y_1416_, v___y_1417_, v___y_1418_);
                    if lean_obj_tag(v___x_1489_) == 0 {
                        v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
                        lean_inc(v_a_1490_);
                        lean_dec_ref_known(v___x_1489_, 1);
                        lean_inc_ref(v_body_1487_);
                        lean_inc_ref(v_post_1415_);
                        lean_inc_ref(v_pre_1413_);
                        v___x_1491_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_body_1487_, v___y_1416_, v___y_1417_, v___y_1418_);
                        if lean_obj_tag(v___x_1491_) == 0 {
                            v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
                            lean_inc(v_a_1492_);
                            lean_dec_ref_known(v___x_1491_, 1);
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
                            lean_dec(v_a_1490_);
                            lean_dec(v_binderName_1485_);
                            lean_dec_ref_known(v___y_1470_, 3);
                            lean_dec_ref(v_post_1415_);
                            lean_dec_ref(v_pre_1413_);
                            return v___x_1491_;
                        }
                    } else {
                        lean_dec(v_binderName_1485_);
                        lean_dec_ref_known(v___y_1470_, 3);
                        lean_dec_ref(v_post_1415_);
                        lean_dec_ref(v_pre_1413_);
                        return v___x_1489_;
                    }
                }
                8 => {
                    v_declName_1499_ = lean_ctor_get(v___y_1470_, 0);
                    lean_inc(v_declName_1499_);
                    v_type_1500_ = lean_ctor_get(v___y_1470_, 1);
                    v_value_1501_ = lean_ctor_get(v___y_1470_, 2);
                    v_body_1502_ = lean_ctor_get(v___y_1470_, 3);
                    lean_inc_ref(v_body_1502_);
                    v_nondep_1503_ = lean_ctor_get_uint8(
                        v___y_1470_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                    );
                    lean_inc_ref(v_type_1500_);
                    lean_inc_ref(v_post_1415_);
                    lean_inc_ref(v_pre_1413_);
                    v___x_1504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_type_1500_, v___y_1416_, v___y_1417_, v___y_1418_);
                    if lean_obj_tag(v___x_1504_) == 0 {
                        v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
                        lean_inc(v_a_1505_);
                        lean_dec_ref_known(v___x_1504_, 1);
                        lean_inc_ref(v_value_1501_);
                        lean_inc_ref(v_post_1415_);
                        lean_inc_ref(v_pre_1413_);
                        v___x_1506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_value_1501_, v___y_1416_, v___y_1417_, v___y_1418_);
                        if lean_obj_tag(v___x_1506_) == 0 {
                            v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
                            lean_inc(v_a_1507_);
                            lean_dec_ref_known(v___x_1506_, 1);
                            lean_inc_ref(v_body_1502_);
                            lean_inc_ref(v_post_1415_);
                            lean_inc_ref(v_pre_1413_);
                            v___x_1508_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_body_1502_, v___y_1416_, v___y_1417_, v___y_1418_);
                            if lean_obj_tag(v___x_1508_) == 0 {
                                v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
                                lean_inc(v_a_1509_);
                                lean_dec_ref_known(v___x_1508_, 1);
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
                                lean_dec(v_a_1507_);
                                lean_dec(v_a_1505_);
                                lean_dec_ref(v_body_1502_);
                                lean_dec(v_declName_1499_);
                                lean_dec_ref_known(v___y_1470_, 4);
                                lean_dec_ref(v_post_1415_);
                                lean_dec_ref(v_pre_1413_);
                                return v___x_1508_;
                            }
                        } else {
                            lean_dec(v_a_1505_);
                            lean_dec_ref(v_body_1502_);
                            lean_dec_ref_known(v___y_1470_, 4);
                            lean_dec(v_declName_1499_);
                            lean_dec_ref(v_post_1415_);
                            lean_dec_ref(v_pre_1413_);
                            return v___x_1506_;
                        }
                    } else {
                        lean_dec_ref(v_body_1502_);
                        lean_dec(v_declName_1499_);
                        lean_dec_ref_known(v___y_1470_, 4);
                        lean_dec_ref(v_post_1415_);
                        lean_dec_ref(v_pre_1413_);
                        return v___x_1504_;
                    }
                }
                5 => {
                    v_dummy_1516_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_preprocess___lam__1___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_preprocess___lam__1___closed__0_once
                        ),
                        _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__0,
                    );
                    v_nargs_1517_ = l_Lean_Expr_getAppNumArgs(v___y_1470_);
                    lean_inc(v_nargs_1517_);
                    v___x_1518_ = lean_mk_array(v_nargs_1517_, v_dummy_1516_);
                    v___x_1519_ = lean_unsigned_to_nat(1);
                    v___x_1520_ = lean_nat_sub(v_nargs_1517_, v___x_1519_);
                    lean_dec(v_nargs_1517_);
                    v___x_1521_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__5(v_pre_1413_, v_post_1415_, v___y_1470_, v___x_1518_, v___x_1520_, v___y_1416_, v___y_1417_, v___y_1418_);
                    return v___x_1521_;
                }
                10 => {
                    v_data_1522_ = lean_ctor_get(v___y_1470_, 0);
                    v_expr_1523_ = lean_ctor_get(v___y_1470_, 1);
                    lean_inc_ref(v_expr_1523_);
                    lean_inc_ref(v_post_1415_);
                    lean_inc_ref(v_pre_1413_);
                    v___x_1524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_expr_1523_, v___y_1416_, v___y_1417_, v___y_1418_);
                    if lean_obj_tag(v___x_1524_) == 0 {
                        v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
                        lean_inc(v_a_1525_);
                        lean_dec_ref_known(v___x_1524_, 1);
                        v___x_1526_ = lean_ptr_addr(v_expr_1523_);
                        v___x_1527_ = lean_ptr_addr(v_a_1525_);
                        v___x_1528_ = lean_usize_dec_eq(v___x_1526_, v___x_1527_);
                        if v___x_1528_ == 0 {
                            lean_inc(v_data_1522_);
                            lean_dec_ref_known(v___y_1470_, 2);
                            v___x_1529_ = l_Lean_Expr_mdata___override(v_data_1522_, v_a_1525_);
                            v___x_1530_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___x_1529_, v___y_1416_, v___y_1417_, v___y_1418_);
                            return v___x_1530_;
                        } else {
                            lean_dec(v_a_1525_);
                            v___x_1531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___y_1470_, v___y_1416_, v___y_1417_, v___y_1418_);
                            return v___x_1531_;
                        }
                    } else {
                        lean_dec_ref_known(v___y_1470_, 2);
                        lean_dec_ref(v_post_1415_);
                        lean_dec_ref(v_pre_1413_);
                        return v___x_1524_;
                    }
                }
                11 => {
                    v_typeName_1532_ = lean_ctor_get(v___y_1470_, 0);
                    v_idx_1533_ = lean_ctor_get(v___y_1470_, 1);
                    v_struct_1534_ = lean_ctor_get(v___y_1470_, 2);
                    lean_inc_ref(v_struct_1534_);
                    lean_inc_ref(v_post_1415_);
                    lean_inc_ref(v_pre_1413_);
                    v___x_1535_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1413_, v_post_1415_, v_struct_1534_, v___y_1416_, v___y_1417_, v___y_1418_);
                    if lean_obj_tag(v___x_1535_) == 0 {
                        v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
                        lean_inc(v_a_1536_);
                        lean_dec_ref_known(v___x_1535_, 1);
                        v___x_1537_ = lean_ptr_addr(v_struct_1534_);
                        v___x_1538_ = lean_ptr_addr(v_a_1536_);
                        v___x_1539_ = lean_usize_dec_eq(v___x_1537_, v___x_1538_);
                        if v___x_1539_ == 0 {
                            lean_inc(v_idx_1533_);
                            lean_inc(v_typeName_1532_);
                            lean_dec_ref_known(v___y_1470_, 3);
                            v___x_1540_ = l_Lean_Expr_proj___override(
                                v_typeName_1532_,
                                v_idx_1533_,
                                v_a_1536_,
                            );
                            v___x_1541_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___x_1540_, v___y_1416_, v___y_1417_, v___y_1418_);
                            return v___x_1541_;
                        } else {
                            lean_dec(v_a_1536_);
                            v___x_1542_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1413_, v_post_1415_, v___y_1470_, v___y_1416_, v___y_1417_, v___y_1418_);
                            return v___x_1542_;
                        }
                    } else {
                        lean_dec_ref_known(v___y_1470_, 3);
                        lean_dec_ref(v_post_1415_);
                        lean_dec_ref(v_pre_1413_);
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
                    v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
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
                    v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
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
    mut v___x_1571_: *mut LeanObject,
    mut v_pre_1572_: *mut LeanObject,
    mut v_e_1573_: *mut LeanObject,
    mut v_post_1574_: *mut LeanObject,
    mut v___y_1575_: *mut LeanObject,
    mut v___y_1576_: *mut LeanObject,
    mut v___y_1577_: *mut LeanObject,
    mut v___y_1578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1579_: *mut LeanObject = core::ptr::null_mut();
    v_res_1579_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__1(v___x_1571_, v_pre_1572_, v_e_1573_, v_post_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
    lean_dec(v___y_1577_);
    lean_dec_ref(v___y_1576_);
    lean_dec(v___y_1575_);
    return v_res_1579_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(
    mut v_pre_1580_: *mut LeanObject,
    mut v_post_1581_: *mut LeanObject,
    mut v_e_1582_: *mut LeanObject,
    mut v_a_1583_: *mut LeanObject,
    mut v___y_1584_: *mut LeanObject,
    mut v___y_1585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1592_: u8 = 0;
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1602_: u8 = 0;
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut v_unused_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1611_: u8 = 0;
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1615_: u8 = 0;
    let mut v_val_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut v_a_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1624_: u8 = 0;
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_1583_);
                v___x_1587_ =
                    lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
                lean_closure_set(v___x_1587_, 0, lean_box(0));
                lean_closure_set(v___x_1587_, 1, lean_box(0));
                lean_closure_set(v___x_1587_, 2, v_a_1583_);
                v___x_1588_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__0(lean_box(0), v___x_1587_, v___y_1584_, v___y_1585_);
                if lean_obj_tag(v___x_1588_) == 0 {
                    v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
                    v_isSharedCheck_1620_ = (!lean_is_exclusive(v___x_1588_)) as u8;
                    if v_isSharedCheck_1620_ == 0 {
                        v___x_1591_ = v___x_1588_;
                        v_isShared_1592_ = v_isSharedCheck_1620_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1589_);
                        lean_dec(v___x_1588_);
                        v___x_1591_ = lean_box(0);
                        v_isShared_1592_ = v_isSharedCheck_1620_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_1582_);
                    lean_dec_ref(v_post_1581_);
                    lean_dec_ref(v_pre_1580_);
                    v_a_1621_ = lean_ctor_get(v___x_1588_, 0);
                    v_isSharedCheck_1628_ = (!lean_is_exclusive(v___x_1588_)) as u8;
                    if v_isSharedCheck_1628_ == 0 {
                        v___x_1623_ = v___x_1588_;
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1621_);
                        lean_dec(v___x_1588_);
                        v___x_1623_ = lean_box(0);
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1593_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4___redArg(v_a_1589_, v_e_1582_);
                lean_dec(v_a_1589_);
                if lean_obj_tag(v___x_1593_) == 0 {
                    lean_del_object(v___x_1591_);
                    v___x_1594_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___closed__0;
                    lean_inc_ref(v_e_1582_);
                    v___f_1595_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__1___boxed as *mut core::ffi::c_void, 8, 4);
                    lean_closure_set(v___f_1595_, 0, v___x_1594_);
                    lean_closure_set(v___f_1595_, 1, v_pre_1580_);
                    lean_closure_set(v___f_1595_, 2, v_e_1582_);
                    lean_closure_set(v___f_1595_, 3, v_post_1581_);
                    v___x_1596_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6___redArg(v___f_1595_, v_a_1583_, v___y_1584_, v___y_1585_);
                    if lean_obj_tag(v___x_1596_) == 0 {
                        v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
                        lean_inc_n(v_a_1597_, 2);
                        lean_dec_ref_known(v___x_1596_, 1);
                        lean_inc(v_a_1583_);
                        v___f_1598_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        lean_closure_set(v___f_1598_, 0, v_a_1583_);
                        lean_closure_set(v___f_1598_, 1, v_e_1582_);
                        lean_closure_set(v___f_1598_, 2, v_a_1597_);
                        v___x_1599_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___lam__0(lean_box(0), v___f_1598_, v___y_1584_, v___y_1585_);
                        if lean_obj_tag(v___x_1599_) == 0 {
                            v_isSharedCheck_1606_ = (!lean_is_exclusive(v___x_1599_)) as u8;
                            if v_isSharedCheck_1606_ == 0 {
                                v_unused_1607_ = lean_ctor_get(v___x_1599_, 0);
                                lean_dec(v_unused_1607_);
                                v___x_1601_ = v___x_1599_;
                                v_isShared_1602_ = v_isSharedCheck_1606_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v___x_1599_);
                                v___x_1601_ = lean_box(0);
                                v_isShared_1602_ = v_isSharedCheck_1606_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1597_);
                            v_a_1608_ = lean_ctor_get(v___x_1599_, 0);
                            v_isSharedCheck_1615_ = (!lean_is_exclusive(v___x_1599_)) as u8;
                            if v_isSharedCheck_1615_ == 0 {
                                v___x_1610_ = v___x_1599_;
                                v_isShared_1611_ = v_isSharedCheck_1615_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_1608_);
                                lean_dec(v___x_1599_);
                                v___x_1610_ = lean_box(0);
                                v_isShared_1611_ = v_isSharedCheck_1615_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_1582_);
                        return v___x_1596_;
                    }
                } else {
                    lean_dec_ref(v_e_1582_);
                    lean_dec_ref(v_post_1581_);
                    lean_dec_ref(v_pre_1580_);
                    v_val_1616_ = lean_ctor_get(v___x_1593_, 0);
                    lean_inc(v_val_1616_);
                    lean_dec_ref_known(v___x_1593_, 1);
                    if v_isShared_1592_ == 0 {
                        lean_ctor_set(v___x_1591_, 0, v_val_1616_);
                        v___x_1618_ = v___x_1591_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_val_1616_);
                        v___x_1618_ = v_reuseFailAlloc_1619_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1602_ == 0 {
                    lean_ctor_set(v___x_1601_, 0, v_a_1597_);
                    v___x_1604_ = v___x_1601_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1597_);
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
                    v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
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
                    v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
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
    mut v_pre_1629_: *mut LeanObject,
    mut v_post_1630_: *mut LeanObject,
    mut v_e_1631_: *mut LeanObject,
    mut v_a_1632_: *mut LeanObject,
    mut v___y_1633_: *mut LeanObject,
    mut v___y_1634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1640_: u8 = 0;
    let mut v_e_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1655_: u8 = 0;
    let mut v_a_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1659_: u8 = 0;
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_post_1630_);
                lean_inc(v___y_1634_);
                lean_inc_ref(v___y_1633_);
                lean_inc_ref(v_e_1631_);
                v___x_1636_ = lean_apply_4(
                    v_post_1630_,
                    v_e_1631_,
                    v___y_1633_,
                    v___y_1634_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1636_) == 0 {
                    v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
                    v_isSharedCheck_1655_ = (!lean_is_exclusive(v___x_1636_)) as u8;
                    if v_isSharedCheck_1655_ == 0 {
                        v___x_1639_ = v___x_1636_;
                        v_isShared_1640_ = v_isSharedCheck_1655_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1637_);
                        lean_dec(v___x_1636_);
                        v___x_1639_ = lean_box(0);
                        v_isShared_1640_ = v_isSharedCheck_1655_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_1631_);
                    lean_dec_ref(v_post_1630_);
                    lean_dec_ref(v_pre_1629_);
                    v_a_1656_ = lean_ctor_get(v___x_1636_, 0);
                    v_isSharedCheck_1663_ = (!lean_is_exclusive(v___x_1636_)) as u8;
                    if v_isSharedCheck_1663_ == 0 {
                        v___x_1658_ = v___x_1636_;
                        v_isShared_1659_ = v_isSharedCheck_1663_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1656_);
                        lean_dec(v___x_1636_);
                        v___x_1658_ = lean_box(0);
                        v_isShared_1659_ = v_isSharedCheck_1663_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match lean_obj_tag(v_a_1637_) {
                0 => {
                    lean_dec_ref(v_e_1631_);
                    lean_dec_ref(v_post_1630_);
                    lean_dec_ref(v_pre_1629_);
                    v_e_1641_ = lean_ctor_get(v_a_1637_, 0);
                    lean_inc_ref(v_e_1641_);
                    lean_dec_ref_known(v_a_1637_, 1);
                    if v_isShared_1640_ == 0 {
                        lean_ctor_set(v___x_1639_, 0, v_e_1641_);
                        v___x_1643_ = v___x_1639_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_e_1641_);
                        v___x_1643_ = v_reuseFailAlloc_1644_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    lean_del_object(v___x_1639_);
                    lean_dec_ref(v_e_1631_);
                    v_e_1645_ = lean_ctor_get(v_a_1637_, 0);
                    lean_inc_ref(v_e_1645_);
                    lean_dec_ref_known(v_a_1637_, 1);
                    v___x_1646_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1629_, v_post_1630_, v_e_1645_, v_a_1632_, v___y_1633_, v___y_1634_);
                    return v___x_1646_;
                }
                _ => {
                    lean_dec_ref(v_post_1630_);
                    lean_dec_ref(v_pre_1629_);
                    v_e_x3f_1647_ = lean_ctor_get(v_a_1637_, 0);
                    lean_inc(v_e_x3f_1647_);
                    lean_dec_ref_known(v_a_1637_, 1);
                    if lean_obj_tag(v_e_x3f_1647_) == 0 {
                        if v_isShared_1640_ == 0 {
                            lean_ctor_set(v___x_1639_, 0, v_e_1631_);
                            v___x_1649_ = v___x_1639_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_e_1631_);
                            v___x_1649_ = v_reuseFailAlloc_1650_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_1631_);
                        v_val_1651_ = lean_ctor_get(v_e_x3f_1647_, 0);
                        lean_inc(v_val_1651_);
                        lean_dec_ref_known(v_e_x3f_1647_, 1);
                        if v_isShared_1640_ == 0 {
                            lean_ctor_set(v___x_1639_, 0, v_val_1651_);
                            v___x_1653_ = v___x_1639_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_val_1651_);
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
                    v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
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
    mut v_pre_1664_: *mut LeanObject,
    mut v_post_1665_: *mut LeanObject,
    mut v_e_1666_: *mut LeanObject,
    mut v_a_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1671_: *mut LeanObject = core::ptr::null_mut();
    v_res_1671_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__3(v_pre_1664_, v_post_1665_, v_e_1666_, v_a_1667_, v___y_1668_, v___y_1669_);
    lean_dec(v___y_1669_);
    lean_dec_ref(v___y_1668_);
    lean_dec(v_a_1667_);
    return v_res_1671_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__2___boxed(
    mut v_pre_1672_: *mut LeanObject,
    mut v_post_1673_: *mut LeanObject,
    mut v_sz_1674_: *mut LeanObject,
    mut v_i_1675_: *mut LeanObject,
    mut v_bs_1676_: *mut LeanObject,
    mut v___y_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
    mut v___y_1680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1681_: usize = 0;
    let mut v_i_boxed_1682_: usize = 0;
    let mut v_res_1683_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1681_ = lean_unbox_usize(v_sz_1674_);
    lean_dec(v_sz_1674_);
    v_i_boxed_1682_ = lean_unbox_usize(v_i_1675_);
    lean_dec(v_i_1675_);
    v_res_1683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__2(v_pre_1672_, v_post_1673_, v_sz_boxed_1681_, v_i_boxed_1682_, v_bs_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
    lean_dec(v___y_1679_);
    lean_dec_ref(v___y_1678_);
    lean_dec(v___y_1677_);
    return v_res_1683_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__5___boxed(
    mut v_pre_1684_: *mut LeanObject,
    mut v_post_1685_: *mut LeanObject,
    mut v_x_1686_: *mut LeanObject,
    mut v_x_1687_: *mut LeanObject,
    mut v_x_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
    mut v___y_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
    mut v___y_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1693_: *mut LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__5(v_pre_1684_, v_post_1685_, v_x_1686_, v_x_1687_, v_x_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
    lean_dec(v___y_1691_);
    lean_dec_ref(v___y_1690_);
    lean_dec(v___y_1689_);
    return v_res_1693_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1___boxed(
    mut v_pre_1694_: *mut LeanObject,
    mut v_post_1695_: *mut LeanObject,
    mut v_e_1696_: *mut LeanObject,
    mut v_a_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
    mut v___y_1700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1701_: *mut LeanObject = core::ptr::null_mut();
    v_res_1701_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1694_, v_post_1695_, v_e_1696_, v_a_1697_, v___y_1698_, v___y_1699_);
    lean_dec(v___y_1699_);
    lean_dec_ref(v___y_1698_);
    lean_dec(v_a_1697_);
    return v_res_1701_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___lam__0(
    mut v_00_u03b1_1702_: *mut LeanObject,
    mut v_x_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
    mut v___y_1705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    v___x_1707_ = lean_apply_1(v_x_1703_, lean_box(0));
    v___x_1708_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1708_, 0, v___x_1707_);
    return v___x_1708_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___lam__0___boxed(
    mut v_00_u03b1_1709_: *mut LeanObject,
    mut v_x_1710_: *mut LeanObject,
    mut v___y_1711_: *mut LeanObject,
    mut v___y_1712_: *mut LeanObject,
    mut v___y_1713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1714_: *mut LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___lam__0(
        v_00_u03b1_1709_,
        v_x_1710_,
        v___y_1711_,
        v___y_1712_,
    );
    lean_dec(v___y_1712_);
    lean_dec_ref(v___y_1711_);
    return v_res_1714_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    v___x_1715_ = lean_box(0);
    v___x_1716_ = lean_unsigned_to_nat(16);
    v___x_1717_ = lean_mk_array(v___x_1716_, v___x_1715_);
    return v___x_1717_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    v___x_1718_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__0_once
        ),
        _init_l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__0,
    );
    v___x_1719_ = lean_unsigned_to_nat(0);
    v___x_1720_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1720_, 0, v___x_1719_);
    lean_ctor_set(v___x_1720_, 1, v___x_1718_);
    return v___x_1720_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    v___x_1721_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__1_once
        ),
        _init_l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__1,
    );
    v___x_1722_ = lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_1722_, 0, lean_box(0));
    lean_closure_set(v___x_1722_, 1, lean_box(0));
    lean_closure_set(v___x_1722_, 2, v___x_1721_);
    return v___x_1722_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1(
    mut v_input_1723_: *mut LeanObject,
    mut v_pre_1724_: *mut LeanObject,
    mut v_post_1725_: *mut LeanObject,
    mut v___y_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1738_: u8 = 0;
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1742_: u8 = 0;
    let mut v_unused_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1729_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__2_once), _init_l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___closed__2);
                v___x_1730_ =
                    l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___lam__0(
                        lean_box(0),
                        v___x_1729_,
                        v___y_1726_,
                        v___y_1727_,
                    );
                v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
                lean_inc(v_a_1731_);
                lean_dec_ref(v___x_1730_);
                v___x_1732_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1(v_pre_1724_, v_post_1725_, v_input_1723_, v_a_1731_, v___y_1726_, v___y_1727_);
                if lean_obj_tag(v___x_1732_) == 0 {
                    v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
                    lean_inc(v_a_1733_);
                    lean_dec_ref_known(v___x_1732_, 1);
                    v___x_1734_ = lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___x_1734_, 0, lean_box(0));
                    lean_closure_set(v___x_1734_, 1, lean_box(0));
                    lean_closure_set(v___x_1734_, 2, v_a_1731_);
                    v___x_1735_ = l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1___lam__0(lean_box(0), v___x_1734_, v___y_1726_, v___y_1727_);
                    v_isSharedCheck_1742_ = (!lean_is_exclusive(v___x_1735_)) as u8;
                    if v_isSharedCheck_1742_ == 0 {
                        v_unused_1743_ = lean_ctor_get(v___x_1735_, 0);
                        lean_dec(v_unused_1743_);
                        v___x_1737_ = v___x_1735_;
                        v_isShared_1738_ = v_isSharedCheck_1742_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1735_);
                        v___x_1737_ = lean_box(0);
                        v_isShared_1738_ = v_isSharedCheck_1742_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1731_);
                    return v___x_1732_;
                }
            }
            1 => {
                if v_isShared_1738_ == 0 {
                    lean_ctor_set(v___x_1737_, 0, v_a_1733_);
                    v___x_1740_ = v___x_1737_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1733_);
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
    mut v_input_1744_: *mut LeanObject,
    mut v_pre_1745_: *mut LeanObject,
    mut v_post_1746_: *mut LeanObject,
    mut v___y_1747_: *mut LeanObject,
    mut v___y_1748_: *mut LeanObject,
    mut v___y_1749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1750_: *mut LeanObject = core::ptr::null_mut();
    v_res_1750_ = l_Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1(
        v_input_1744_,
        v_pre_1745_,
        v_post_1746_,
        v___y_1747_,
        v___y_1748_,
    );
    lean_dec(v___y_1748_);
    lean_dec_ref(v___y_1747_);
    return v_res_1750_;
}
pub unsafe fn l_Lean_Elab_Structural_preprocess(
    mut v_e_1752_: *mut LeanObject,
    mut v_recFnNames_1753_: *mut LeanObject,
    mut v_numFixedParams_1754_: *mut LeanObject,
    mut v_a_1755_: *mut LeanObject,
    mut v_a_1756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_recFnNames_1753_);
    v___x_1758_ = l_Lean_Meta_unfoldIfArgIsAppOf(
        v_recFnNames_1753_,
        v_numFixedParams_1754_,
        v_e_1752_,
        v_a_1755_,
        v_a_1756_,
    );
    if lean_obj_tag(v___x_1758_) == 0 {
        let mut v_a_1759_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1760_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
        v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
        lean_inc(v_a_1759_);
        lean_dec_ref_known(v___x_1758_, 1);
        v___f_1760_ = lean_alloc_closure(
            l_Lean_Elab_Structural_preprocess___lam__0___boxed as *mut core::ffi::c_void,
            5,
            1,
        );
        lean_closure_set(v___f_1760_, 0, v_recFnNames_1753_);
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
        lean_dec_ref(v_recFnNames_1753_);
        return v___x_1758_;
    }
}
pub unsafe fn l_Lean_Elab_Structural_preprocess___boxed(
    mut v_e_1763_: *mut LeanObject,
    mut v_recFnNames_1764_: *mut LeanObject,
    mut v_numFixedParams_1765_: *mut LeanObject,
    mut v_a_1766_: *mut LeanObject,
    mut v_a_1767_: *mut LeanObject,
    mut v_a_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1769_: *mut LeanObject = core::ptr::null_mut();
    v_res_1769_ = l_Lean_Elab_Structural_preprocess(
        v_e_1763_,
        v_recFnNames_1764_,
        v_numFixedParams_1765_,
        v_a_1766_,
        v_a_1767_,
    );
    lean_dec(v_a_1767_);
    lean_dec_ref(v_a_1766_);
    return v_res_1769_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4(
    mut v_00_u03b2_1770_: *mut LeanObject,
    mut v_m_1771_: *mut LeanObject,
    mut v_a_1772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    v___x_1773_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4___redArg(v_m_1771_, v_a_1772_);
    return v___x_1773_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4___boxed(
    mut v_00_u03b2_1774_: *mut LeanObject,
    mut v_m_1775_: *mut LeanObject,
    mut v_a_1776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1777_: *mut LeanObject = core::ptr::null_mut();
    v_res_1777_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4(v_00_u03b2_1774_, v_m_1775_, v_a_1776_);
    lean_dec_ref(v_a_1776_);
    lean_dec_ref(v_m_1775_);
    return v_res_1777_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8(
    mut v_00_u03b1_1778_: *mut LeanObject,
    mut v_ref_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    v___x_1783_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_1779_);
    return v___x_1783_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8___boxed(
    mut v_00_u03b1_1784_: *mut LeanObject,
    mut v_ref_1785_: *mut LeanObject,
    mut v___y_1786_: *mut LeanObject,
    mut v___y_1787_: *mut LeanObject,
    mut v___y_1788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1789_: *mut LeanObject = core::ptr::null_mut();
    v_res_1789_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_1784_, v_ref_1785_, v___y_1786_, v___y_1787_);
    lean_dec(v___y_1787_);
    lean_dec_ref(v___y_1786_);
    return v_res_1789_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9(
    mut v_00_u03b1_1790_: *mut LeanObject,
    mut v___y_1791_: *mut LeanObject,
    mut v___y_1792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    v___x_1794_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___redArg();
    return v___x_1794_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9___boxed(
    mut v_00_u03b1_1795_: *mut LeanObject,
    mut v___y_1796_: *mut LeanObject,
    mut v___y_1797_: *mut LeanObject,
    mut v___y_1798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1799_: *mut LeanObject = core::ptr::null_mut();
    v_res_1799_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6_spec__9(v_00_u03b1_1795_, v___y_1796_, v___y_1797_);
    lean_dec(v___y_1797_);
    lean_dec_ref(v___y_1796_);
    return v_res_1799_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6(
    mut v_00_u03b1_1800_: *mut LeanObject,
    mut v_x_1801_: *mut LeanObject,
    mut v___y_1802_: *mut LeanObject,
    mut v___y_1803_: *mut LeanObject,
    mut v___y_1804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    v___x_1806_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6___redArg(v_x_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
    return v___x_1806_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6___boxed(
    mut v_00_u03b1_1807_: *mut LeanObject,
    mut v_x_1808_: *mut LeanObject,
    mut v___y_1809_: *mut LeanObject,
    mut v___y_1810_: *mut LeanObject,
    mut v___y_1811_: *mut LeanObject,
    mut v___y_1812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1813_: *mut LeanObject = core::ptr::null_mut();
    v_res_1813_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__6(v_00_u03b1_1807_, v_x_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
    lean_dec(v___y_1811_);
    lean_dec_ref(v___y_1810_);
    lean_dec(v___y_1809_);
    return v_res_1813_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7(
    mut v_00_u03b2_1814_: *mut LeanObject,
    mut v_m_1815_: *mut LeanObject,
    mut v_a_1816_: *mut LeanObject,
    mut v_b_1817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    v___x_1818_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7___redArg(v_m_1815_, v_a_1816_, v_b_1817_);
    return v___x_1818_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5(
    mut v_00_u03b2_1819_: *mut LeanObject,
    mut v_a_1820_: *mut LeanObject,
    mut v_x_1821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    v___x_1822_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5___redArg(v_a_1820_, v_x_1821_);
    return v___x_1822_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5___boxed(
    mut v_00_u03b2_1823_: *mut LeanObject,
    mut v_a_1824_: *mut LeanObject,
    mut v_x_1825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1826_: *mut LeanObject = core::ptr::null_mut();
    v_res_1826_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__4_spec__5(v_00_u03b2_1823_, v_a_1824_, v_x_1825_);
    lean_dec(v_x_1825_);
    lean_dec_ref(v_a_1824_);
    return v_res_1826_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__11(
    mut v_00_u03b2_1827_: *mut LeanObject,
    mut v_a_1828_: *mut LeanObject,
    mut v_x_1829_: *mut LeanObject,
) -> u8 {
    let mut v___x_1830_: u8 = 0;
    v___x_1830_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__11___redArg(v_a_1828_, v_x_1829_);
    return v___x_1830_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__11___boxed(
    mut v_00_u03b2_1831_: *mut LeanObject,
    mut v_a_1832_: *mut LeanObject,
    mut v_x_1833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1834_: u8 = 0;
    let mut v_r_1835_: *mut LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_1831_, v_a_1832_, v_x_1833_);
    lean_dec(v_x_1833_);
    lean_dec_ref(v_a_1832_);
    v_r_1835_ = lean_box((v_res_1834_) as usize);
    return v_r_1835_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12(
    mut v_00_u03b2_1836_: *mut LeanObject,
    mut v_data_1837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    v___x_1838_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12___redArg(v_data_1837_);
    return v___x_1838_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__13(
    mut v_00_u03b2_1839_: *mut LeanObject,
    mut v_a_1840_: *mut LeanObject,
    mut v_b_1841_: *mut LeanObject,
    mut v_x_1842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    v___x_1843_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__13___redArg(v_a_1840_, v_b_1841_, v_x_1842_);
    return v___x_1843_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13(
    mut v_00_u03b2_1844_: *mut LeanObject,
    mut v_i_1845_: *mut LeanObject,
    mut v_source_1846_: *mut LeanObject,
    mut v_target_1847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    v___x_1848_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v_i_1845_, v_source_1846_, v_target_1847_);
    return v___x_1848_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14(
    mut v_00_u03b2_1849_: *mut LeanObject,
    mut v_x_1850_: *mut LeanObject,
    mut v_x_1851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    v___x_1852_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_Structural_preprocess_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_x_1850_, v_x_1851_);
    return v___x_1852_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_Structural_Preprocess(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_RecAppSyntax(builtin);
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
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_Structural_Preprocess(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_Structural_Preprocess(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_RecAppSyntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Preprocess(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_Structural_Preprocess(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_Structural_Preprocess(builtin);
}
