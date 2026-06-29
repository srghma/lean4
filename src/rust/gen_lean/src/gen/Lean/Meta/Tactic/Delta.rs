// Lean compiler output
// Module: Lean.Meta.Tactic.Delta
// Imports: Lean.Meta.Tactic.Replace Lean.Meta.Transform
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_set, lean_array_size,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_ptr_addr, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Prelude::{l_Lean_maxRecDepthErrorMessage, l_List_lengthTR___redArg};
use crate::r#gen::Init::System::CancelToken::l_IO_CancelToken_isSet;
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_mkRef___boxed};
use crate::r#gen::Lean::CoreM::{l_Lean_Core_checkSystem, l_Lean_Core_instantiateValueLevelParams};
use crate::r#gen::Lean::Declaration::{
    l_Lean_ConstantInfo_hasValue, l_Lean_ConstantInfo_levelParams, l_Lean_ConstantInfo_name,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::r#gen::Lean::Exception::l_Lean_interruptExceptionId;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux, l_Lean_Expr_betaRev,
    l_Lean_Expr_forallE___override, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_lam___override, l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override,
    l_Lean_Expr_proj___override, l_Lean_Expr_sort___override, l_Lean_ExprStructEq_beq,
    l_Lean_ExprStructEq_hash, l_Lean_instBEqBinderInfo_beq, l_Lean_mkAppN,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getType___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    initialize_Lean_Meta_Tactic_Replace, l_Lean_MVarId_change, l_Lean_MVarId_changeLocalDecl,
    runtime_initialize_Lean_Meta_Tactic_Replace,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getType,
};
use crate::r#gen::Lean::Meta::Transform::{
    initialize_Lean_Meta_Transform, runtime_initialize_Lean_Meta_Transform,
};
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_deltaExpand___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_deltaExpand___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_deltaExpand___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_deltaExpand___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_deltaTarget___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [100, 101, 108, 116, 97, 0],
    };
static mut l_Lean_MVarId_deltaTarget___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_deltaTarget___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_deltaTarget___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_deltaTarget___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2820377975091604199 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_deltaTarget___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_deltaTarget___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_delta_x3f(
    mut v_e_1097_: *mut crate::leanh::LeanObject,
    mut v_p_1098_: *mut crate::leanh::LeanObject,
    mut v_allowOpaque_1099_: u8,
    mut v_a_1100_: *mut crate::leanh::LeanObject,
    mut v_a_1101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: u8 = 0;
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1119_: u8 = 0;
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: u8 = 0;
    let mut v___x_1123_: u8 = 0;
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: u8 = 0;
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1132_: u8 = 0;
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1143_: u8 = 0;
    let mut v_a_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1147_: u8 = 0;
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1151_: u8 = 0;
    let mut v_isSharedCheck_1152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1106_ = l_Lean_Expr_getAppFn(v_e_1097_);
                if crate::leanh::lean_obj_tag(v___x_1106_) == 4 {
                    v_declName_1107_ = crate::leanh::lean_ctor_get(v___x_1106_, 0);
                    crate::leanh::lean_inc(v_declName_1107_);
                    v_us_1108_ = crate::leanh::lean_ctor_get(v___x_1106_, 1);
                    crate::leanh::lean_inc(v_us_1108_);
                    crate::leanh::lean_dec_ref_known(v___x_1106_, 2);
                    v___x_1109_ = lean_st_ref_get(v_a_1101_);
                    v_env_1113_ = crate::leanh::lean_ctor_get(v___x_1109_, 0);
                    crate::leanh::lean_inc_ref(v_env_1113_);
                    crate::leanh::lean_dec(v___x_1109_);
                    v___x_1114_ = 0;
                    v___x_1115_ =
                        l_Lean_Environment_find_x3f(v_env_1113_, v_declName_1107_, v___x_1114_);
                    if crate::leanh::lean_obj_tag(v___x_1115_) == 0 {
                        crate::leanh::lean_dec(v_us_1108_);
                        crate::leanh::lean_dec_ref(v_p_1098_);
                        crate::leanh::lean_dec_ref(v_e_1097_);
                        state = 1;
                        continue;
                    } else {
                        v_val_1116_ = crate::leanh::lean_ctor_get(v___x_1115_, 0);
                        v_isSharedCheck_1152_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1115_)) as u8;
                        if v_isSharedCheck_1152_ == 0 {
                            v___x_1118_ = v___x_1115_;
                            v_isShared_1119_ = v_isSharedCheck_1152_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1116_);
                            crate::leanh::lean_dec(v___x_1115_);
                            v___x_1118_ = crate::leanh::lean_box(0);
                            v_isShared_1119_ = v_isSharedCheck_1152_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1106_);
                    crate::leanh::lean_dec_ref(v_p_1098_);
                    crate::leanh::lean_dec_ref(v_e_1097_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1104_ = crate::leanh::lean_box(0);
                v___x_1105_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1105_, 0, v___x_1104_);
                return v___x_1105_;
            }
            2 => {
                v___x_1111_ = crate::leanh::lean_box(0);
                v___x_1112_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1112_, 0, v___x_1111_);
                return v___x_1112_;
            }
            3 => {
                v___x_1120_ = l_Lean_ConstantInfo_name(v_val_1116_);
                v___x_1121_ = crate::leanh::lean_apply_1(v_p_1098_, v___x_1120_);
                v___x_1122_ = (crate::leanh::lean_unbox(v___x_1121_) as u8);
                if v___x_1122_ == 0 {
                    crate::leanh::lean_del_object(v___x_1118_);
                    crate::leanh::lean_dec(v_val_1116_);
                    crate::leanh::lean_dec(v_us_1108_);
                    crate::leanh::lean_dec_ref(v_e_1097_);
                    state = 2;
                    continue;
                } else {
                    v___x_1123_ = l_Lean_ConstantInfo_hasValue(v_val_1116_, v_allowOpaque_1099_);
                    if v___x_1123_ == 0 {
                        crate::leanh::lean_del_object(v___x_1118_);
                        crate::leanh::lean_dec(v_val_1116_);
                        crate::leanh::lean_dec(v_us_1108_);
                        crate::leanh::lean_dec_ref(v_e_1097_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1124_ = l_Lean_ConstantInfo_levelParams(v_val_1116_);
                        v___x_1125_ = l_List_lengthTR___redArg(v___x_1124_);
                        crate::leanh::lean_dec(v___x_1124_);
                        v___x_1126_ = l_List_lengthTR___redArg(v_us_1108_);
                        v___x_1127_ = lean_nat_dec_eq(v___x_1125_, v___x_1126_);
                        crate::leanh::lean_dec(v___x_1126_);
                        crate::leanh::lean_dec(v___x_1125_);
                        if v___x_1127_ == 0 {
                            crate::leanh::lean_del_object(v___x_1118_);
                            crate::leanh::lean_dec(v_val_1116_);
                            crate::leanh::lean_dec(v_us_1108_);
                            crate::leanh::lean_dec_ref(v_e_1097_);
                            state = 2;
                            continue;
                        } else {
                            v___x_1128_ = l_Lean_Core_instantiateValueLevelParams(
                                v_val_1116_,
                                v_us_1108_,
                                v_allowOpaque_1099_,
                                v_a_1100_,
                                v_a_1101_,
                            );
                            crate::leanh::lean_dec(v_val_1116_);
                            if crate::leanh::lean_obj_tag(v___x_1128_) == 0 {
                                v_a_1129_ = crate::leanh::lean_ctor_get(v___x_1128_, 0);
                                v_isSharedCheck_1143_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1128_)) as u8;
                                if v_isSharedCheck_1143_ == 0 {
                                    v___x_1131_ = v___x_1128_;
                                    v_isShared_1132_ = v_isSharedCheck_1143_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1129_);
                                    crate::leanh::lean_dec(v___x_1128_);
                                    v___x_1131_ = crate::leanh::lean_box(0);
                                    v_isShared_1132_ = v_isSharedCheck_1143_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_1118_);
                                crate::leanh::lean_dec_ref(v_e_1097_);
                                v_a_1144_ = crate::leanh::lean_ctor_get(v___x_1128_, 0);
                                v_isSharedCheck_1151_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1128_)) as u8;
                                if v_isSharedCheck_1151_ == 0 {
                                    v___x_1146_ = v___x_1128_;
                                    v_isShared_1147_ = v_isSharedCheck_1151_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1144_);
                                    crate::leanh::lean_dec(v___x_1128_);
                                    v___x_1146_ = crate::leanh::lean_box(0);
                                    v_isShared_1147_ = v_isSharedCheck_1151_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            4 => {
                v___x_1133_ = l_Lean_Expr_getAppNumArgs(v_e_1097_);
                v___x_1134_ = lean_mk_empty_array_with_capacity(v___x_1133_);
                crate::leanh::lean_dec(v___x_1133_);
                v___x_1135_ =
                    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_1097_, v___x_1134_);
                v___x_1136_ = l_Lean_Expr_betaRev(v_a_1129_, v___x_1135_, v___x_1123_, v___x_1114_);
                crate::leanh::lean_dec_ref(v___x_1135_);
                if v_isShared_1119_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1118_, 0, v___x_1136_);
                    v___x_1138_ = v___x_1118_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1142_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1136_);
                    v___x_1138_ = v_reuseFailAlloc_1142_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1132_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1131_, 0, v___x_1138_);
                    v___x_1140_ = v___x_1131_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1141_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
                    v___x_1140_ = v_reuseFailAlloc_1141_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1140_;
            }
            7 => {
                if v_isShared_1147_ == 0 {
                    v___x_1149_ = v___x_1146_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1150_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
                    v___x_1149_ = v_reuseFailAlloc_1150_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1149_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_delta_x3f___boxed(
    mut v_e_1153_: *mut crate::leanh::LeanObject,
    mut v_p_1154_: *mut crate::leanh::LeanObject,
    mut v_allowOpaque_1155_: *mut crate::leanh::LeanObject,
    mut v_a_1156_: *mut crate::leanh::LeanObject,
    mut v_a_1157_: *mut crate::leanh::LeanObject,
    mut v_a_1158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowOpaque_boxed_1159_: u8 = 0;
    let mut v_res_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowOpaque_boxed_1159_ = (crate::leanh::lean_unbox(v_allowOpaque_1155_) as u8);
    v_res_1160_ = l_Lean_Meta_delta_x3f(
        v_e_1153_,
        v_p_1154_,
        v_allowOpaque_boxed_1159_,
        v_a_1156_,
        v_a_1157_,
    );
    crate::leanh::lean_dec(v_a_1157_);
    crate::leanh::lean_dec_ref(v_a_1156_);
    return v_res_1160_;
}
pub unsafe fn l_Lean_Meta_deltaExpand___lam__0(
    mut v_p_1161_: *mut crate::leanh::LeanObject,
    mut v_allowOpaque_1162_: u8,
    mut v_e_1163_: *mut crate::leanh::LeanObject,
    mut v___y_1164_: *mut crate::leanh::LeanObject,
    mut v___y_1165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1171_: u8 = 0;
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1179_: u8 = 0;
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1186_: u8 = 0;
    let mut v_isSharedCheck_1187_: u8 = 0;
    let mut v_a_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1191_: u8 = 0;
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1167_ = l_Lean_Meta_delta_x3f(
                    v_e_1163_,
                    v_p_1161_,
                    v_allowOpaque_1162_,
                    v___y_1164_,
                    v___y_1165_,
                );
                if crate::leanh::lean_obj_tag(v___x_1167_) == 0 {
                    v_a_1168_ = crate::leanh::lean_ctor_get(v___x_1167_, 0);
                    v_isSharedCheck_1187_ = (!crate::leanh::lean_is_exclusive(v___x_1167_)) as u8;
                    if v_isSharedCheck_1187_ == 0 {
                        v___x_1170_ = v___x_1167_;
                        v_isShared_1171_ = v_isSharedCheck_1187_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1168_);
                        crate::leanh::lean_dec(v___x_1167_);
                        v___x_1170_ = crate::leanh::lean_box(0);
                        v_isShared_1171_ = v_isSharedCheck_1187_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1188_ = crate::leanh::lean_ctor_get(v___x_1167_, 0);
                    v_isSharedCheck_1195_ = (!crate::leanh::lean_is_exclusive(v___x_1167_)) as u8;
                    if v_isSharedCheck_1195_ == 0 {
                        v___x_1190_ = v___x_1167_;
                        v_isShared_1191_ = v_isSharedCheck_1195_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1188_);
                        crate::leanh::lean_dec(v___x_1167_);
                        v___x_1190_ = crate::leanh::lean_box(0);
                        v_isShared_1191_ = v_isSharedCheck_1195_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1168_) == 0 {
                    v___x_1172_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1172_, 0, v_a_1168_);
                    if v_isShared_1171_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1170_, 0, v___x_1172_);
                        v___x_1174_ = v___x_1170_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
                        v___x_1174_ = v_reuseFailAlloc_1175_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_1176_ = crate::leanh::lean_ctor_get(v_a_1168_, 0);
                    v_isSharedCheck_1186_ = (!crate::leanh::lean_is_exclusive(v_a_1168_)) as u8;
                    if v_isSharedCheck_1186_ == 0 {
                        v___x_1178_ = v_a_1168_;
                        v_isShared_1179_ = v_isSharedCheck_1186_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1176_);
                        crate::leanh::lean_dec(v_a_1168_);
                        v___x_1178_ = crate::leanh::lean_box(0);
                        v_isShared_1179_ = v_isSharedCheck_1186_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1174_;
            }
            3 => {
                if v_isShared_1179_ == 0 {
                    v___x_1181_ = v___x_1178_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1185_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_val_1176_);
                    v___x_1181_ = v_reuseFailAlloc_1185_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1171_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1170_, 0, v___x_1181_);
                    v___x_1183_ = v___x_1170_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1184_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
                    v___x_1183_ = v_reuseFailAlloc_1184_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1183_;
            }
            6 => {
                if v_isShared_1191_ == 0 {
                    v___x_1193_ = v___x_1190_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1194_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
                    v___x_1193_ = v_reuseFailAlloc_1194_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1193_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_deltaExpand___lam__0___boxed(
    mut v_p_1196_: *mut crate::leanh::LeanObject,
    mut v_allowOpaque_1197_: *mut crate::leanh::LeanObject,
    mut v_e_1198_: *mut crate::leanh::LeanObject,
    mut v___y_1199_: *mut crate::leanh::LeanObject,
    mut v___y_1200_: *mut crate::leanh::LeanObject,
    mut v___y_1201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowOpaque_boxed_1202_: u8 = 0;
    let mut v_res_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowOpaque_boxed_1202_ = (crate::leanh::lean_unbox(v_allowOpaque_1197_) as u8);
    v_res_1203_ = l_Lean_Meta_deltaExpand___lam__0(
        v_p_1196_,
        v_allowOpaque_boxed_1202_,
        v_e_1198_,
        v___y_1199_,
        v___y_1200_,
    );
    crate::leanh::lean_dec(v___y_1200_);
    crate::leanh::lean_dec_ref(v___y_1199_);
    return v_res_1203_;
}
pub unsafe fn l_Lean_Meta_deltaExpand___lam__1(
    mut v_e_1204_: *mut crate::leanh::LeanObject,
    mut v___y_1205_: *mut crate::leanh::LeanObject,
    mut v___y_1206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1208_, 0, v_e_1204_);
    v___x_1209_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1209_, 0, v___x_1208_);
    return v___x_1209_;
}
pub unsafe fn l_Lean_Meta_deltaExpand___lam__1___boxed(
    mut v_e_1210_: *mut crate::leanh::LeanObject,
    mut v___y_1211_: *mut crate::leanh::LeanObject,
    mut v___y_1212_: *mut crate::leanh::LeanObject,
    mut v___y_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1214_ = l_Lean_Meta_deltaExpand___lam__1(v_e_1210_, v___y_1211_, v___y_1212_);
    crate::leanh::lean_dec(v___y_1212_);
    crate::leanh::lean_dec_ref(v___y_1211_);
    return v_res_1214_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(
    mut v_00_u03b1_1215_: *mut crate::leanh::LeanObject,
    mut v_x_1216_: *mut crate::leanh::LeanObject,
    mut v___y_1217_: *mut crate::leanh::LeanObject,
    mut v___y_1218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1220_ = crate::leanh::lean_apply_1(v_x_1216_, crate::leanh::lean_box(0));
    v___x_1221_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1221_, 0, v___x_1220_);
    return v___x_1221_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0___boxed(
    mut v_00_u03b1_1222_: *mut crate::leanh::LeanObject,
    mut v_x_1223_: *mut crate::leanh::LeanObject,
    mut v___y_1224_: *mut crate::leanh::LeanObject,
    mut v___y_1225_: *mut crate::leanh::LeanObject,
    mut v___y_1226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1227_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(v_00_u03b1_1222_, v_x_1223_, v___y_1224_, v___y_1225_);
    crate::leanh::lean_dec(v___y_1225_);
    crate::leanh::lean_dec_ref(v___y_1224_);
    return v_res_1227_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(
    mut v_a_1228_: *mut crate::leanh::LeanObject,
    mut v_x_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: u8 = 0;
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1229_) == 0 {
                    v___x_1230_ = crate::leanh::lean_box(0);
                    return v___x_1230_;
                } else {
                    v_key_1231_ = crate::leanh::lean_ctor_get(v_x_1229_, 0);
                    v_value_1232_ = crate::leanh::lean_ctor_get(v_x_1229_, 1);
                    v_tail_1233_ = crate::leanh::lean_ctor_get(v_x_1229_, 2);
                    v___x_1234_ = l_Lean_ExprStructEq_beq(v_key_1231_, v_a_1228_);
                    if v___x_1234_ == 0 {
                        v_x_1229_ = v_tail_1233_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_1232_);
                        v___x_1236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1236_, 0, v_value_1232_);
                        return v___x_1236_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg___boxed(
    mut v_a_1237_: *mut crate::leanh::LeanObject,
    mut v_x_1238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1239_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1237_, v_x_1238_);
    crate::leanh::lean_dec(v_x_1238_);
    crate::leanh::lean_dec_ref(v_a_1237_);
    return v_res_1239_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(
    mut v_m_1240_: *mut crate::leanh::LeanObject,
    mut v_a_1241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: u64 = 0;
    let mut v___x_1245_: u64 = 0;
    let mut v___x_1246_: u64 = 0;
    let mut v_fold_1247_: u64 = 0;
    let mut v___x_1248_: u64 = 0;
    let mut v___x_1249_: u64 = 0;
    let mut v___x_1250_: u64 = 0;
    let mut v___x_1251_: usize = 0;
    let mut v___x_1252_: usize = 0;
    let mut v___x_1253_: usize = 0;
    let mut v___x_1254_: usize = 0;
    let mut v___x_1255_: usize = 0;
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1242_ = crate::leanh::lean_ctor_get(v_m_1240_, 1);
    v___x_1243_ = lean_array_get_size(v_buckets_1242_);
    v___x_1244_ = l_Lean_ExprStructEq_hash(v_a_1241_);
    v___x_1245_ = 32u64;
    v___x_1246_ = lean_uint64_shift_right(v___x_1244_, v___x_1245_);
    v_fold_1247_ = lean_uint64_xor(v___x_1244_, v___x_1246_);
    v___x_1248_ = 16u64;
    v___x_1249_ = lean_uint64_shift_right(v_fold_1247_, v___x_1248_);
    v___x_1250_ = lean_uint64_xor(v_fold_1247_, v___x_1249_);
    v___x_1251_ = lean_uint64_to_usize(v___x_1250_);
    v___x_1252_ = lean_usize_of_nat(v___x_1243_);
    v___x_1253_ = 1usize;
    v___x_1254_ = lean_usize_sub(v___x_1252_, v___x_1253_);
    v___x_1255_ = lean_usize_land(v___x_1251_, v___x_1254_);
    v___x_1256_ = lean_array_uget_borrowed(v_buckets_1242_, v___x_1255_);
    v___x_1257_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1241_, v___x_1256_);
    return v___x_1257_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_m_1258_: *mut crate::leanh::LeanObject,
    mut v_a_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_m_1258_, v_a_1259_);
    crate::leanh::lean_dec_ref(v_a_1259_);
    crate::leanh::lean_dec_ref(v_m_1258_);
    return v_res_1260_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12___redArg(
    mut v_a_1261_: *mut crate::leanh::LeanObject,
    mut v_b_1262_: *mut crate::leanh::LeanObject,
    mut v_x_1263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1269_: u8 = 0;
    let mut v___x_1270_: u8 = 0;
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1263_) == 0 {
                    crate::leanh::lean_dec(v_b_1262_);
                    crate::leanh::lean_dec_ref(v_a_1261_);
                    return v_x_1263_;
                } else {
                    v_key_1264_ = crate::leanh::lean_ctor_get(v_x_1263_, 0);
                    v_value_1265_ = crate::leanh::lean_ctor_get(v_x_1263_, 1);
                    v_tail_1266_ = crate::leanh::lean_ctor_get(v_x_1263_, 2);
                    v_isSharedCheck_1278_ = (!crate::leanh::lean_is_exclusive(v_x_1263_)) as u8;
                    if v_isSharedCheck_1278_ == 0 {
                        v___x_1268_ = v_x_1263_;
                        v_isShared_1269_ = v_isSharedCheck_1278_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1266_);
                        crate::leanh::lean_inc(v_value_1265_);
                        crate::leanh::lean_inc(v_key_1264_);
                        crate::leanh::lean_dec(v_x_1263_);
                        v___x_1268_ = crate::leanh::lean_box(0);
                        v_isShared_1269_ = v_isSharedCheck_1278_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1270_ = l_Lean_ExprStructEq_beq(v_key_1264_, v_a_1261_);
                if v___x_1270_ == 0 {
                    v___x_1271_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1261_, v_b_1262_, v_tail_1266_);
                    if v_isShared_1269_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1268_, 2, v___x_1271_);
                        v___x_1273_ = v___x_1268_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1274_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_key_1264_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_value_1265_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 2, v___x_1271_);
                        v___x_1273_ = v_reuseFailAlloc_1274_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1265_);
                    crate::leanh::lean_dec(v_key_1264_);
                    if v_isShared_1269_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1268_, 1, v_b_1262_);
                        crate::leanh::lean_ctor_set(v___x_1268_, 0, v_a_1261_);
                        v___x_1276_ = v___x_1268_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1277_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1261_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_b_1262_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_tail_1266_);
                        v___x_1276_ = v_reuseFailAlloc_1277_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1273_;
            }
            3 => {
                return v___x_1276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(
    mut v_x_1279_: *mut crate::leanh::LeanObject,
    mut v_x_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: u64 = 0;
    let mut v___x_1289_: u64 = 0;
    let mut v___x_1290_: u64 = 0;
    let mut v_fold_1291_: u64 = 0;
    let mut v___x_1292_: u64 = 0;
    let mut v___x_1293_: u64 = 0;
    let mut v___x_1294_: u64 = 0;
    let mut v___x_1295_: usize = 0;
    let mut v___x_1296_: usize = 0;
    let mut v___x_1297_: usize = 0;
    let mut v___x_1298_: usize = 0;
    let mut v___x_1299_: usize = 0;
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1280_) == 0 {
                    return v_x_1279_;
                } else {
                    v_key_1281_ = crate::leanh::lean_ctor_get(v_x_1280_, 0);
                    v_value_1282_ = crate::leanh::lean_ctor_get(v_x_1280_, 1);
                    v_tail_1283_ = crate::leanh::lean_ctor_get(v_x_1280_, 2);
                    v_isSharedCheck_1306_ = (!crate::leanh::lean_is_exclusive(v_x_1280_)) as u8;
                    if v_isSharedCheck_1306_ == 0 {
                        v___x_1285_ = v_x_1280_;
                        v_isShared_1286_ = v_isSharedCheck_1306_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1283_);
                        crate::leanh::lean_inc(v_value_1282_);
                        crate::leanh::lean_inc(v_key_1281_);
                        crate::leanh::lean_dec(v_x_1280_);
                        v___x_1285_ = crate::leanh::lean_box(0);
                        v_isShared_1286_ = v_isSharedCheck_1306_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1287_ = lean_array_get_size(v_x_1279_);
                v___x_1288_ = l_Lean_ExprStructEq_hash(v_key_1281_);
                v___x_1289_ = 32u64;
                v___x_1290_ = lean_uint64_shift_right(v___x_1288_, v___x_1289_);
                v_fold_1291_ = lean_uint64_xor(v___x_1288_, v___x_1290_);
                v___x_1292_ = 16u64;
                v___x_1293_ = lean_uint64_shift_right(v_fold_1291_, v___x_1292_);
                v___x_1294_ = lean_uint64_xor(v_fold_1291_, v___x_1293_);
                v___x_1295_ = lean_uint64_to_usize(v___x_1294_);
                v___x_1296_ = lean_usize_of_nat(v___x_1287_);
                v___x_1297_ = 1usize;
                v___x_1298_ = lean_usize_sub(v___x_1296_, v___x_1297_);
                v___x_1299_ = lean_usize_land(v___x_1295_, v___x_1298_);
                v___x_1300_ = lean_array_uget_borrowed(v_x_1279_, v___x_1299_);
                crate::leanh::lean_inc(v___x_1300_);
                if v_isShared_1286_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1285_, 2, v___x_1300_);
                    v___x_1302_ = v___x_1285_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1305_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_key_1281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_value_1282_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 2, v___x_1300_);
                    v___x_1302_ = v_reuseFailAlloc_1305_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1303_ = lean_array_uset(v_x_1279_, v___x_1299_, v___x_1302_);
                v_x_1279_ = v___x_1303_;
                v_x_1280_ = v_tail_1283_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(
    mut v_i_1307_: *mut crate::leanh::LeanObject,
    mut v_source_1308_: *mut crate::leanh::LeanObject,
    mut v_target_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: u8 = 0;
    let mut v_es_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1310_ = lean_array_get_size(v_source_1308_);
                v___x_1311_ = lean_nat_dec_lt(v_i_1307_, v___x_1310_);
                if v___x_1311_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1308_);
                    crate::leanh::lean_dec(v_i_1307_);
                    return v_target_1309_;
                } else {
                    v_es_1312_ = lean_array_fget(v_source_1308_, v_i_1307_);
                    v___x_1313_ = crate::leanh::lean_box(0);
                    v_source_1314_ = lean_array_fset(v_source_1308_, v_i_1307_, v___x_1313_);
                    v_target_1315_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_1309_, v_es_1312_);
                    v___x_1316_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1317_ = lean_nat_add(v_i_1307_, v___x_1316_);
                    crate::leanh::lean_dec(v_i_1307_);
                    v_i_1307_ = v___x_1317_;
                    v_source_1308_ = v_source_1314_;
                    v_target_1309_ = v_target_1315_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(
    mut v_data_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1320_ = lean_array_get_size(v_data_1319_);
    v___x_1321_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1322_ = lean_nat_mul(v___x_1320_, v___x_1321_);
    v___x_1323_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1324_ = crate::leanh::lean_box(0);
    v___x_1325_ = lean_mk_array(v_nbuckets_1322_, v___x_1324_);
    v___x_1326_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1323_, v_data_1319_, v___x_1325_);
    return v___x_1326_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(
    mut v_a_1327_: *mut crate::leanh::LeanObject,
    mut v_x_1328_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1329_: u8 = 0;
    let mut v_key_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1328_) == 0 {
                    v___x_1329_ = 0;
                    return v___x_1329_;
                } else {
                    v_key_1330_ = crate::leanh::lean_ctor_get(v_x_1328_, 0);
                    v_tail_1331_ = crate::leanh::lean_ctor_get(v_x_1328_, 2);
                    v___x_1332_ = l_Lean_ExprStructEq_beq(v_key_1330_, v_a_1327_);
                    if v___x_1332_ == 0 {
                        v_x_1328_ = v_tail_1331_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1332_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg___boxed(
    mut v_a_1334_: *mut crate::leanh::LeanObject,
    mut v_x_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1336_: u8 = 0;
    let mut v_r_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1334_, v_x_1335_);
    crate::leanh::lean_dec(v_x_1335_);
    crate::leanh::lean_dec_ref(v_a_1334_);
    v_r_1337_ = crate::leanh::lean_box((v_res_1336_) as usize);
    return v_r_1337_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(
    mut v_m_1338_: *mut crate::leanh::LeanObject,
    mut v_a_1339_: *mut crate::leanh::LeanObject,
    mut v_b_1340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: u64 = 0;
    let mut v___x_1348_: u64 = 0;
    let mut v___x_1349_: u64 = 0;
    let mut v_fold_1350_: u64 = 0;
    let mut v___x_1351_: u64 = 0;
    let mut v___x_1352_: u64 = 0;
    let mut v___x_1353_: u64 = 0;
    let mut v___x_1354_: usize = 0;
    let mut v___x_1355_: usize = 0;
    let mut v___x_1356_: usize = 0;
    let mut v___x_1357_: usize = 0;
    let mut v___x_1358_: usize = 0;
    let mut v_bkt_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: u8 = 0;
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: u8 = 0;
    let mut v_val_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1385_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1341_ = crate::leanh::lean_ctor_get(v_m_1338_, 0);
                v_buckets_1342_ = crate::leanh::lean_ctor_get(v_m_1338_, 1);
                v_isSharedCheck_1385_ = (!crate::leanh::lean_is_exclusive(v_m_1338_)) as u8;
                if v_isSharedCheck_1385_ == 0 {
                    v___x_1344_ = v_m_1338_;
                    v_isShared_1345_ = v_isSharedCheck_1385_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1342_);
                    crate::leanh::lean_inc(v_size_1341_);
                    crate::leanh::lean_dec(v_m_1338_);
                    v___x_1344_ = crate::leanh::lean_box(0);
                    v_isShared_1345_ = v_isSharedCheck_1385_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1346_ = lean_array_get_size(v_buckets_1342_);
                v___x_1347_ = l_Lean_ExprStructEq_hash(v_a_1339_);
                v___x_1348_ = 32u64;
                v___x_1349_ = lean_uint64_shift_right(v___x_1347_, v___x_1348_);
                v_fold_1350_ = lean_uint64_xor(v___x_1347_, v___x_1349_);
                v___x_1351_ = 16u64;
                v___x_1352_ = lean_uint64_shift_right(v_fold_1350_, v___x_1351_);
                v___x_1353_ = lean_uint64_xor(v_fold_1350_, v___x_1352_);
                v___x_1354_ = lean_uint64_to_usize(v___x_1353_);
                v___x_1355_ = lean_usize_of_nat(v___x_1346_);
                v___x_1356_ = 1usize;
                v___x_1357_ = lean_usize_sub(v___x_1355_, v___x_1356_);
                v___x_1358_ = lean_usize_land(v___x_1354_, v___x_1357_);
                v_bkt_1359_ = lean_array_uget_borrowed(v_buckets_1342_, v___x_1358_);
                v___x_1360_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1339_, v_bkt_1359_);
                if v___x_1360_ == 0 {
                    v___x_1361_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1362_ = lean_nat_add(v_size_1341_, v___x_1361_);
                    crate::leanh::lean_dec(v_size_1341_);
                    crate::leanh::lean_inc(v_bkt_1359_);
                    v___x_1363_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1363_, 0, v_a_1339_);
                    crate::leanh::lean_ctor_set(v___x_1363_, 1, v_b_1340_);
                    crate::leanh::lean_ctor_set(v___x_1363_, 2, v_bkt_1359_);
                    v_buckets_x27_1364_ =
                        lean_array_uset(v_buckets_1342_, v___x_1358_, v___x_1363_);
                    v___x_1365_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1366_ = lean_nat_mul(v_size_x27_1362_, v___x_1365_);
                    v___x_1367_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1368_ = lean_nat_div(v___x_1366_, v___x_1367_);
                    crate::leanh::lean_dec(v___x_1366_);
                    v___x_1369_ = lean_array_get_size(v_buckets_x27_1364_);
                    v___x_1370_ = lean_nat_dec_le(v___x_1368_, v___x_1369_);
                    crate::leanh::lean_dec(v___x_1368_);
                    if v___x_1370_ == 0 {
                        v_val_1371_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1364_);
                        if v_isShared_1345_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1344_, 1, v_val_1371_);
                            crate::leanh::lean_ctor_set(v___x_1344_, 0, v_size_x27_1362_);
                            v___x_1373_ = v___x_1344_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1374_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1374_,
                                0,
                                v_size_x27_1362_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_val_1371_);
                            v___x_1373_ = v_reuseFailAlloc_1374_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1345_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1344_, 1, v_buckets_x27_1364_);
                            crate::leanh::lean_ctor_set(v___x_1344_, 0, v_size_x27_1362_);
                            v___x_1376_ = v___x_1344_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1377_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1377_,
                                0,
                                v_size_x27_1362_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1377_,
                                1,
                                v_buckets_x27_1364_,
                            );
                            v___x_1376_ = v_reuseFailAlloc_1377_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1359_);
                    v___x_1378_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1379_ =
                        lean_array_uset(v_buckets_1342_, v___x_1358_, v___x_1378_);
                    v___x_1380_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1339_, v_b_1340_, v_bkt_1359_);
                    v___x_1381_ = lean_array_uset(v_buckets_x27_1379_, v___x_1358_, v___x_1380_);
                    if v_isShared_1345_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1344_, 1, v___x_1381_);
                        v___x_1383_ = v___x_1344_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1384_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_size_1341_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___x_1381_);
                        v___x_1383_ = v_reuseFailAlloc_1384_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1373_;
            }
            3 => {
                return v___x_1376_;
            }
            4 => {
                return v___x_1383_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2(
    mut v_a_1386_: *mut crate::leanh::LeanObject,
    mut v_e_1387_: *mut crate::leanh::LeanObject,
    mut v_a_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1390_ = lean_st_ref_take(v_a_1386_);
    v___x_1391_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v___x_1390_, v_e_1387_, v_a_1388_);
    v___x_1392_ = lean_st_ref_set(v_a_1386_, v___x_1391_);
    v___x_1393_ = crate::leanh::lean_box(0);
    return v___x_1393_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2___boxed(
    mut v_a_1394_: *mut crate::leanh::LeanObject,
    mut v_e_1395_: *mut crate::leanh::LeanObject,
    mut v_a_1396_: *mut crate::leanh::LeanObject,
    mut v___y_1397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1398_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2(v_a_1394_, v_e_1395_, v_a_1396_);
    crate::leanh::lean_dec(v_a_1394_);
    return v_res_1398_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1399_ = crate::leanh::lean_box(0);
    v___x_1400_ = l_Lean_interruptExceptionId;
    v___x_1401_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1401_, 0, v___x_1400_);
    crate::leanh::lean_ctor_set(v___x_1401_, 1, v___x_1399_);
    return v___x_1401_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1403_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
    v___x_1404_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1404_, 0, v___x_1403_);
    return v___x_1404_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___boxed(
    mut v___y_1405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1406_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg();
    return v_res_1406_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1412_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1413_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1413_, 0, v___x_1412_);
    return v___x_1413_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1414_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
    v___x_1415_ = l_Lean_MessageData_ofFormat(v___x_1414_);
    return v___x_1415_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1416_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
    v___x_1417_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2;
    v___x_1418_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1418_, 0, v___x_1417_);
    crate::leanh::lean_ctor_set(v___x_1418_, 1, v___x_1416_);
    return v___x_1418_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(
    mut v_ref_1419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1421_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
    v___x_1422_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1422_, 0, v_ref_1419_);
    crate::leanh::lean_ctor_set(v___x_1422_, 1, v___x_1421_);
    v___x_1423_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1423_, 0, v___x_1422_);
    return v___x_1423_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___boxed(
    mut v_ref_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1426_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1424_);
    return v_res_1426_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(
    mut v_x_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1437_: u8 = 0;
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1441_: u8 = 0;
    let mut v___y_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: u8 = 0;
    let mut v___y_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1452_: u8 = 0;
    let mut v___y_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1475_: u8 = 0;
    let mut v_cancelTk_x3f_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1477_: u8 = 0;
    let mut v_inheritedTraceOptions_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: u8 = 0;
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1463_ = crate::leanh::lean_ctor_get(v___y_1429_, 0);
                v_fileMap_1464_ = crate::leanh::lean_ctor_get(v___y_1429_, 1);
                v_options_1465_ = crate::leanh::lean_ctor_get(v___y_1429_, 2);
                v_currRecDepth_1466_ = crate::leanh::lean_ctor_get(v___y_1429_, 3);
                v_maxRecDepth_1467_ = crate::leanh::lean_ctor_get(v___y_1429_, 4);
                v_ref_1468_ = crate::leanh::lean_ctor_get(v___y_1429_, 5);
                v_currNamespace_1469_ = crate::leanh::lean_ctor_get(v___y_1429_, 6);
                v_openDecls_1470_ = crate::leanh::lean_ctor_get(v___y_1429_, 7);
                v_initHeartbeats_1471_ = crate::leanh::lean_ctor_get(v___y_1429_, 8);
                v_maxHeartbeats_1472_ = crate::leanh::lean_ctor_get(v___y_1429_, 9);
                v_quotContext_1473_ = crate::leanh::lean_ctor_get(v___y_1429_, 10);
                v_currMacroScope_1474_ = crate::leanh::lean_ctor_get(v___y_1429_, 11);
                v_diag_1475_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1429_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1476_ = crate::leanh::lean_ctor_get(v___y_1429_, 12);
                v_suppressElabErrors_1477_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1429_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1478_ = crate::leanh::lean_ctor_get(v___y_1429_, 13);
                if crate::leanh::lean_obj_tag(v_cancelTk_x3f_1476_) == 1 {
                    v_val_1484_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_1476_, 0);
                    v___x_1485_ = l_IO_CancelToken_isSet(v_val_1484_);
                    if v___x_1485_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_1427_);
                        v___x_1486_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg();
                        v_a_1487_ = crate::leanh::lean_ctor_get(v___x_1486_, 0);
                        v_isSharedCheck_1494_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1486_)) as u8;
                        if v_isSharedCheck_1494_ == 0 {
                            v___x_1489_ = v___x_1486_;
                            v_isShared_1490_ = v_isSharedCheck_1494_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1487_);
                            crate::leanh::lean_dec(v___x_1486_);
                            v___x_1489_ = crate::leanh::lean_box(0);
                            v_isShared_1490_ = v_isSharedCheck_1494_;
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
                if crate::leanh::lean_obj_tag(v___y_1433_) == 0 {
                    return v___y_1433_;
                } else {
                    v_a_1434_ = crate::leanh::lean_ctor_get(v___y_1433_, 0);
                    v_isSharedCheck_1441_ = (!crate::leanh::lean_is_exclusive(v___y_1433_)) as u8;
                    if v_isSharedCheck_1441_ == 0 {
                        v___x_1436_ = v___y_1433_;
                        v_isShared_1437_ = v_isSharedCheck_1441_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1434_);
                        crate::leanh::lean_dec(v___y_1433_);
                        v___x_1436_ = crate::leanh::lean_box(0);
                        v_isShared_1437_ = v_isSharedCheck_1441_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1437_ == 0 {
                    v___x_1439_ = v___x_1436_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1440_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
                    v___x_1439_ = v_reuseFailAlloc_1440_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1439_;
            }
            4 => {
                v___x_1459_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1460_ = lean_nat_add(v___y_1448_, v___x_1459_);
                crate::leanh::lean_inc_ref(v___y_1456_);
                crate::leanh::lean_inc(v___y_1449_);
                crate::leanh::lean_inc(v___y_1447_);
                crate::leanh::lean_inc(v___y_1455_);
                crate::leanh::lean_inc(v___y_1450_);
                crate::leanh::lean_inc(v___y_1454_);
                crate::leanh::lean_inc(v___y_1453_);
                crate::leanh::lean_inc(v___y_1458_);
                crate::leanh::lean_inc(v___y_1457_);
                crate::leanh::lean_inc_ref(v___y_1451_);
                crate::leanh::lean_inc_ref(v___y_1445_);
                crate::leanh::lean_inc_ref(v___y_1446_);
                v___x_1461_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1461_, 0, v___y_1446_);
                crate::leanh::lean_ctor_set(v___x_1461_, 1, v___y_1445_);
                crate::leanh::lean_ctor_set(v___x_1461_, 2, v___y_1451_);
                crate::leanh::lean_ctor_set(v___x_1461_, 3, v___x_1460_);
                crate::leanh::lean_ctor_set(v___x_1461_, 4, v___y_1457_);
                crate::leanh::lean_ctor_set(v___x_1461_, 5, v___y_1443_);
                crate::leanh::lean_ctor_set(v___x_1461_, 6, v___y_1458_);
                crate::leanh::lean_ctor_set(v___x_1461_, 7, v___y_1453_);
                crate::leanh::lean_ctor_set(v___x_1461_, 8, v___y_1454_);
                crate::leanh::lean_ctor_set(v___x_1461_, 9, v___y_1450_);
                crate::leanh::lean_ctor_set(v___x_1461_, 10, v___y_1455_);
                crate::leanh::lean_ctor_set(v___x_1461_, 11, v___y_1447_);
                crate::leanh::lean_ctor_set(v___x_1461_, 12, v___y_1449_);
                crate::leanh::lean_ctor_set(v___x_1461_, 13, v___y_1456_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1461_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___y_1452_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1461_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_1444_,
                );
                crate::leanh::lean_inc(v___y_1430_);
                crate::leanh::lean_inc(v___y_1428_);
                v___x_1462_ = crate::leanh::lean_apply_4(
                    v_x_1427_,
                    v___y_1428_,
                    v___x_1461_,
                    v___y_1430_,
                    crate::leanh::lean_box(0),
                );
                v___y_1433_ = v___x_1462_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1480_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1481_ = lean_nat_dec_eq(v_maxRecDepth_1467_, v___x_1480_);
                if v___x_1481_ == 0 {
                    v___x_1482_ = lean_nat_dec_eq(v_currRecDepth_1466_, v_maxRecDepth_1467_);
                    if v___x_1482_ == 0 {
                        crate::leanh::lean_inc(v_ref_1468_);
                        v___y_1443_ = v_ref_1468_;
                        v___y_1444_ = v_suppressElabErrors_1477_;
                        v___y_1445_ = v_fileMap_1464_;
                        v___y_1446_ = v_fileName_1463_;
                        v___y_1447_ = v_currMacroScope_1474_;
                        v___y_1448_ = v_currRecDepth_1466_;
                        v___y_1449_ = v_cancelTk_x3f_1476_;
                        v___y_1450_ = v_maxHeartbeats_1472_;
                        v___y_1451_ = v_options_1465_;
                        v___y_1452_ = v_diag_1475_;
                        v___y_1453_ = v_openDecls_1470_;
                        v___y_1454_ = v_initHeartbeats_1471_;
                        v___y_1455_ = v_quotContext_1473_;
                        v___y_1456_ = v_inheritedTraceOptions_1478_;
                        v___y_1457_ = v_maxRecDepth_1467_;
                        v___y_1458_ = v_currNamespace_1469_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_1427_);
                        crate::leanh::lean_inc(v_ref_1468_);
                        v___x_1483_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1468_);
                        v___y_1433_ = v___x_1483_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_ref_1468_);
                    v___y_1443_ = v_ref_1468_;
                    v___y_1444_ = v_suppressElabErrors_1477_;
                    v___y_1445_ = v_fileMap_1464_;
                    v___y_1446_ = v_fileName_1463_;
                    v___y_1447_ = v_currMacroScope_1474_;
                    v___y_1448_ = v_currRecDepth_1466_;
                    v___y_1449_ = v_cancelTk_x3f_1476_;
                    v___y_1450_ = v_maxHeartbeats_1472_;
                    v___y_1451_ = v_options_1465_;
                    v___y_1452_ = v_diag_1475_;
                    v___y_1453_ = v_openDecls_1470_;
                    v___y_1454_ = v_initHeartbeats_1471_;
                    v___y_1455_ = v_quotContext_1473_;
                    v___y_1456_ = v_inheritedTraceOptions_1478_;
                    v___y_1457_ = v_maxRecDepth_1467_;
                    v___y_1458_ = v_currNamespace_1469_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v_isShared_1490_ == 0 {
                    v___x_1492_ = v___x_1489_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1493_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
                    v___x_1492_ = v_reuseFailAlloc_1493_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg___boxed(
    mut v_x_1495_: *mut crate::leanh::LeanObject,
    mut v___y_1496_: *mut crate::leanh::LeanObject,
    mut v___y_1497_: *mut crate::leanh::LeanObject,
    mut v___y_1498_: *mut crate::leanh::LeanObject,
    mut v___y_1499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1500_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v_x_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
    crate::leanh::lean_dec(v___y_1498_);
    crate::leanh::lean_dec_ref(v___y_1497_);
    crate::leanh::lean_dec(v___y_1496_);
    return v_res_1500_;
}
pub unsafe fn _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = crate::leanh::lean_box(0);
    v_dummy_1503_ = l_Lean_Expr_sort___override(v___x_1502_);
    return v_dummy_1503_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(
    mut v_pre_1504_: *mut crate::leanh::LeanObject,
    mut v_post_1505_: *mut crate::leanh::LeanObject,
    mut v_sz_1506_: usize,
    mut v_i_1507_: usize,
    mut v_bs_1508_: *mut crate::leanh::LeanObject,
    mut v___y_1509_: *mut crate::leanh::LeanObject,
    mut v___y_1510_: *mut crate::leanh::LeanObject,
    mut v___y_1511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1513_: u8 = 0;
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: usize = 0;
    let mut v___x_1521_: usize = 0;
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1527_: u8 = 0;
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1513_ = lean_usize_dec_lt(v_i_1507_, v_sz_1506_);
                if v___x_1513_ == 0 {
                    crate::leanh::lean_dec_ref(v_post_1505_);
                    crate::leanh::lean_dec_ref(v_pre_1504_);
                    v___x_1514_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1514_, 0, v_bs_1508_);
                    return v___x_1514_;
                } else {
                    v_v_1515_ = lean_array_uget_borrowed(v_bs_1508_, v_i_1507_);
                    crate::leanh::lean_inc(v_v_1515_);
                    crate::leanh::lean_inc_ref(v_post_1505_);
                    crate::leanh::lean_inc_ref(v_pre_1504_);
                    v___x_1516_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1504_, v_post_1505_, v_v_1515_, v___y_1509_, v___y_1510_, v___y_1511_);
                    if crate::leanh::lean_obj_tag(v___x_1516_) == 0 {
                        v_a_1517_ = crate::leanh::lean_ctor_get(v___x_1516_, 0);
                        crate::leanh::lean_inc(v_a_1517_);
                        crate::leanh::lean_dec_ref_known(v___x_1516_, 1);
                        v___x_1518_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1519_ = lean_array_uset(v_bs_1508_, v_i_1507_, v___x_1518_);
                        v___x_1520_ = 1usize;
                        v___x_1521_ = lean_usize_add(v_i_1507_, v___x_1520_);
                        v___x_1522_ = lean_array_uset(v_bs_x27_1519_, v_i_1507_, v_a_1517_);
                        v_i_1507_ = v___x_1521_;
                        v_bs_1508_ = v___x_1522_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_1508_);
                        crate::leanh::lean_dec_ref(v_post_1505_);
                        crate::leanh::lean_dec_ref(v_pre_1504_);
                        v_a_1524_ = crate::leanh::lean_ctor_get(v___x_1516_, 0);
                        v_isSharedCheck_1531_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1516_)) as u8;
                        if v_isSharedCheck_1531_ == 0 {
                            v___x_1526_ = v___x_1516_;
                            v_isShared_1527_ = v_isSharedCheck_1531_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1524_);
                            crate::leanh::lean_dec(v___x_1516_);
                            v___x_1526_ = crate::leanh::lean_box(0);
                            v_isShared_1527_ = v_isSharedCheck_1531_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1527_ == 0 {
                    v___x_1529_ = v___x_1526_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
                    v___x_1529_ = v_reuseFailAlloc_1530_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(
    mut v_pre_1532_: *mut crate::leanh::LeanObject,
    mut v_post_1533_: *mut crate::leanh::LeanObject,
    mut v_x_1534_: *mut crate::leanh::LeanObject,
    mut v_x_1535_: *mut crate::leanh::LeanObject,
    mut v_x_1536_: *mut crate::leanh::LeanObject,
    mut v___y_1537_: *mut crate::leanh::LeanObject,
    mut v___y_1538_: *mut crate::leanh::LeanObject,
    mut v___y_1539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1549_: usize = 0;
    let mut v___x_1550_: usize = 0;
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1558_: u8 = 0;
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1534_) == 5 {
                    v_fn_1541_ = crate::leanh::lean_ctor_get(v_x_1534_, 0);
                    crate::leanh::lean_inc_ref(v_fn_1541_);
                    v_arg_1542_ = crate::leanh::lean_ctor_get(v_x_1534_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1542_);
                    crate::leanh::lean_dec_ref_known(v_x_1534_, 2);
                    v___x_1543_ = lean_array_set(v_x_1535_, v_x_1536_, v_arg_1542_);
                    v___x_1544_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1545_ = lean_nat_sub(v_x_1536_, v___x_1544_);
                    crate::leanh::lean_dec(v_x_1536_);
                    v_x_1534_ = v_fn_1541_;
                    v_x_1535_ = v___x_1543_;
                    v_x_1536_ = v___x_1545_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_1536_);
                    crate::leanh::lean_inc_ref(v_post_1533_);
                    crate::leanh::lean_inc_ref(v_pre_1532_);
                    v___x_1547_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1532_, v_post_1533_, v_x_1534_, v___y_1537_, v___y_1538_, v___y_1539_);
                    if crate::leanh::lean_obj_tag(v___x_1547_) == 0 {
                        v_a_1548_ = crate::leanh::lean_ctor_get(v___x_1547_, 0);
                        crate::leanh::lean_inc(v_a_1548_);
                        crate::leanh::lean_dec_ref_known(v___x_1547_, 1);
                        v_sz_1549_ = lean_array_size(v_x_1535_);
                        v___x_1550_ = 0usize;
                        crate::leanh::lean_inc_ref(v_post_1533_);
                        crate::leanh::lean_inc_ref(v_pre_1532_);
                        v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(v_pre_1532_, v_post_1533_, v_sz_1549_, v___x_1550_, v_x_1535_, v___y_1537_, v___y_1538_, v___y_1539_);
                        if crate::leanh::lean_obj_tag(v___x_1551_) == 0 {
                            v_a_1552_ = crate::leanh::lean_ctor_get(v___x_1551_, 0);
                            crate::leanh::lean_inc(v_a_1552_);
                            crate::leanh::lean_dec_ref_known(v___x_1551_, 1);
                            v___x_1553_ = l_Lean_mkAppN(v_a_1548_, v_a_1552_);
                            crate::leanh::lean_dec(v_a_1552_);
                            v___x_1554_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1532_, v_post_1533_, v___x_1553_, v___y_1537_, v___y_1538_, v___y_1539_);
                            return v___x_1554_;
                        } else {
                            crate::leanh::lean_dec(v_a_1548_);
                            crate::leanh::lean_dec_ref(v_post_1533_);
                            crate::leanh::lean_dec_ref(v_pre_1532_);
                            v_a_1555_ = crate::leanh::lean_ctor_get(v___x_1551_, 0);
                            v_isSharedCheck_1562_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1551_)) as u8;
                            if v_isSharedCheck_1562_ == 0 {
                                v___x_1557_ = v___x_1551_;
                                v_isShared_1558_ = v_isSharedCheck_1562_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1555_);
                                crate::leanh::lean_dec(v___x_1551_);
                                v___x_1557_ = crate::leanh::lean_box(0);
                                v_isShared_1558_ = v_isSharedCheck_1562_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_1535_);
                        crate::leanh::lean_dec_ref(v_post_1533_);
                        crate::leanh::lean_dec_ref(v_pre_1532_);
                        return v___x_1547_;
                    }
                }
            }
            1 => {
                if v_isShared_1558_ == 0 {
                    v___x_1560_ = v___x_1557_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1561_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
                    v___x_1560_ = v_reuseFailAlloc_1561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1(
    mut v___x_1563_: *mut crate::leanh::LeanObject,
    mut v_pre_1564_: *mut crate::leanh::LeanObject,
    mut v_e_1565_: *mut crate::leanh::LeanObject,
    mut v_post_1566_: *mut crate::leanh::LeanObject,
    mut v___y_1567_: *mut crate::leanh::LeanObject,
    mut v___y_1568_: *mut crate::leanh::LeanObject,
    mut v___y_1569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1575_: u8 = 0;
    let mut v___y_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1579_: u8 = 0;
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: usize = 0;
    let mut v___x_1583_: usize = 0;
    let mut v___x_1584_: u8 = 0;
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1592_: u8 = 0;
    let mut v___y_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1594_: u8 = 0;
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: u8 = 0;
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1605_: u8 = 0;
    let mut v___y_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1607_: u8 = 0;
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1619_: u8 = 0;
    let mut v___y_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1625_: u8 = 0;
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: usize = 0;
    let mut v___x_1631_: usize = 0;
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: usize = 0;
    let mut v___x_1634_: usize = 0;
    let mut v___x_1635_: u8 = 0;
    let mut v_binderName_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1639_: u8 = 0;
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: usize = 0;
    let mut v___x_1645_: usize = 0;
    let mut v___x_1646_: u8 = 0;
    let mut v___x_1647_: usize = 0;
    let mut v___x_1648_: usize = 0;
    let mut v___x_1649_: u8 = 0;
    let mut v_declName_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1654_: u8 = 0;
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: usize = 0;
    let mut v___x_1662_: usize = 0;
    let mut v___x_1663_: u8 = 0;
    let mut v___x_1664_: usize = 0;
    let mut v___x_1665_: usize = 0;
    let mut v___x_1666_: u8 = 0;
    let mut v_dummy_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: usize = 0;
    let mut v___x_1678_: usize = 0;
    let mut v___x_1679_: u8 = 0;
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: usize = 0;
    let mut v___x_1689_: usize = 0;
    let mut v___x_1690_: u8 = 0;
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1705_: u8 = 0;
    let mut v_a_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1709_: u8 = 0;
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1713_: u8 = 0;
    let mut v_a_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1614_ = l_Lean_Core_checkSystem(v___x_1563_, v___y_1568_, v___y_1569_);
                if crate::leanh::lean_obj_tag(v___x_1614_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1614_, 1);
                    crate::leanh::lean_inc_ref(v_pre_1564_);
                    crate::leanh::lean_inc(v___y_1569_);
                    crate::leanh::lean_inc_ref(v___y_1568_);
                    crate::leanh::lean_inc_ref(v_e_1565_);
                    v___x_1615_ = crate::leanh::lean_apply_4(
                        v_pre_1564_,
                        v_e_1565_,
                        v___y_1568_,
                        v___y_1569_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_1615_) == 0 {
                        v_a_1616_ = crate::leanh::lean_ctor_get(v___x_1615_, 0);
                        v_isSharedCheck_1705_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1615_)) as u8;
                        if v_isSharedCheck_1705_ == 0 {
                            v___x_1618_ = v___x_1615_;
                            v_isShared_1619_ = v_isSharedCheck_1705_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1616_);
                            crate::leanh::lean_dec(v___x_1615_);
                            v___x_1618_ = crate::leanh::lean_box(0);
                            v_isShared_1619_ = v_isSharedCheck_1705_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_post_1566_);
                        crate::leanh::lean_dec_ref(v_e_1565_);
                        crate::leanh::lean_dec_ref(v_pre_1564_);
                        v_a_1706_ = crate::leanh::lean_ctor_get(v___x_1615_, 0);
                        v_isSharedCheck_1713_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1615_)) as u8;
                        if v_isSharedCheck_1713_ == 0 {
                            v___x_1708_ = v___x_1615_;
                            v_isShared_1709_ = v_isSharedCheck_1713_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1706_);
                            crate::leanh::lean_dec(v___x_1615_);
                            v___x_1708_ = crate::leanh::lean_box(0);
                            v_isShared_1709_ = v_isSharedCheck_1713_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_post_1566_);
                    crate::leanh::lean_dec_ref(v_e_1565_);
                    crate::leanh::lean_dec_ref(v_pre_1564_);
                    v_a_1714_ = crate::leanh::lean_ctor_get(v___x_1614_, 0);
                    v_isSharedCheck_1721_ = (!crate::leanh::lean_is_exclusive(v___x_1614_)) as u8;
                    if v_isSharedCheck_1721_ == 0 {
                        v___x_1716_ = v___x_1614_;
                        v_isShared_1717_ = v_isSharedCheck_1721_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1714_);
                        crate::leanh::lean_dec(v___x_1614_);
                        v___x_1716_ = crate::leanh::lean_box(0);
                        v_isShared_1717_ = v_isSharedCheck_1721_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1579_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1576_);
                    crate::leanh::lean_dec_ref(v___y_1572_);
                    v___x_1580_ = l_Lean_Expr_letE___override(
                        v___y_1577_,
                        v___y_1574_,
                        v___y_1573_,
                        v___y_1578_,
                        v___y_1575_,
                    );
                    v___x_1581_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___x_1580_, v___y_1567_, v___y_1568_, v___y_1569_);
                    return v___x_1581_;
                } else {
                    v___x_1582_ = lean_ptr_addr(v___y_1576_);
                    crate::leanh::lean_dec_ref(v___y_1576_);
                    v___x_1583_ = lean_ptr_addr(v___y_1578_);
                    v___x_1584_ = lean_usize_dec_eq(v___x_1582_, v___x_1583_);
                    if v___x_1584_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_1572_);
                        v___x_1585_ = l_Lean_Expr_letE___override(
                            v___y_1577_,
                            v___y_1574_,
                            v___y_1573_,
                            v___y_1578_,
                            v___y_1575_,
                        );
                        v___x_1586_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___x_1585_, v___y_1567_, v___y_1568_, v___y_1569_);
                        return v___x_1586_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1578_);
                        crate::leanh::lean_dec(v___y_1577_);
                        crate::leanh::lean_dec_ref(v___y_1574_);
                        crate::leanh::lean_dec_ref(v___y_1573_);
                        v___x_1587_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___y_1572_, v___y_1567_, v___y_1568_, v___y_1569_);
                        return v___x_1587_;
                    }
                }
            }
            2 => {
                if v___y_1594_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1589_);
                    v___x_1595_ = l_Lean_Expr_lam___override(
                        v___y_1593_,
                        v___y_1591_,
                        v___y_1590_,
                        v___y_1592_,
                    );
                    v___x_1596_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___x_1595_, v___y_1567_, v___y_1568_, v___y_1569_);
                    return v___x_1596_;
                } else {
                    v___x_1597_ = l_Lean_instBEqBinderInfo_beq(v___y_1592_, v___y_1592_);
                    if v___x_1597_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_1589_);
                        v___x_1598_ = l_Lean_Expr_lam___override(
                            v___y_1593_,
                            v___y_1591_,
                            v___y_1590_,
                            v___y_1592_,
                        );
                        v___x_1599_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___x_1598_, v___y_1567_, v___y_1568_, v___y_1569_);
                        return v___x_1599_;
                    } else {
                        crate::leanh::lean_dec(v___y_1593_);
                        crate::leanh::lean_dec_ref(v___y_1591_);
                        crate::leanh::lean_dec_ref(v___y_1590_);
                        v___x_1600_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___y_1589_, v___y_1567_, v___y_1568_, v___y_1569_);
                        return v___x_1600_;
                    }
                }
            }
            3 => {
                if v___y_1607_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1602_);
                    v___x_1608_ = l_Lean_Expr_forallE___override(
                        v___y_1604_,
                        v___y_1603_,
                        v___y_1606_,
                        v___y_1605_,
                    );
                    v___x_1609_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___x_1608_, v___y_1567_, v___y_1568_, v___y_1569_);
                    return v___x_1609_;
                } else {
                    v___x_1610_ = l_Lean_instBEqBinderInfo_beq(v___y_1605_, v___y_1605_);
                    if v___x_1610_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_1602_);
                        v___x_1611_ = l_Lean_Expr_forallE___override(
                            v___y_1604_,
                            v___y_1603_,
                            v___y_1606_,
                            v___y_1605_,
                        );
                        v___x_1612_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___x_1611_, v___y_1567_, v___y_1568_, v___y_1569_);
                        return v___x_1612_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1606_);
                        crate::leanh::lean_dec(v___y_1604_);
                        crate::leanh::lean_dec_ref(v___y_1603_);
                        v___x_1613_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___y_1602_, v___y_1567_, v___y_1568_, v___y_1569_);
                        return v___x_1613_;
                    }
                }
            }
            4 => match crate::leanh::lean_obj_tag(v_a_1616_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_post_1566_);
                    crate::leanh::lean_dec_ref(v_e_1565_);
                    crate::leanh::lean_dec_ref(v_pre_1564_);
                    v_e_1695_ = crate::leanh::lean_ctor_get(v_a_1616_, 0);
                    crate::leanh::lean_inc_ref(v_e_1695_);
                    crate::leanh::lean_dec_ref_known(v_a_1616_, 1);
                    if v_isShared_1619_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1618_, 0, v_e_1695_);
                        v___x_1697_ = v___x_1618_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1698_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_e_1695_);
                        v___x_1697_ = v_reuseFailAlloc_1698_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_1618_);
                    crate::leanh::lean_dec_ref(v_e_1565_);
                    v_e_1699_ = crate::leanh::lean_ctor_get(v_a_1616_, 0);
                    crate::leanh::lean_inc_ref(v_e_1699_);
                    crate::leanh::lean_dec_ref_known(v_a_1616_, 1);
                    crate::leanh::lean_inc_ref(v_post_1566_);
                    crate::leanh::lean_inc_ref(v_pre_1564_);
                    v___x_1700_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_e_1699_, v___y_1567_, v___y_1568_, v___y_1569_);
                    if crate::leanh::lean_obj_tag(v___x_1700_) == 0 {
                        v_a_1701_ = crate::leanh::lean_ctor_get(v___x_1700_, 0);
                        crate::leanh::lean_inc(v_a_1701_);
                        crate::leanh::lean_dec_ref_known(v___x_1700_, 1);
                        v___x_1702_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v_a_1701_, v___y_1567_, v___y_1568_, v___y_1569_);
                        return v___x_1702_;
                    } else {
                        crate::leanh::lean_dec_ref(v_post_1566_);
                        crate::leanh::lean_dec_ref(v_pre_1564_);
                        return v___x_1700_;
                    }
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_1618_);
                    v_e_x3f_1703_ = crate::leanh::lean_ctor_get(v_a_1616_, 0);
                    crate::leanh::lean_inc(v_e_x3f_1703_);
                    crate::leanh::lean_dec_ref_known(v_a_1616_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_1703_) == 0 {
                        v___y_1621_ = v_e_1565_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1565_);
                        v_val_1704_ = crate::leanh::lean_ctor_get(v_e_x3f_1703_, 0);
                        crate::leanh::lean_inc(v_val_1704_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_1703_, 1);
                        v___y_1621_ = v_val_1704_;
                        state = 5;
                        continue;
                    }
                }
            },
            5 => match crate::leanh::lean_obj_tag(v___y_1621_) {
                7 => {
                    v_binderName_1622_ = crate::leanh::lean_ctor_get(v___y_1621_, 0);
                    crate::leanh::lean_inc(v_binderName_1622_);
                    v_binderType_1623_ = crate::leanh::lean_ctor_get(v___y_1621_, 1);
                    v_body_1624_ = crate::leanh::lean_ctor_get(v___y_1621_, 2);
                    v_binderInfo_1625_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1621_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_1623_);
                    crate::leanh::lean_inc_ref(v_post_1566_);
                    crate::leanh::lean_inc_ref(v_pre_1564_);
                    v___x_1626_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_binderType_1623_, v___y_1567_, v___y_1568_, v___y_1569_);
                    if crate::leanh::lean_obj_tag(v___x_1626_) == 0 {
                        v_a_1627_ = crate::leanh::lean_ctor_get(v___x_1626_, 0);
                        crate::leanh::lean_inc(v_a_1627_);
                        crate::leanh::lean_dec_ref_known(v___x_1626_, 1);
                        crate::leanh::lean_inc_ref(v_body_1624_);
                        crate::leanh::lean_inc_ref(v_post_1566_);
                        crate::leanh::lean_inc_ref(v_pre_1564_);
                        v___x_1628_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_body_1624_, v___y_1567_, v___y_1568_, v___y_1569_);
                        if crate::leanh::lean_obj_tag(v___x_1628_) == 0 {
                            v_a_1629_ = crate::leanh::lean_ctor_get(v___x_1628_, 0);
                            crate::leanh::lean_inc(v_a_1629_);
                            crate::leanh::lean_dec_ref_known(v___x_1628_, 1);
                            v___x_1630_ = lean_ptr_addr(v_binderType_1623_);
                            v___x_1631_ = lean_ptr_addr(v_a_1627_);
                            v___x_1632_ = lean_usize_dec_eq(v___x_1630_, v___x_1631_);
                            if v___x_1632_ == 0 {
                                v___y_1602_ = v___y_1621_;
                                v___y_1603_ = v_a_1627_;
                                v___y_1604_ = v_binderName_1622_;
                                v___y_1605_ = v_binderInfo_1625_;
                                v___y_1606_ = v_a_1629_;
                                v___y_1607_ = v___x_1632_;
                                state = 3;
                                continue;
                            } else {
                                v___x_1633_ = lean_ptr_addr(v_body_1624_);
                                v___x_1634_ = lean_ptr_addr(v_a_1629_);
                                v___x_1635_ = lean_usize_dec_eq(v___x_1633_, v___x_1634_);
                                v___y_1602_ = v___y_1621_;
                                v___y_1603_ = v_a_1627_;
                                v___y_1604_ = v_binderName_1622_;
                                v___y_1605_ = v_binderInfo_1625_;
                                v___y_1606_ = v_a_1629_;
                                v___y_1607_ = v___x_1635_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1627_);
                            crate::leanh::lean_dec_ref_known(v___y_1621_, 3);
                            crate::leanh::lean_dec(v_binderName_1622_);
                            crate::leanh::lean_dec_ref(v_post_1566_);
                            crate::leanh::lean_dec_ref(v_pre_1564_);
                            return v___x_1628_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_1621_, 3);
                        crate::leanh::lean_dec(v_binderName_1622_);
                        crate::leanh::lean_dec_ref(v_post_1566_);
                        crate::leanh::lean_dec_ref(v_pre_1564_);
                        return v___x_1626_;
                    }
                }
                6 => {
                    v_binderName_1636_ = crate::leanh::lean_ctor_get(v___y_1621_, 0);
                    crate::leanh::lean_inc(v_binderName_1636_);
                    v_binderType_1637_ = crate::leanh::lean_ctor_get(v___y_1621_, 1);
                    v_body_1638_ = crate::leanh::lean_ctor_get(v___y_1621_, 2);
                    v_binderInfo_1639_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1621_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_1637_);
                    crate::leanh::lean_inc_ref(v_post_1566_);
                    crate::leanh::lean_inc_ref(v_pre_1564_);
                    v___x_1640_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_binderType_1637_, v___y_1567_, v___y_1568_, v___y_1569_);
                    if crate::leanh::lean_obj_tag(v___x_1640_) == 0 {
                        v_a_1641_ = crate::leanh::lean_ctor_get(v___x_1640_, 0);
                        crate::leanh::lean_inc(v_a_1641_);
                        crate::leanh::lean_dec_ref_known(v___x_1640_, 1);
                        crate::leanh::lean_inc_ref(v_body_1638_);
                        crate::leanh::lean_inc_ref(v_post_1566_);
                        crate::leanh::lean_inc_ref(v_pre_1564_);
                        v___x_1642_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_body_1638_, v___y_1567_, v___y_1568_, v___y_1569_);
                        if crate::leanh::lean_obj_tag(v___x_1642_) == 0 {
                            v_a_1643_ = crate::leanh::lean_ctor_get(v___x_1642_, 0);
                            crate::leanh::lean_inc(v_a_1643_);
                            crate::leanh::lean_dec_ref_known(v___x_1642_, 1);
                            v___x_1644_ = lean_ptr_addr(v_binderType_1637_);
                            v___x_1645_ = lean_ptr_addr(v_a_1641_);
                            v___x_1646_ = lean_usize_dec_eq(v___x_1644_, v___x_1645_);
                            if v___x_1646_ == 0 {
                                v___y_1589_ = v___y_1621_;
                                v___y_1590_ = v_a_1643_;
                                v___y_1591_ = v_a_1641_;
                                v___y_1592_ = v_binderInfo_1639_;
                                v___y_1593_ = v_binderName_1636_;
                                v___y_1594_ = v___x_1646_;
                                state = 2;
                                continue;
                            } else {
                                v___x_1647_ = lean_ptr_addr(v_body_1638_);
                                v___x_1648_ = lean_ptr_addr(v_a_1643_);
                                v___x_1649_ = lean_usize_dec_eq(v___x_1647_, v___x_1648_);
                                v___y_1589_ = v___y_1621_;
                                v___y_1590_ = v_a_1643_;
                                v___y_1591_ = v_a_1641_;
                                v___y_1592_ = v_binderInfo_1639_;
                                v___y_1593_ = v_binderName_1636_;
                                v___y_1594_ = v___x_1649_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1641_);
                            crate::leanh::lean_dec_ref_known(v___y_1621_, 3);
                            crate::leanh::lean_dec(v_binderName_1636_);
                            crate::leanh::lean_dec_ref(v_post_1566_);
                            crate::leanh::lean_dec_ref(v_pre_1564_);
                            return v___x_1642_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_1621_, 3);
                        crate::leanh::lean_dec(v_binderName_1636_);
                        crate::leanh::lean_dec_ref(v_post_1566_);
                        crate::leanh::lean_dec_ref(v_pre_1564_);
                        return v___x_1640_;
                    }
                }
                8 => {
                    v_declName_1650_ = crate::leanh::lean_ctor_get(v___y_1621_, 0);
                    crate::leanh::lean_inc(v_declName_1650_);
                    v_type_1651_ = crate::leanh::lean_ctor_get(v___y_1621_, 1);
                    v_value_1652_ = crate::leanh::lean_ctor_get(v___y_1621_, 2);
                    v_body_1653_ = crate::leanh::lean_ctor_get(v___y_1621_, 3);
                    crate::leanh::lean_inc_ref(v_body_1653_);
                    v_nondep_1654_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1621_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_type_1651_);
                    crate::leanh::lean_inc_ref(v_post_1566_);
                    crate::leanh::lean_inc_ref(v_pre_1564_);
                    v___x_1655_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_type_1651_, v___y_1567_, v___y_1568_, v___y_1569_);
                    if crate::leanh::lean_obj_tag(v___x_1655_) == 0 {
                        v_a_1656_ = crate::leanh::lean_ctor_get(v___x_1655_, 0);
                        crate::leanh::lean_inc(v_a_1656_);
                        crate::leanh::lean_dec_ref_known(v___x_1655_, 1);
                        crate::leanh::lean_inc_ref(v_value_1652_);
                        crate::leanh::lean_inc_ref(v_post_1566_);
                        crate::leanh::lean_inc_ref(v_pre_1564_);
                        v___x_1657_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_value_1652_, v___y_1567_, v___y_1568_, v___y_1569_);
                        if crate::leanh::lean_obj_tag(v___x_1657_) == 0 {
                            v_a_1658_ = crate::leanh::lean_ctor_get(v___x_1657_, 0);
                            crate::leanh::lean_inc(v_a_1658_);
                            crate::leanh::lean_dec_ref_known(v___x_1657_, 1);
                            crate::leanh::lean_inc_ref(v_body_1653_);
                            crate::leanh::lean_inc_ref(v_post_1566_);
                            crate::leanh::lean_inc_ref(v_pre_1564_);
                            v___x_1659_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_body_1653_, v___y_1567_, v___y_1568_, v___y_1569_);
                            if crate::leanh::lean_obj_tag(v___x_1659_) == 0 {
                                v_a_1660_ = crate::leanh::lean_ctor_get(v___x_1659_, 0);
                                crate::leanh::lean_inc(v_a_1660_);
                                crate::leanh::lean_dec_ref_known(v___x_1659_, 1);
                                v___x_1661_ = lean_ptr_addr(v_type_1651_);
                                v___x_1662_ = lean_ptr_addr(v_a_1656_);
                                v___x_1663_ = lean_usize_dec_eq(v___x_1661_, v___x_1662_);
                                if v___x_1663_ == 0 {
                                    v___y_1572_ = v___y_1621_;
                                    v___y_1573_ = v_a_1658_;
                                    v___y_1574_ = v_a_1656_;
                                    v___y_1575_ = v_nondep_1654_;
                                    v___y_1576_ = v_body_1653_;
                                    v___y_1577_ = v_declName_1650_;
                                    v___y_1578_ = v_a_1660_;
                                    v___y_1579_ = v___x_1663_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1664_ = lean_ptr_addr(v_value_1652_);
                                    v___x_1665_ = lean_ptr_addr(v_a_1658_);
                                    v___x_1666_ = lean_usize_dec_eq(v___x_1664_, v___x_1665_);
                                    v___y_1572_ = v___y_1621_;
                                    v___y_1573_ = v_a_1658_;
                                    v___y_1574_ = v_a_1656_;
                                    v___y_1575_ = v_nondep_1654_;
                                    v___y_1576_ = v_body_1653_;
                                    v___y_1577_ = v_declName_1650_;
                                    v___y_1578_ = v_a_1660_;
                                    v___y_1579_ = v___x_1666_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1658_);
                                crate::leanh::lean_dec(v_a_1656_);
                                crate::leanh::lean_dec_ref(v_body_1653_);
                                crate::leanh::lean_dec(v_declName_1650_);
                                crate::leanh::lean_dec_ref_known(v___y_1621_, 4);
                                crate::leanh::lean_dec_ref(v_post_1566_);
                                crate::leanh::lean_dec_ref(v_pre_1564_);
                                return v___x_1659_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1656_);
                            crate::leanh::lean_dec_ref(v_body_1653_);
                            crate::leanh::lean_dec(v_declName_1650_);
                            crate::leanh::lean_dec_ref_known(v___y_1621_, 4);
                            crate::leanh::lean_dec_ref(v_post_1566_);
                            crate::leanh::lean_dec_ref(v_pre_1564_);
                            return v___x_1657_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_1653_);
                        crate::leanh::lean_dec(v_declName_1650_);
                        crate::leanh::lean_dec_ref_known(v___y_1621_, 4);
                        crate::leanh::lean_dec_ref(v_post_1566_);
                        crate::leanh::lean_dec_ref(v_pre_1564_);
                        return v___x_1655_;
                    }
                }
                5 => {
                    v_dummy_1667_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0);
                    v_nargs_1668_ = l_Lean_Expr_getAppNumArgs(v___y_1621_);
                    crate::leanh::lean_inc(v_nargs_1668_);
                    v___x_1669_ = lean_mk_array(v_nargs_1668_, v_dummy_1667_);
                    v___x_1670_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1671_ = lean_nat_sub(v_nargs_1668_, v___x_1670_);
                    crate::leanh::lean_dec(v_nargs_1668_);
                    v___x_1672_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(v_pre_1564_, v_post_1566_, v___y_1621_, v___x_1669_, v___x_1671_, v___y_1567_, v___y_1568_, v___y_1569_);
                    return v___x_1672_;
                }
                10 => {
                    v_data_1673_ = crate::leanh::lean_ctor_get(v___y_1621_, 0);
                    v_expr_1674_ = crate::leanh::lean_ctor_get(v___y_1621_, 1);
                    crate::leanh::lean_inc_ref(v_expr_1674_);
                    crate::leanh::lean_inc_ref(v_post_1566_);
                    crate::leanh::lean_inc_ref(v_pre_1564_);
                    v___x_1675_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_expr_1674_, v___y_1567_, v___y_1568_, v___y_1569_);
                    if crate::leanh::lean_obj_tag(v___x_1675_) == 0 {
                        v_a_1676_ = crate::leanh::lean_ctor_get(v___x_1675_, 0);
                        crate::leanh::lean_inc(v_a_1676_);
                        crate::leanh::lean_dec_ref_known(v___x_1675_, 1);
                        v___x_1677_ = lean_ptr_addr(v_expr_1674_);
                        v___x_1678_ = lean_ptr_addr(v_a_1676_);
                        v___x_1679_ = lean_usize_dec_eq(v___x_1677_, v___x_1678_);
                        if v___x_1679_ == 0 {
                            crate::leanh::lean_inc(v_data_1673_);
                            crate::leanh::lean_dec_ref_known(v___y_1621_, 2);
                            v___x_1680_ = l_Lean_Expr_mdata___override(v_data_1673_, v_a_1676_);
                            v___x_1681_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___x_1680_, v___y_1567_, v___y_1568_, v___y_1569_);
                            return v___x_1681_;
                        } else {
                            crate::leanh::lean_dec(v_a_1676_);
                            v___x_1682_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___y_1621_, v___y_1567_, v___y_1568_, v___y_1569_);
                            return v___x_1682_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_1621_, 2);
                        crate::leanh::lean_dec_ref(v_post_1566_);
                        crate::leanh::lean_dec_ref(v_pre_1564_);
                        return v___x_1675_;
                    }
                }
                11 => {
                    v_typeName_1683_ = crate::leanh::lean_ctor_get(v___y_1621_, 0);
                    v_idx_1684_ = crate::leanh::lean_ctor_get(v___y_1621_, 1);
                    v_struct_1685_ = crate::leanh::lean_ctor_get(v___y_1621_, 2);
                    crate::leanh::lean_inc_ref(v_struct_1685_);
                    crate::leanh::lean_inc_ref(v_post_1566_);
                    crate::leanh::lean_inc_ref(v_pre_1564_);
                    v___x_1686_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_struct_1685_, v___y_1567_, v___y_1568_, v___y_1569_);
                    if crate::leanh::lean_obj_tag(v___x_1686_) == 0 {
                        v_a_1687_ = crate::leanh::lean_ctor_get(v___x_1686_, 0);
                        crate::leanh::lean_inc(v_a_1687_);
                        crate::leanh::lean_dec_ref_known(v___x_1686_, 1);
                        v___x_1688_ = lean_ptr_addr(v_struct_1685_);
                        v___x_1689_ = lean_ptr_addr(v_a_1687_);
                        v___x_1690_ = lean_usize_dec_eq(v___x_1688_, v___x_1689_);
                        if v___x_1690_ == 0 {
                            crate::leanh::lean_inc(v_idx_1684_);
                            crate::leanh::lean_inc(v_typeName_1683_);
                            crate::leanh::lean_dec_ref_known(v___y_1621_, 3);
                            v___x_1691_ = l_Lean_Expr_proj___override(
                                v_typeName_1683_,
                                v_idx_1684_,
                                v_a_1687_,
                            );
                            v___x_1692_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___x_1691_, v___y_1567_, v___y_1568_, v___y_1569_);
                            return v___x_1692_;
                        } else {
                            crate::leanh::lean_dec(v_a_1687_);
                            v___x_1693_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___y_1621_, v___y_1567_, v___y_1568_, v___y_1569_);
                            return v___x_1693_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_1621_, 3);
                        crate::leanh::lean_dec_ref(v_post_1566_);
                        crate::leanh::lean_dec_ref(v_pre_1564_);
                        return v___x_1686_;
                    }
                }
                _ => {
                    v___x_1694_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___y_1621_, v___y_1567_, v___y_1568_, v___y_1569_);
                    return v___x_1694_;
                }
            },
            6 => {
                return v___x_1697_;
            }
            7 => {
                if v_isShared_1709_ == 0 {
                    v___x_1711_ = v___x_1708_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1712_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
                    v___x_1711_ = v_reuseFailAlloc_1712_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1711_;
            }
            9 => {
                if v_isShared_1717_ == 0 {
                    v___x_1719_ = v___x_1716_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1720_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
                    v___x_1719_ = v_reuseFailAlloc_1720_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___boxed(
    mut v___x_1722_: *mut crate::leanh::LeanObject,
    mut v_pre_1723_: *mut crate::leanh::LeanObject,
    mut v_e_1724_: *mut crate::leanh::LeanObject,
    mut v_post_1725_: *mut crate::leanh::LeanObject,
    mut v___y_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
    mut v___y_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1730_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1(v___x_1722_, v_pre_1723_, v_e_1724_, v_post_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
    crate::leanh::lean_dec(v___y_1728_);
    crate::leanh::lean_dec_ref(v___y_1727_);
    crate::leanh::lean_dec(v___y_1726_);
    return v_res_1730_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(
    mut v_pre_1731_: *mut crate::leanh::LeanObject,
    mut v_post_1732_: *mut crate::leanh::LeanObject,
    mut v_e_1733_: *mut crate::leanh::LeanObject,
    mut v_a_1734_: *mut crate::leanh::LeanObject,
    mut v___y_1735_: *mut crate::leanh::LeanObject,
    mut v___y_1736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1753_: u8 = 0;
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1757_: u8 = 0;
    let mut v_unused_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1762_: u8 = 0;
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut v_val_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1771_: u8 = 0;
    let mut v_a_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_1734_);
                v___x_1738_ = crate::leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_1738_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1738_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1738_, 2, v_a_1734_);
                v___x_1739_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(crate::leanh::lean_box(0), v___x_1738_, v___y_1735_, v___y_1736_);
                if crate::leanh::lean_obj_tag(v___x_1739_) == 0 {
                    v_a_1740_ = crate::leanh::lean_ctor_get(v___x_1739_, 0);
                    v_isSharedCheck_1771_ = (!crate::leanh::lean_is_exclusive(v___x_1739_)) as u8;
                    if v_isSharedCheck_1771_ == 0 {
                        v___x_1742_ = v___x_1739_;
                        v_isShared_1743_ = v_isSharedCheck_1771_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1740_);
                        crate::leanh::lean_dec(v___x_1739_);
                        v___x_1742_ = crate::leanh::lean_box(0);
                        v_isShared_1743_ = v_isSharedCheck_1771_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1733_);
                    crate::leanh::lean_dec_ref(v_post_1732_);
                    crate::leanh::lean_dec_ref(v_pre_1731_);
                    v_a_1772_ = crate::leanh::lean_ctor_get(v___x_1739_, 0);
                    v_isSharedCheck_1779_ = (!crate::leanh::lean_is_exclusive(v___x_1739_)) as u8;
                    if v_isSharedCheck_1779_ == 0 {
                        v___x_1774_ = v___x_1739_;
                        v_isShared_1775_ = v_isSharedCheck_1779_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1772_);
                        crate::leanh::lean_dec(v___x_1739_);
                        v___x_1774_ = crate::leanh::lean_box(0);
                        v_isShared_1775_ = v_isSharedCheck_1779_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_a_1740_, v_e_1733_);
                crate::leanh::lean_dec(v_a_1740_);
                if crate::leanh::lean_obj_tag(v___x_1744_) == 0 {
                    crate::leanh::lean_del_object(v___x_1742_);
                    v___x_1745_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___closed__0;
                    crate::leanh::lean_inc_ref(v_e_1733_);
                    v___f_1746_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___boxed as *mut core::ffi::c_void, 8, 4);
                    crate::leanh::lean_closure_set(v___f_1746_, 0, v___x_1745_);
                    crate::leanh::lean_closure_set(v___f_1746_, 1, v_pre_1731_);
                    crate::leanh::lean_closure_set(v___f_1746_, 2, v_e_1733_);
                    crate::leanh::lean_closure_set(v___f_1746_, 3, v_post_1732_);
                    v___x_1747_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v___f_1746_, v_a_1734_, v___y_1735_, v___y_1736_);
                    if crate::leanh::lean_obj_tag(v___x_1747_) == 0 {
                        v_a_1748_ = crate::leanh::lean_ctor_get(v___x_1747_, 0);
                        crate::leanh::lean_inc_n(v_a_1748_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1747_, 1);
                        crate::leanh::lean_inc(v_a_1734_);
                        v___f_1749_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        crate::leanh::lean_closure_set(v___f_1749_, 0, v_a_1734_);
                        crate::leanh::lean_closure_set(v___f_1749_, 1, v_e_1733_);
                        crate::leanh::lean_closure_set(v___f_1749_, 2, v_a_1748_);
                        v___x_1750_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(crate::leanh::lean_box(0), v___f_1749_, v___y_1735_, v___y_1736_);
                        if crate::leanh::lean_obj_tag(v___x_1750_) == 0 {
                            v_isSharedCheck_1757_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1750_)) as u8;
                            if v_isSharedCheck_1757_ == 0 {
                                v_unused_1758_ = crate::leanh::lean_ctor_get(v___x_1750_, 0);
                                crate::leanh::lean_dec(v_unused_1758_);
                                v___x_1752_ = v___x_1750_;
                                v_isShared_1753_ = v_isSharedCheck_1757_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1750_);
                                v___x_1752_ = crate::leanh::lean_box(0);
                                v_isShared_1753_ = v_isSharedCheck_1757_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1748_);
                            v_a_1759_ = crate::leanh::lean_ctor_get(v___x_1750_, 0);
                            v_isSharedCheck_1766_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1750_)) as u8;
                            if v_isSharedCheck_1766_ == 0 {
                                v___x_1761_ = v___x_1750_;
                                v_isShared_1762_ = v_isSharedCheck_1766_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1759_);
                                crate::leanh::lean_dec(v___x_1750_);
                                v___x_1761_ = crate::leanh::lean_box(0);
                                v_isShared_1762_ = v_isSharedCheck_1766_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1733_);
                        return v___x_1747_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1733_);
                    crate::leanh::lean_dec_ref(v_post_1732_);
                    crate::leanh::lean_dec_ref(v_pre_1731_);
                    v_val_1767_ = crate::leanh::lean_ctor_get(v___x_1744_, 0);
                    crate::leanh::lean_inc(v_val_1767_);
                    crate::leanh::lean_dec_ref_known(v___x_1744_, 1);
                    if v_isShared_1743_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1742_, 0, v_val_1767_);
                        v___x_1769_ = v___x_1742_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_val_1767_);
                        v___x_1769_ = v_reuseFailAlloc_1770_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1753_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1752_, 0, v_a_1748_);
                    v___x_1755_ = v___x_1752_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1756_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1748_);
                    v___x_1755_ = v_reuseFailAlloc_1756_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1755_;
            }
            4 => {
                if v_isShared_1762_ == 0 {
                    v___x_1764_ = v___x_1761_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1765_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
                    v___x_1764_ = v_reuseFailAlloc_1765_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1764_;
            }
            6 => {
                return v___x_1769_;
            }
            7 => {
                if v_isShared_1775_ == 0 {
                    v___x_1777_ = v___x_1774_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1778_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
                    v___x_1777_ = v_reuseFailAlloc_1778_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(
    mut v_pre_1780_: *mut crate::leanh::LeanObject,
    mut v_post_1781_: *mut crate::leanh::LeanObject,
    mut v_e_1782_: *mut crate::leanh::LeanObject,
    mut v_a_1783_: *mut crate::leanh::LeanObject,
    mut v___y_1784_: *mut crate::leanh::LeanObject,
    mut v___y_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1791_: u8 = 0;
    let mut v_e_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v_a_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1810_: u8 = 0;
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_post_1781_);
                crate::leanh::lean_inc(v___y_1785_);
                crate::leanh::lean_inc_ref(v___y_1784_);
                crate::leanh::lean_inc_ref(v_e_1782_);
                v___x_1787_ = crate::leanh::lean_apply_4(
                    v_post_1781_,
                    v_e_1782_,
                    v___y_1784_,
                    v___y_1785_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1787_) == 0 {
                    v_a_1788_ = crate::leanh::lean_ctor_get(v___x_1787_, 0);
                    v_isSharedCheck_1806_ = (!crate::leanh::lean_is_exclusive(v___x_1787_)) as u8;
                    if v_isSharedCheck_1806_ == 0 {
                        v___x_1790_ = v___x_1787_;
                        v_isShared_1791_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1788_);
                        crate::leanh::lean_dec(v___x_1787_);
                        v___x_1790_ = crate::leanh::lean_box(0);
                        v_isShared_1791_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1782_);
                    crate::leanh::lean_dec_ref(v_post_1781_);
                    crate::leanh::lean_dec_ref(v_pre_1780_);
                    v_a_1807_ = crate::leanh::lean_ctor_get(v___x_1787_, 0);
                    v_isSharedCheck_1814_ = (!crate::leanh::lean_is_exclusive(v___x_1787_)) as u8;
                    if v_isSharedCheck_1814_ == 0 {
                        v___x_1809_ = v___x_1787_;
                        v_isShared_1810_ = v_isSharedCheck_1814_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1807_);
                        crate::leanh::lean_dec(v___x_1787_);
                        v___x_1809_ = crate::leanh::lean_box(0);
                        v_isShared_1810_ = v_isSharedCheck_1814_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_1788_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_e_1782_);
                    crate::leanh::lean_dec_ref(v_post_1781_);
                    crate::leanh::lean_dec_ref(v_pre_1780_);
                    v_e_1792_ = crate::leanh::lean_ctor_get(v_a_1788_, 0);
                    crate::leanh::lean_inc_ref(v_e_1792_);
                    crate::leanh::lean_dec_ref_known(v_a_1788_, 1);
                    if v_isShared_1791_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1790_, 0, v_e_1792_);
                        v___x_1794_ = v___x_1790_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1795_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_e_1792_);
                        v___x_1794_ = v_reuseFailAlloc_1795_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_1790_);
                    crate::leanh::lean_dec_ref(v_e_1782_);
                    v_e_1796_ = crate::leanh::lean_ctor_get(v_a_1788_, 0);
                    crate::leanh::lean_inc_ref(v_e_1796_);
                    crate::leanh::lean_dec_ref_known(v_a_1788_, 1);
                    v___x_1797_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1780_, v_post_1781_, v_e_1796_, v_a_1783_, v___y_1784_, v___y_1785_);
                    return v___x_1797_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_post_1781_);
                    crate::leanh::lean_dec_ref(v_pre_1780_);
                    v_e_x3f_1798_ = crate::leanh::lean_ctor_get(v_a_1788_, 0);
                    crate::leanh::lean_inc(v_e_x3f_1798_);
                    crate::leanh::lean_dec_ref_known(v_a_1788_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_1798_) == 0 {
                        if v_isShared_1791_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1790_, 0, v_e_1782_);
                            v___x_1800_ = v___x_1790_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1801_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_e_1782_);
                            v___x_1800_ = v_reuseFailAlloc_1801_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1782_);
                        v_val_1802_ = crate::leanh::lean_ctor_get(v_e_x3f_1798_, 0);
                        crate::leanh::lean_inc(v_val_1802_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_1798_, 1);
                        if v_isShared_1791_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1790_, 0, v_val_1802_);
                            v___x_1804_ = v___x_1790_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1805_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_val_1802_);
                            v___x_1804_ = v_reuseFailAlloc_1805_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_1794_;
            }
            3 => {
                return v___x_1800_;
            }
            4 => {
                return v___x_1804_;
            }
            5 => {
                if v_isShared_1810_ == 0 {
                    v___x_1812_ = v___x_1809_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1813_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
                    v___x_1812_ = v_reuseFailAlloc_1813_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2___boxed(
    mut v_pre_1815_: *mut crate::leanh::LeanObject,
    mut v_post_1816_: *mut crate::leanh::LeanObject,
    mut v_e_1817_: *mut crate::leanh::LeanObject,
    mut v_a_1818_: *mut crate::leanh::LeanObject,
    mut v___y_1819_: *mut crate::leanh::LeanObject,
    mut v___y_1820_: *mut crate::leanh::LeanObject,
    mut v___y_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1822_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1815_, v_post_1816_, v_e_1817_, v_a_1818_, v___y_1819_, v___y_1820_);
    crate::leanh::lean_dec(v___y_1820_);
    crate::leanh::lean_dec_ref(v___y_1819_);
    crate::leanh::lean_dec(v_a_1818_);
    return v_res_1822_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1___boxed(
    mut v_pre_1823_: *mut crate::leanh::LeanObject,
    mut v_post_1824_: *mut crate::leanh::LeanObject,
    mut v_sz_1825_: *mut crate::leanh::LeanObject,
    mut v_i_1826_: *mut crate::leanh::LeanObject,
    mut v_bs_1827_: *mut crate::leanh::LeanObject,
    mut v___y_1828_: *mut crate::leanh::LeanObject,
    mut v___y_1829_: *mut crate::leanh::LeanObject,
    mut v___y_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1832_: usize = 0;
    let mut v_i_boxed_1833_: usize = 0;
    let mut v_res_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1832_ = crate::leanh::lean_unbox_usize(v_sz_1825_);
    crate::leanh::lean_dec(v_sz_1825_);
    v_i_boxed_1833_ = crate::leanh::lean_unbox_usize(v_i_1826_);
    crate::leanh::lean_dec(v_i_1826_);
    v_res_1834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(v_pre_1823_, v_post_1824_, v_sz_boxed_1832_, v_i_boxed_1833_, v_bs_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
    crate::leanh::lean_dec(v___y_1830_);
    crate::leanh::lean_dec_ref(v___y_1829_);
    crate::leanh::lean_dec(v___y_1828_);
    return v_res_1834_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4___boxed(
    mut v_pre_1835_: *mut crate::leanh::LeanObject,
    mut v_post_1836_: *mut crate::leanh::LeanObject,
    mut v_x_1837_: *mut crate::leanh::LeanObject,
    mut v_x_1838_: *mut crate::leanh::LeanObject,
    mut v_x_1839_: *mut crate::leanh::LeanObject,
    mut v___y_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1844_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(v_pre_1835_, v_post_1836_, v_x_1837_, v_x_1838_, v_x_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
    crate::leanh::lean_dec(v___y_1842_);
    crate::leanh::lean_dec_ref(v___y_1841_);
    crate::leanh::lean_dec(v___y_1840_);
    return v_res_1844_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___boxed(
    mut v_pre_1845_: *mut crate::leanh::LeanObject,
    mut v_post_1846_: *mut crate::leanh::LeanObject,
    mut v_e_1847_: *mut crate::leanh::LeanObject,
    mut v_a_1848_: *mut crate::leanh::LeanObject,
    mut v___y_1849_: *mut crate::leanh::LeanObject,
    mut v___y_1850_: *mut crate::leanh::LeanObject,
    mut v___y_1851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1852_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1845_, v_post_1846_, v_e_1847_, v_a_1848_, v___y_1849_, v___y_1850_);
    crate::leanh::lean_dec(v___y_1850_);
    crate::leanh::lean_dec_ref(v___y_1849_);
    crate::leanh::lean_dec(v_a_1848_);
    return v_res_1852_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(
    mut v_00_u03b1_1853_: *mut crate::leanh::LeanObject,
    mut v_x_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
    mut v___y_1856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1858_ = crate::leanh::lean_apply_1(v_x_1854_, crate::leanh::lean_box(0));
    v___x_1859_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1859_, 0, v___x_1858_);
    return v___x_1859_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0___boxed(
    mut v_00_u03b1_1860_: *mut crate::leanh::LeanObject,
    mut v_x_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1865_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(
        v_00_u03b1_1860_,
        v_x_1861_,
        v___y_1862_,
        v___y_1863_,
    );
    crate::leanh::lean_dec(v___y_1863_);
    crate::leanh::lean_dec_ref(v___y_1862_);
    return v_res_1865_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1866_ = crate::leanh::lean_box(0);
    v___x_1867_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1868_ = lean_mk_array(v___x_1867_, v___x_1866_);
    return v___x_1868_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1869_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0_once
        ),
        _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0,
    );
    v___x_1870_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1871_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_1870_);
    crate::leanh::lean_ctor_set(v___x_1871_, 1, v___x_1869_);
    return v___x_1871_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1872_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1_once
        ),
        _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1,
    );
    v___x_1873_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_1873_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1873_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1873_, 2, v___x_1872_);
    return v___x_1873_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(
    mut v_input_1874_: *mut crate::leanh::LeanObject,
    mut v_pre_1875_: *mut crate::leanh::LeanObject,
    mut v_post_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
    mut v___y_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1889_: u8 = 0;
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut v_unused_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1880_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2_once), _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2);
                v___x_1881_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(
                    crate::leanh::lean_box(0),
                    v___x_1880_,
                    v___y_1877_,
                    v___y_1878_,
                );
                v_a_1882_ = crate::leanh::lean_ctor_get(v___x_1881_, 0);
                crate::leanh::lean_inc(v_a_1882_);
                crate::leanh::lean_dec_ref(v___x_1881_);
                v___x_1883_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1875_, v_post_1876_, v_input_1874_, v_a_1882_, v___y_1877_, v___y_1878_);
                if crate::leanh::lean_obj_tag(v___x_1883_) == 0 {
                    v_a_1884_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                    crate::leanh::lean_inc(v_a_1884_);
                    crate::leanh::lean_dec_ref_known(v___x_1883_, 1);
                    v___x_1885_ = crate::leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_1885_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_1885_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_1885_, 2, v_a_1882_);
                    v___x_1886_ =
                        l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(
                            crate::leanh::lean_box(0),
                            v___x_1885_,
                            v___y_1877_,
                            v___y_1878_,
                        );
                    v_isSharedCheck_1893_ = (!crate::leanh::lean_is_exclusive(v___x_1886_)) as u8;
                    if v_isSharedCheck_1893_ == 0 {
                        v_unused_1894_ = crate::leanh::lean_ctor_get(v___x_1886_, 0);
                        crate::leanh::lean_dec(v_unused_1894_);
                        v___x_1888_ = v___x_1886_;
                        v_isShared_1889_ = v_isSharedCheck_1893_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1886_);
                        v___x_1888_ = crate::leanh::lean_box(0);
                        v_isShared_1889_ = v_isSharedCheck_1893_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1882_);
                    return v___x_1883_;
                }
            }
            1 => {
                if v_isShared_1889_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1888_, 0, v_a_1884_);
                    v___x_1891_ = v___x_1888_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1892_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1884_);
                    v___x_1891_ = v_reuseFailAlloc_1892_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___boxed(
    mut v_input_1895_: *mut crate::leanh::LeanObject,
    mut v_pre_1896_: *mut crate::leanh::LeanObject,
    mut v_post_1897_: *mut crate::leanh::LeanObject,
    mut v___y_1898_: *mut crate::leanh::LeanObject,
    mut v___y_1899_: *mut crate::leanh::LeanObject,
    mut v___y_1900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1901_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(
        v_input_1895_,
        v_pre_1896_,
        v_post_1897_,
        v___y_1898_,
        v___y_1899_,
    );
    crate::leanh::lean_dec(v___y_1899_);
    crate::leanh::lean_dec_ref(v___y_1898_);
    return v_res_1901_;
}
pub unsafe fn l_Lean_Meta_deltaExpand(
    mut v_e_1903_: *mut crate::leanh::LeanObject,
    mut v_p_1904_: *mut crate::leanh::LeanObject,
    mut v_allowOpaque_1905_: u8,
    mut v_a_1906_: *mut crate::leanh::LeanObject,
    mut v_a_1907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1909_ = crate::leanh::lean_box((v_allowOpaque_1905_) as usize);
    v___f_1910_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_deltaExpand___lam__0___boxed as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1910_, 0, v_p_1904_);
    crate::leanh::lean_closure_set(v___f_1910_, 1, v___x_1909_);
    v___f_1911_ = l_Lean_Meta_deltaExpand___closed__0;
    v___x_1912_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(
        v_e_1903_,
        v___f_1910_,
        v___f_1911_,
        v_a_1906_,
        v_a_1907_,
    );
    return v___x_1912_;
}
pub unsafe fn l_Lean_Meta_deltaExpand___boxed(
    mut v_e_1913_: *mut crate::leanh::LeanObject,
    mut v_p_1914_: *mut crate::leanh::LeanObject,
    mut v_allowOpaque_1915_: *mut crate::leanh::LeanObject,
    mut v_a_1916_: *mut crate::leanh::LeanObject,
    mut v_a_1917_: *mut crate::leanh::LeanObject,
    mut v_a_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowOpaque_boxed_1919_: u8 = 0;
    let mut v_res_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowOpaque_boxed_1919_ = (crate::leanh::lean_unbox(v_allowOpaque_1915_) as u8);
    v_res_1920_ = l_Lean_Meta_deltaExpand(
        v_e_1913_,
        v_p_1914_,
        v_allowOpaque_boxed_1919_,
        v_a_1916_,
        v_a_1917_,
    );
    crate::leanh::lean_dec(v_a_1917_);
    crate::leanh::lean_dec_ref(v_a_1916_);
    return v_res_1920_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3(
    mut v_00_u03b2_1921_: *mut crate::leanh::LeanObject,
    mut v_m_1922_: *mut crate::leanh::LeanObject,
    mut v_a_1923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1924_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_m_1922_, v_a_1923_);
    return v___x_1924_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_1925_: *mut crate::leanh::LeanObject,
    mut v_m_1926_: *mut crate::leanh::LeanObject,
    mut v_a_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1928_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3(v_00_u03b2_1925_, v_m_1926_, v_a_1927_);
    crate::leanh::lean_dec_ref(v_a_1927_);
    crate::leanh::lean_dec_ref(v_m_1926_);
    return v_res_1928_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7(
    mut v_00_u03b1_1929_: *mut crate::leanh::LeanObject,
    mut v_ref_1930_: *mut crate::leanh::LeanObject,
    mut v___y_1931_: *mut crate::leanh::LeanObject,
    mut v___y_1932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1934_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1930_);
    return v___x_1934_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___boxed(
    mut v_00_u03b1_1935_: *mut crate::leanh::LeanObject,
    mut v_ref_1936_: *mut crate::leanh::LeanObject,
    mut v___y_1937_: *mut crate::leanh::LeanObject,
    mut v___y_1938_: *mut crate::leanh::LeanObject,
    mut v___y_1939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1940_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1935_, v_ref_1936_, v___y_1937_, v___y_1938_);
    crate::leanh::lean_dec(v___y_1938_);
    crate::leanh::lean_dec_ref(v___y_1937_);
    return v_res_1940_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8(
    mut v_00_u03b1_1941_: *mut crate::leanh::LeanObject,
    mut v___y_1942_: *mut crate::leanh::LeanObject,
    mut v___y_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg();
    return v___x_1945_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___boxed(
    mut v_00_u03b1_1946_: *mut crate::leanh::LeanObject,
    mut v___y_1947_: *mut crate::leanh::LeanObject,
    mut v___y_1948_: *mut crate::leanh::LeanObject,
    mut v___y_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1950_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1946_, v___y_1947_, v___y_1948_);
    crate::leanh::lean_dec(v___y_1948_);
    crate::leanh::lean_dec_ref(v___y_1947_);
    return v_res_1950_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(
    mut v_00_u03b1_1951_: *mut crate::leanh::LeanObject,
    mut v_x_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1957_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v_x_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
    return v___x_1957_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___boxed(
    mut v_00_u03b1_1958_: *mut crate::leanh::LeanObject,
    mut v_x_1959_: *mut crate::leanh::LeanObject,
    mut v___y_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
    mut v___y_1962_: *mut crate::leanh::LeanObject,
    mut v___y_1963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1964_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(v_00_u03b1_1958_, v_x_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
    crate::leanh::lean_dec(v___y_1962_);
    crate::leanh::lean_dec_ref(v___y_1961_);
    crate::leanh::lean_dec(v___y_1960_);
    return v_res_1964_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6(
    mut v_00_u03b2_1965_: *mut crate::leanh::LeanObject,
    mut v_m_1966_: *mut crate::leanh::LeanObject,
    mut v_a_1967_: *mut crate::leanh::LeanObject,
    mut v_b_1968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1969_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v_m_1966_, v_a_1967_, v_b_1968_);
    return v___x_1969_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(
    mut v_00_u03b2_1970_: *mut crate::leanh::LeanObject,
    mut v_a_1971_: *mut crate::leanh::LeanObject,
    mut v_x_1972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1973_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1971_, v_x_1972_);
    return v___x_1973_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___boxed(
    mut v_00_u03b2_1974_: *mut crate::leanh::LeanObject,
    mut v_a_1975_: *mut crate::leanh::LeanObject,
    mut v_x_1976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1977_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1974_, v_a_1975_, v_x_1976_);
    crate::leanh::lean_dec(v_x_1976_);
    crate::leanh::lean_dec_ref(v_a_1975_);
    return v_res_1977_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10(
    mut v_00_u03b2_1978_: *mut crate::leanh::LeanObject,
    mut v_a_1979_: *mut crate::leanh::LeanObject,
    mut v_x_1980_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1981_: u8 = 0;
    v___x_1981_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1979_, v_x_1980_);
    return v___x_1981_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___boxed(
    mut v_00_u03b2_1982_: *mut crate::leanh::LeanObject,
    mut v_a_1983_: *mut crate::leanh::LeanObject,
    mut v_x_1984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1985_: u8 = 0;
    let mut v_r_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1985_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1982_, v_a_1983_, v_x_1984_);
    crate::leanh::lean_dec(v_x_1984_);
    crate::leanh::lean_dec_ref(v_a_1983_);
    v_r_1986_ = crate::leanh::lean_box((v_res_1985_) as usize);
    return v_r_1986_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11(
    mut v_00_u03b2_1987_: *mut crate::leanh::LeanObject,
    mut v_data_1988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1989_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1988_);
    return v___x_1989_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12(
    mut v_00_u03b2_1990_: *mut crate::leanh::LeanObject,
    mut v_a_1991_: *mut crate::leanh::LeanObject,
    mut v_b_1992_: *mut crate::leanh::LeanObject,
    mut v_x_1993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1994_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1991_, v_b_1992_, v_x_1993_);
    return v___x_1994_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12(
    mut v_00_u03b2_1995_: *mut crate::leanh::LeanObject,
    mut v_i_1996_: *mut crate::leanh::LeanObject,
    mut v_source_1997_: *mut crate::leanh::LeanObject,
    mut v_target_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1999_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1996_, v_source_1997_, v_target_1998_);
    return v___x_1999_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(
    mut v_00_u03b2_2000_: *mut crate::leanh::LeanObject,
    mut v_x_2001_: *mut crate::leanh::LeanObject,
    mut v_x_2002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2003_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_2001_, v_x_2002_);
    return v___x_2003_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(
    mut v_mvarId_2004_: *mut crate::leanh::LeanObject,
    mut v_x_2005_: *mut crate::leanh::LeanObject,
    mut v___y_2006_: *mut crate::leanh::LeanObject,
    mut v___y_2007_: *mut crate::leanh::LeanObject,
    mut v___y_2008_: *mut crate::leanh::LeanObject,
    mut v___y_2009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2015_: u8 = 0;
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut v_a_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2023_: u8 = 0;
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2027_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2011_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_2004_,
                    v_x_2005_,
                    v___y_2006_,
                    v___y_2007_,
                    v___y_2008_,
                    v___y_2009_,
                );
                if crate::leanh::lean_obj_tag(v___x_2011_) == 0 {
                    v_a_2012_ = crate::leanh::lean_ctor_get(v___x_2011_, 0);
                    v_isSharedCheck_2019_ = (!crate::leanh::lean_is_exclusive(v___x_2011_)) as u8;
                    if v_isSharedCheck_2019_ == 0 {
                        v___x_2014_ = v___x_2011_;
                        v_isShared_2015_ = v_isSharedCheck_2019_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2012_);
                        crate::leanh::lean_dec(v___x_2011_);
                        v___x_2014_ = crate::leanh::lean_box(0);
                        v_isShared_2015_ = v_isSharedCheck_2019_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2020_ = crate::leanh::lean_ctor_get(v___x_2011_, 0);
                    v_isSharedCheck_2027_ = (!crate::leanh::lean_is_exclusive(v___x_2011_)) as u8;
                    if v_isSharedCheck_2027_ == 0 {
                        v___x_2022_ = v___x_2011_;
                        v_isShared_2023_ = v_isSharedCheck_2027_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2020_);
                        crate::leanh::lean_dec(v___x_2011_);
                        v___x_2022_ = crate::leanh::lean_box(0);
                        v_isShared_2023_ = v_isSharedCheck_2027_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2015_ == 0 {
                    v___x_2017_ = v___x_2014_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2018_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
                    v___x_2017_ = v_reuseFailAlloc_2018_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2017_;
            }
            3 => {
                if v_isShared_2023_ == 0 {
                    v___x_2025_ = v___x_2022_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2026_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
                    v___x_2025_ = v_reuseFailAlloc_2026_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg___boxed(
    mut v_mvarId_2028_: *mut crate::leanh::LeanObject,
    mut v_x_2029_: *mut crate::leanh::LeanObject,
    mut v___y_2030_: *mut crate::leanh::LeanObject,
    mut v___y_2031_: *mut crate::leanh::LeanObject,
    mut v___y_2032_: *mut crate::leanh::LeanObject,
    mut v___y_2033_: *mut crate::leanh::LeanObject,
    mut v___y_2034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2035_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(
        v_mvarId_2028_,
        v_x_2029_,
        v___y_2030_,
        v___y_2031_,
        v___y_2032_,
        v___y_2033_,
    );
    crate::leanh::lean_dec(v___y_2033_);
    crate::leanh::lean_dec_ref(v___y_2032_);
    crate::leanh::lean_dec(v___y_2031_);
    crate::leanh::lean_dec_ref(v___y_2030_);
    return v_res_2035_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0(
    mut v_00_u03b1_2036_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2037_: *mut crate::leanh::LeanObject,
    mut v_x_2038_: *mut crate::leanh::LeanObject,
    mut v___y_2039_: *mut crate::leanh::LeanObject,
    mut v___y_2040_: *mut crate::leanh::LeanObject,
    mut v___y_2041_: *mut crate::leanh::LeanObject,
    mut v___y_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(
        v_mvarId_2037_,
        v_x_2038_,
        v___y_2039_,
        v___y_2040_,
        v___y_2041_,
        v___y_2042_,
    );
    return v___x_2044_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___boxed(
    mut v_00_u03b1_2045_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2046_: *mut crate::leanh::LeanObject,
    mut v_x_2047_: *mut crate::leanh::LeanObject,
    mut v___y_2048_: *mut crate::leanh::LeanObject,
    mut v___y_2049_: *mut crate::leanh::LeanObject,
    mut v___y_2050_: *mut crate::leanh::LeanObject,
    mut v___y_2051_: *mut crate::leanh::LeanObject,
    mut v___y_2052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2053_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0(
        v_00_u03b1_2045_,
        v_mvarId_2046_,
        v_x_2047_,
        v___y_2048_,
        v___y_2049_,
        v___y_2050_,
        v___y_2051_,
    );
    crate::leanh::lean_dec(v___y_2051_);
    crate::leanh::lean_dec_ref(v___y_2050_);
    crate::leanh::lean_dec(v___y_2049_);
    crate::leanh::lean_dec_ref(v___y_2048_);
    return v_res_2053_;
}
pub unsafe fn l_Lean_MVarId_deltaTarget___lam__0(
    mut v_mvarId_2054_: *mut crate::leanh::LeanObject,
    mut v___x_2055_: *mut crate::leanh::LeanObject,
    mut v_p_2056_: *mut crate::leanh::LeanObject,
    mut v___y_2057_: *mut crate::leanh::LeanObject,
    mut v___y_2058_: *mut crate::leanh::LeanObject,
    mut v___y_2059_: *mut crate::leanh::LeanObject,
    mut v___y_2060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: u8 = 0;
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2072_: u8 = 0;
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2076_: u8 = 0;
    let mut v_a_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2080_: u8 = 0;
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut v_a_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2088_: u8 = 0;
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2092_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_2054_);
                v___x_2062_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2054_,
                    v___x_2055_,
                    v___y_2057_,
                    v___y_2058_,
                    v___y_2059_,
                    v___y_2060_,
                );
                if crate::leanh::lean_obj_tag(v___x_2062_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2062_, 1);
                    crate::leanh::lean_inc(v_mvarId_2054_);
                    v___x_2063_ = l_Lean_MVarId_getType(
                        v_mvarId_2054_,
                        v___y_2057_,
                        v___y_2058_,
                        v___y_2059_,
                        v___y_2060_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2063_) == 0 {
                        v_a_2064_ = crate::leanh::lean_ctor_get(v___x_2063_, 0);
                        crate::leanh::lean_inc(v_a_2064_);
                        crate::leanh::lean_dec_ref_known(v___x_2063_, 1);
                        v___x_2065_ = 0;
                        v___x_2066_ = l_Lean_Meta_deltaExpand(
                            v_a_2064_,
                            v_p_2056_,
                            v___x_2065_,
                            v___y_2059_,
                            v___y_2060_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2066_) == 0 {
                            v_a_2067_ = crate::leanh::lean_ctor_get(v___x_2066_, 0);
                            crate::leanh::lean_inc(v_a_2067_);
                            crate::leanh::lean_dec_ref_known(v___x_2066_, 1);
                            v___x_2068_ = l_Lean_MVarId_change(
                                v_mvarId_2054_,
                                v_a_2067_,
                                v___x_2065_,
                                v___y_2057_,
                                v___y_2058_,
                                v___y_2059_,
                                v___y_2060_,
                            );
                            return v___x_2068_;
                        } else {
                            crate::leanh::lean_dec(v_mvarId_2054_);
                            v_a_2069_ = crate::leanh::lean_ctor_get(v___x_2066_, 0);
                            v_isSharedCheck_2076_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2066_)) as u8;
                            if v_isSharedCheck_2076_ == 0 {
                                v___x_2071_ = v___x_2066_;
                                v_isShared_2072_ = v_isSharedCheck_2076_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2069_);
                                crate::leanh::lean_dec(v___x_2066_);
                                v___x_2071_ = crate::leanh::lean_box(0);
                                v_isShared_2072_ = v_isSharedCheck_2076_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_p_2056_);
                        crate::leanh::lean_dec(v_mvarId_2054_);
                        v_a_2077_ = crate::leanh::lean_ctor_get(v___x_2063_, 0);
                        v_isSharedCheck_2084_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2063_)) as u8;
                        if v_isSharedCheck_2084_ == 0 {
                            v___x_2079_ = v___x_2063_;
                            v_isShared_2080_ = v_isSharedCheck_2084_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2077_);
                            crate::leanh::lean_dec(v___x_2063_);
                            v___x_2079_ = crate::leanh::lean_box(0);
                            v_isShared_2080_ = v_isSharedCheck_2084_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_2056_);
                    crate::leanh::lean_dec(v_mvarId_2054_);
                    v_a_2085_ = crate::leanh::lean_ctor_get(v___x_2062_, 0);
                    v_isSharedCheck_2092_ = (!crate::leanh::lean_is_exclusive(v___x_2062_)) as u8;
                    if v_isSharedCheck_2092_ == 0 {
                        v___x_2087_ = v___x_2062_;
                        v_isShared_2088_ = v_isSharedCheck_2092_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2085_);
                        crate::leanh::lean_dec(v___x_2062_);
                        v___x_2087_ = crate::leanh::lean_box(0);
                        v_isShared_2088_ = v_isSharedCheck_2092_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2072_ == 0 {
                    v___x_2074_ = v___x_2071_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2075_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
                    v___x_2074_ = v_reuseFailAlloc_2075_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2074_;
            }
            3 => {
                if v_isShared_2080_ == 0 {
                    v___x_2082_ = v___x_2079_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2083_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
                    v___x_2082_ = v_reuseFailAlloc_2083_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2082_;
            }
            5 => {
                if v_isShared_2088_ == 0 {
                    v___x_2090_ = v___x_2087_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2091_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
                    v___x_2090_ = v_reuseFailAlloc_2091_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2090_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_deltaTarget___lam__0___boxed(
    mut v_mvarId_2093_: *mut crate::leanh::LeanObject,
    mut v___x_2094_: *mut crate::leanh::LeanObject,
    mut v_p_2095_: *mut crate::leanh::LeanObject,
    mut v___y_2096_: *mut crate::leanh::LeanObject,
    mut v___y_2097_: *mut crate::leanh::LeanObject,
    mut v___y_2098_: *mut crate::leanh::LeanObject,
    mut v___y_2099_: *mut crate::leanh::LeanObject,
    mut v___y_2100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2101_ = l_Lean_MVarId_deltaTarget___lam__0(
        v_mvarId_2093_,
        v___x_2094_,
        v_p_2095_,
        v___y_2096_,
        v___y_2097_,
        v___y_2098_,
        v___y_2099_,
    );
    crate::leanh::lean_dec(v___y_2099_);
    crate::leanh::lean_dec_ref(v___y_2098_);
    crate::leanh::lean_dec(v___y_2097_);
    crate::leanh::lean_dec_ref(v___y_2096_);
    return v_res_2101_;
}
pub unsafe fn l_Lean_MVarId_deltaTarget(
    mut v_mvarId_2105_: *mut crate::leanh::LeanObject,
    mut v_p_2106_: *mut crate::leanh::LeanObject,
    mut v_a_2107_: *mut crate::leanh::LeanObject,
    mut v_a_2108_: *mut crate::leanh::LeanObject,
    mut v_a_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2112_ = l_Lean_MVarId_deltaTarget___closed__1;
    crate::leanh::lean_inc(v_mvarId_2105_);
    v___f_2113_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_deltaTarget___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2113_, 0, v_mvarId_2105_);
    crate::leanh::lean_closure_set(v___f_2113_, 1, v___x_2112_);
    crate::leanh::lean_closure_set(v___f_2113_, 2, v_p_2106_);
    v___x_2114_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(
        v_mvarId_2105_,
        v___f_2113_,
        v_a_2107_,
        v_a_2108_,
        v_a_2109_,
        v_a_2110_,
    );
    return v___x_2114_;
}
pub unsafe fn l_Lean_MVarId_deltaTarget___boxed(
    mut v_mvarId_2115_: *mut crate::leanh::LeanObject,
    mut v_p_2116_: *mut crate::leanh::LeanObject,
    mut v_a_2117_: *mut crate::leanh::LeanObject,
    mut v_a_2118_: *mut crate::leanh::LeanObject,
    mut v_a_2119_: *mut crate::leanh::LeanObject,
    mut v_a_2120_: *mut crate::leanh::LeanObject,
    mut v_a_2121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2122_ = l_Lean_MVarId_deltaTarget(
        v_mvarId_2115_,
        v_p_2116_,
        v_a_2117_,
        v_a_2118_,
        v_a_2119_,
        v_a_2120_,
    );
    crate::leanh::lean_dec(v_a_2120_);
    crate::leanh::lean_dec_ref(v_a_2119_);
    crate::leanh::lean_dec(v_a_2118_);
    crate::leanh::lean_dec_ref(v_a_2117_);
    return v_res_2122_;
}
pub unsafe fn l_Lean_MVarId_deltaLocalDecl___lam__0(
    mut v_mvarId_2123_: *mut crate::leanh::LeanObject,
    mut v___x_2124_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2125_: *mut crate::leanh::LeanObject,
    mut v_p_2126_: *mut crate::leanh::LeanObject,
    mut v___y_2127_: *mut crate::leanh::LeanObject,
    mut v___y_2128_: *mut crate::leanh::LeanObject,
    mut v___y_2129_: *mut crate::leanh::LeanObject,
    mut v___y_2130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: u8 = 0;
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2142_: u8 = 0;
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2146_: u8 = 0;
    let mut v_a_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2150_: u8 = 0;
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2154_: u8 = 0;
    let mut v_a_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_2123_);
                v___x_2132_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2123_,
                    v___x_2124_,
                    v___y_2127_,
                    v___y_2128_,
                    v___y_2129_,
                    v___y_2130_,
                );
                if crate::leanh::lean_obj_tag(v___x_2132_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2132_, 1);
                    crate::leanh::lean_inc(v_fvarId_2125_);
                    v___x_2133_ = l_Lean_FVarId_getType___redArg(
                        v_fvarId_2125_,
                        v___y_2127_,
                        v___y_2129_,
                        v___y_2130_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2133_) == 0 {
                        v_a_2134_ = crate::leanh::lean_ctor_get(v___x_2133_, 0);
                        crate::leanh::lean_inc(v_a_2134_);
                        crate::leanh::lean_dec_ref_known(v___x_2133_, 1);
                        v___x_2135_ = 0;
                        v___x_2136_ = l_Lean_Meta_deltaExpand(
                            v_a_2134_,
                            v_p_2126_,
                            v___x_2135_,
                            v___y_2129_,
                            v___y_2130_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2136_) == 0 {
                            v_a_2137_ = crate::leanh::lean_ctor_get(v___x_2136_, 0);
                            crate::leanh::lean_inc(v_a_2137_);
                            crate::leanh::lean_dec_ref_known(v___x_2136_, 1);
                            v___x_2138_ = l_Lean_MVarId_changeLocalDecl(
                                v_mvarId_2123_,
                                v_fvarId_2125_,
                                v_a_2137_,
                                v___x_2135_,
                                v___y_2127_,
                                v___y_2128_,
                                v___y_2129_,
                                v___y_2130_,
                            );
                            return v___x_2138_;
                        } else {
                            crate::leanh::lean_dec(v_fvarId_2125_);
                            crate::leanh::lean_dec(v_mvarId_2123_);
                            v_a_2139_ = crate::leanh::lean_ctor_get(v___x_2136_, 0);
                            v_isSharedCheck_2146_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2136_)) as u8;
                            if v_isSharedCheck_2146_ == 0 {
                                v___x_2141_ = v___x_2136_;
                                v_isShared_2142_ = v_isSharedCheck_2146_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2139_);
                                crate::leanh::lean_dec(v___x_2136_);
                                v___x_2141_ = crate::leanh::lean_box(0);
                                v_isShared_2142_ = v_isSharedCheck_2146_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_p_2126_);
                        crate::leanh::lean_dec(v_fvarId_2125_);
                        crate::leanh::lean_dec(v_mvarId_2123_);
                        v_a_2147_ = crate::leanh::lean_ctor_get(v___x_2133_, 0);
                        v_isSharedCheck_2154_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2133_)) as u8;
                        if v_isSharedCheck_2154_ == 0 {
                            v___x_2149_ = v___x_2133_;
                            v_isShared_2150_ = v_isSharedCheck_2154_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2147_);
                            crate::leanh::lean_dec(v___x_2133_);
                            v___x_2149_ = crate::leanh::lean_box(0);
                            v_isShared_2150_ = v_isSharedCheck_2154_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_2126_);
                    crate::leanh::lean_dec(v_fvarId_2125_);
                    crate::leanh::lean_dec(v_mvarId_2123_);
                    v_a_2155_ = crate::leanh::lean_ctor_get(v___x_2132_, 0);
                    v_isSharedCheck_2162_ = (!crate::leanh::lean_is_exclusive(v___x_2132_)) as u8;
                    if v_isSharedCheck_2162_ == 0 {
                        v___x_2157_ = v___x_2132_;
                        v_isShared_2158_ = v_isSharedCheck_2162_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2155_);
                        crate::leanh::lean_dec(v___x_2132_);
                        v___x_2157_ = crate::leanh::lean_box(0);
                        v_isShared_2158_ = v_isSharedCheck_2162_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2142_ == 0 {
                    v___x_2144_ = v___x_2141_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
                    v___x_2144_ = v_reuseFailAlloc_2145_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2144_;
            }
            3 => {
                if v_isShared_2150_ == 0 {
                    v___x_2152_ = v___x_2149_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2153_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
                    v___x_2152_ = v_reuseFailAlloc_2153_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2152_;
            }
            5 => {
                if v_isShared_2158_ == 0 {
                    v___x_2160_ = v___x_2157_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2161_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
                    v___x_2160_ = v_reuseFailAlloc_2161_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2160_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_deltaLocalDecl___lam__0___boxed(
    mut v_mvarId_2163_: *mut crate::leanh::LeanObject,
    mut v___x_2164_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2165_: *mut crate::leanh::LeanObject,
    mut v_p_2166_: *mut crate::leanh::LeanObject,
    mut v___y_2167_: *mut crate::leanh::LeanObject,
    mut v___y_2168_: *mut crate::leanh::LeanObject,
    mut v___y_2169_: *mut crate::leanh::LeanObject,
    mut v___y_2170_: *mut crate::leanh::LeanObject,
    mut v___y_2171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2172_ = l_Lean_MVarId_deltaLocalDecl___lam__0(
        v_mvarId_2163_,
        v___x_2164_,
        v_fvarId_2165_,
        v_p_2166_,
        v___y_2167_,
        v___y_2168_,
        v___y_2169_,
        v___y_2170_,
    );
    crate::leanh::lean_dec(v___y_2170_);
    crate::leanh::lean_dec_ref(v___y_2169_);
    crate::leanh::lean_dec(v___y_2168_);
    crate::leanh::lean_dec_ref(v___y_2167_);
    return v_res_2172_;
}
pub unsafe fn l_Lean_MVarId_deltaLocalDecl(
    mut v_mvarId_2173_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2174_: *mut crate::leanh::LeanObject,
    mut v_p_2175_: *mut crate::leanh::LeanObject,
    mut v_a_2176_: *mut crate::leanh::LeanObject,
    mut v_a_2177_: *mut crate::leanh::LeanObject,
    mut v_a_2178_: *mut crate::leanh::LeanObject,
    mut v_a_2179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2181_ = l_Lean_MVarId_deltaTarget___closed__1;
    crate::leanh::lean_inc(v_mvarId_2173_);
    v___f_2182_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_deltaLocalDecl___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2182_, 0, v_mvarId_2173_);
    crate::leanh::lean_closure_set(v___f_2182_, 1, v___x_2181_);
    crate::leanh::lean_closure_set(v___f_2182_, 2, v_fvarId_2174_);
    crate::leanh::lean_closure_set(v___f_2182_, 3, v_p_2175_);
    v___x_2183_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(
        v_mvarId_2173_,
        v___f_2182_,
        v_a_2176_,
        v_a_2177_,
        v_a_2178_,
        v_a_2179_,
    );
    return v___x_2183_;
}
pub unsafe fn l_Lean_MVarId_deltaLocalDecl___boxed(
    mut v_mvarId_2184_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2185_: *mut crate::leanh::LeanObject,
    mut v_p_2186_: *mut crate::leanh::LeanObject,
    mut v_a_2187_: *mut crate::leanh::LeanObject,
    mut v_a_2188_: *mut crate::leanh::LeanObject,
    mut v_a_2189_: *mut crate::leanh::LeanObject,
    mut v_a_2190_: *mut crate::leanh::LeanObject,
    mut v_a_2191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2192_ = l_Lean_MVarId_deltaLocalDecl(
        v_mvarId_2184_,
        v_fvarId_2185_,
        v_p_2186_,
        v_a_2187_,
        v_a_2188_,
        v_a_2189_,
        v_a_2190_,
    );
    crate::leanh::lean_dec(v_a_2190_);
    crate::leanh::lean_dec_ref(v_a_2189_);
    crate::leanh::lean_dec(v_a_2188_);
    crate::leanh::lean_dec_ref(v_a_2187_);
    return v_res_2192_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Delta(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Delta(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Delta(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Replace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Transform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Delta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Delta(builtin);
}
