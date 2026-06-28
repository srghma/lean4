// Lean compiler output
// Module: Lean.Meta.Tactic.Delta
// Imports: Lean.Meta.Tactic.Replace Lean.Meta.Transform
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_maxRecDepthErrorMessage,
    l_List_lengthTR___redArg,
};
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
    lean_array_fget, lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_deltaExpand___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_deltaExpand___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_deltaExpand___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_deltaExpand___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_deltaTarget___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_MVarId_deltaTarget___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_deltaTarget___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_deltaTarget___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_deltaTarget___closed__0_value) as *mut LeanObject,
        2820377975091604199 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_deltaTarget___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_deltaTarget___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_delta_x3f(
    mut v_e_1097_: *mut LeanObject,
    mut v_p_1098_: *mut LeanObject,
    mut v_allowOpaque_1099_: u8,
    mut v_a_1100_: *mut LeanObject,
    mut v_a_1101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: u8 = 0;
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1119_: u8 = 0;
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: u8 = 0;
    let mut v___x_1123_: u8 = 0;
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: u8 = 0;
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1132_: u8 = 0;
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1143_: u8 = 0;
    let mut v_a_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1147_: u8 = 0;
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1151_: u8 = 0;
    let mut v_isSharedCheck_1152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1106_ = l_Lean_Expr_getAppFn(v_e_1097_);
                if lean_obj_tag(v___x_1106_) == 4 {
                    v_declName_1107_ = lean_ctor_get(v___x_1106_, 0);
                    lean_inc(v_declName_1107_);
                    v_us_1108_ = lean_ctor_get(v___x_1106_, 1);
                    lean_inc(v_us_1108_);
                    lean_dec_ref_known(v___x_1106_, 2);
                    v___x_1109_ = lean_st_ref_get(v_a_1101_);
                    v_env_1113_ = lean_ctor_get(v___x_1109_, 0);
                    lean_inc_ref(v_env_1113_);
                    lean_dec(v___x_1109_);
                    v___x_1114_ = 0;
                    v___x_1115_ =
                        l_Lean_Environment_find_x3f(v_env_1113_, v_declName_1107_, v___x_1114_);
                    if lean_obj_tag(v___x_1115_) == 0 {
                        lean_dec(v_us_1108_);
                        lean_dec_ref(v_p_1098_);
                        lean_dec_ref(v_e_1097_);
                        state = 1;
                        continue;
                    } else {
                        v_val_1116_ = lean_ctor_get(v___x_1115_, 0);
                        v_isSharedCheck_1152_ = (!lean_is_exclusive(v___x_1115_)) as u8;
                        if v_isSharedCheck_1152_ == 0 {
                            v___x_1118_ = v___x_1115_;
                            v_isShared_1119_ = v_isSharedCheck_1152_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_1116_);
                            lean_dec(v___x_1115_);
                            v___x_1118_ = lean_box(0);
                            v_isShared_1119_ = v_isSharedCheck_1152_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1106_);
                    lean_dec_ref(v_p_1098_);
                    lean_dec_ref(v_e_1097_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1104_ = lean_box(0);
                v___x_1105_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1105_, 0, v___x_1104_);
                return v___x_1105_;
            }
            2 => {
                v___x_1111_ = lean_box(0);
                v___x_1112_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1112_, 0, v___x_1111_);
                return v___x_1112_;
            }
            3 => {
                v___x_1120_ = l_Lean_ConstantInfo_name(v_val_1116_);
                v___x_1121_ = lean_apply_1(v_p_1098_, v___x_1120_);
                v___x_1122_ = (lean_unbox(v___x_1121_) as u8);
                if v___x_1122_ == 0 {
                    lean_del_object(v___x_1118_);
                    lean_dec(v_val_1116_);
                    lean_dec(v_us_1108_);
                    lean_dec_ref(v_e_1097_);
                    state = 2;
                    continue;
                } else {
                    v___x_1123_ = l_Lean_ConstantInfo_hasValue(v_val_1116_, v_allowOpaque_1099_);
                    if v___x_1123_ == 0 {
                        lean_del_object(v___x_1118_);
                        lean_dec(v_val_1116_);
                        lean_dec(v_us_1108_);
                        lean_dec_ref(v_e_1097_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1124_ = l_Lean_ConstantInfo_levelParams(v_val_1116_);
                        v___x_1125_ = l_List_lengthTR___redArg(v___x_1124_);
                        lean_dec(v___x_1124_);
                        v___x_1126_ = l_List_lengthTR___redArg(v_us_1108_);
                        v___x_1127_ = lean_nat_dec_eq(v___x_1125_, v___x_1126_);
                        lean_dec(v___x_1126_);
                        lean_dec(v___x_1125_);
                        if v___x_1127_ == 0 {
                            lean_del_object(v___x_1118_);
                            lean_dec(v_val_1116_);
                            lean_dec(v_us_1108_);
                            lean_dec_ref(v_e_1097_);
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
                            lean_dec(v_val_1116_);
                            if lean_obj_tag(v___x_1128_) == 0 {
                                v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
                                v_isSharedCheck_1143_ = (!lean_is_exclusive(v___x_1128_)) as u8;
                                if v_isSharedCheck_1143_ == 0 {
                                    v___x_1131_ = v___x_1128_;
                                    v_isShared_1132_ = v_isSharedCheck_1143_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_1129_);
                                    lean_dec(v___x_1128_);
                                    v___x_1131_ = lean_box(0);
                                    v_isShared_1132_ = v_isSharedCheck_1143_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_1118_);
                                lean_dec_ref(v_e_1097_);
                                v_a_1144_ = lean_ctor_get(v___x_1128_, 0);
                                v_isSharedCheck_1151_ = (!lean_is_exclusive(v___x_1128_)) as u8;
                                if v_isSharedCheck_1151_ == 0 {
                                    v___x_1146_ = v___x_1128_;
                                    v_isShared_1147_ = v_isSharedCheck_1151_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_1144_);
                                    lean_dec(v___x_1128_);
                                    v___x_1146_ = lean_box(0);
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
                lean_dec(v___x_1133_);
                v___x_1135_ =
                    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_1097_, v___x_1134_);
                v___x_1136_ = l_Lean_Expr_betaRev(v_a_1129_, v___x_1135_, v___x_1123_, v___x_1114_);
                lean_dec_ref(v___x_1135_);
                if v_isShared_1119_ == 0 {
                    lean_ctor_set(v___x_1118_, 0, v___x_1136_);
                    v___x_1138_ = v___x_1118_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1136_);
                    v___x_1138_ = v_reuseFailAlloc_1142_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1132_ == 0 {
                    lean_ctor_set(v___x_1131_, 0, v___x_1138_);
                    v___x_1140_ = v___x_1131_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
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
                    v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
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
    mut v_e_1153_: *mut LeanObject,
    mut v_p_1154_: *mut LeanObject,
    mut v_allowOpaque_1155_: *mut LeanObject,
    mut v_a_1156_: *mut LeanObject,
    mut v_a_1157_: *mut LeanObject,
    mut v_a_1158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowOpaque_boxed_1159_: u8 = 0;
    let mut v_res_1160_: *mut LeanObject = core::ptr::null_mut();
    v_allowOpaque_boxed_1159_ = (lean_unbox(v_allowOpaque_1155_) as u8);
    v_res_1160_ = l_Lean_Meta_delta_x3f(
        v_e_1153_,
        v_p_1154_,
        v_allowOpaque_boxed_1159_,
        v_a_1156_,
        v_a_1157_,
    );
    lean_dec(v_a_1157_);
    lean_dec_ref(v_a_1156_);
    return v_res_1160_;
}
pub unsafe fn l_Lean_Meta_deltaExpand___lam__0(
    mut v_p_1161_: *mut LeanObject,
    mut v_allowOpaque_1162_: u8,
    mut v_e_1163_: *mut LeanObject,
    mut v___y_1164_: *mut LeanObject,
    mut v___y_1165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1171_: u8 = 0;
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1179_: u8 = 0;
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1186_: u8 = 0;
    let mut v_isSharedCheck_1187_: u8 = 0;
    let mut v_a_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1191_: u8 = 0;
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1194_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_1167_) == 0 {
                    v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
                    v_isSharedCheck_1187_ = (!lean_is_exclusive(v___x_1167_)) as u8;
                    if v_isSharedCheck_1187_ == 0 {
                        v___x_1170_ = v___x_1167_;
                        v_isShared_1171_ = v_isSharedCheck_1187_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1168_);
                        lean_dec(v___x_1167_);
                        v___x_1170_ = lean_box(0);
                        v_isShared_1171_ = v_isSharedCheck_1187_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1188_ = lean_ctor_get(v___x_1167_, 0);
                    v_isSharedCheck_1195_ = (!lean_is_exclusive(v___x_1167_)) as u8;
                    if v_isSharedCheck_1195_ == 0 {
                        v___x_1190_ = v___x_1167_;
                        v_isShared_1191_ = v_isSharedCheck_1195_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1188_);
                        lean_dec(v___x_1167_);
                        v___x_1190_ = lean_box(0);
                        v_isShared_1191_ = v_isSharedCheck_1195_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1168_) == 0 {
                    v___x_1172_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v___x_1172_, 0, v_a_1168_);
                    if v_isShared_1171_ == 0 {
                        lean_ctor_set(v___x_1170_, 0, v___x_1172_);
                        v___x_1174_ = v___x_1170_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
                        v___x_1174_ = v_reuseFailAlloc_1175_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_1176_ = lean_ctor_get(v_a_1168_, 0);
                    v_isSharedCheck_1186_ = (!lean_is_exclusive(v_a_1168_)) as u8;
                    if v_isSharedCheck_1186_ == 0 {
                        v___x_1178_ = v_a_1168_;
                        v_isShared_1179_ = v_isSharedCheck_1186_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1176_);
                        lean_dec(v_a_1168_);
                        v___x_1178_ = lean_box(0);
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
                    v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_val_1176_);
                    v___x_1181_ = v_reuseFailAlloc_1185_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1171_ == 0 {
                    lean_ctor_set(v___x_1170_, 0, v___x_1181_);
                    v___x_1183_ = v___x_1170_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
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
                    v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
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
    mut v_p_1196_: *mut LeanObject,
    mut v_allowOpaque_1197_: *mut LeanObject,
    mut v_e_1198_: *mut LeanObject,
    mut v___y_1199_: *mut LeanObject,
    mut v___y_1200_: *mut LeanObject,
    mut v___y_1201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowOpaque_boxed_1202_: u8 = 0;
    let mut v_res_1203_: *mut LeanObject = core::ptr::null_mut();
    v_allowOpaque_boxed_1202_ = (lean_unbox(v_allowOpaque_1197_) as u8);
    v_res_1203_ = l_Lean_Meta_deltaExpand___lam__0(
        v_p_1196_,
        v_allowOpaque_boxed_1202_,
        v_e_1198_,
        v___y_1199_,
        v___y_1200_,
    );
    lean_dec(v___y_1200_);
    lean_dec_ref(v___y_1199_);
    return v_res_1203_;
}
pub unsafe fn l_Lean_Meta_deltaExpand___lam__1(
    mut v_e_1204_: *mut LeanObject,
    mut v___y_1205_: *mut LeanObject,
    mut v___y_1206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    v___x_1208_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1208_, 0, v_e_1204_);
    v___x_1209_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1209_, 0, v___x_1208_);
    return v___x_1209_;
}
pub unsafe fn l_Lean_Meta_deltaExpand___lam__1___boxed(
    mut v_e_1210_: *mut LeanObject,
    mut v___y_1211_: *mut LeanObject,
    mut v___y_1212_: *mut LeanObject,
    mut v___y_1213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1214_: *mut LeanObject = core::ptr::null_mut();
    v_res_1214_ = l_Lean_Meta_deltaExpand___lam__1(v_e_1210_, v___y_1211_, v___y_1212_);
    lean_dec(v___y_1212_);
    lean_dec_ref(v___y_1211_);
    return v_res_1214_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(
    mut v_00_u03b1_1215_: *mut LeanObject,
    mut v_x_1216_: *mut LeanObject,
    mut v___y_1217_: *mut LeanObject,
    mut v___y_1218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    v___x_1220_ = lean_apply_1(v_x_1216_, lean_box(0));
    v___x_1221_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1221_, 0, v___x_1220_);
    return v___x_1221_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0___boxed(
    mut v_00_u03b1_1222_: *mut LeanObject,
    mut v_x_1223_: *mut LeanObject,
    mut v___y_1224_: *mut LeanObject,
    mut v___y_1225_: *mut LeanObject,
    mut v___y_1226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1227_: *mut LeanObject = core::ptr::null_mut();
    v_res_1227_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(v_00_u03b1_1222_, v_x_1223_, v___y_1224_, v___y_1225_);
    lean_dec(v___y_1225_);
    lean_dec_ref(v___y_1224_);
    return v_res_1227_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(
    mut v_a_1228_: *mut LeanObject,
    mut v_x_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: u8 = 0;
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1229_) == 0 {
                    v___x_1230_ = lean_box(0);
                    return v___x_1230_;
                } else {
                    v_key_1231_ = lean_ctor_get(v_x_1229_, 0);
                    v_value_1232_ = lean_ctor_get(v_x_1229_, 1);
                    v_tail_1233_ = lean_ctor_get(v_x_1229_, 2);
                    v___x_1234_ = l_Lean_ExprStructEq_beq(v_key_1231_, v_a_1228_);
                    if v___x_1234_ == 0 {
                        v_x_1229_ = v_tail_1233_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_1232_);
                        v___x_1236_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1236_, 0, v_value_1232_);
                        return v___x_1236_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg___boxed(
    mut v_a_1237_: *mut LeanObject,
    mut v_x_1238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1239_: *mut LeanObject = core::ptr::null_mut();
    v_res_1239_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1237_, v_x_1238_);
    lean_dec(v_x_1238_);
    lean_dec_ref(v_a_1237_);
    return v_res_1239_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(
    mut v_m_1240_: *mut LeanObject,
    mut v_a_1241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_1242_ = lean_ctor_get(v_m_1240_, 1);
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
    mut v_m_1258_: *mut LeanObject,
    mut v_a_1259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1260_: *mut LeanObject = core::ptr::null_mut();
    v_res_1260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_m_1258_, v_a_1259_);
    lean_dec_ref(v_a_1259_);
    lean_dec_ref(v_m_1258_);
    return v_res_1260_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12___redArg(
    mut v_a_1261_: *mut LeanObject,
    mut v_b_1262_: *mut LeanObject,
    mut v_x_1263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1269_: u8 = 0;
    let mut v___x_1270_: u8 = 0;
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1263_) == 0 {
                    lean_dec(v_b_1262_);
                    lean_dec_ref(v_a_1261_);
                    return v_x_1263_;
                } else {
                    v_key_1264_ = lean_ctor_get(v_x_1263_, 0);
                    v_value_1265_ = lean_ctor_get(v_x_1263_, 1);
                    v_tail_1266_ = lean_ctor_get(v_x_1263_, 2);
                    v_isSharedCheck_1278_ = (!lean_is_exclusive(v_x_1263_)) as u8;
                    if v_isSharedCheck_1278_ == 0 {
                        v___x_1268_ = v_x_1263_;
                        v_isShared_1269_ = v_isSharedCheck_1278_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1266_);
                        lean_inc(v_value_1265_);
                        lean_inc(v_key_1264_);
                        lean_dec(v_x_1263_);
                        v___x_1268_ = lean_box(0);
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
                        lean_ctor_set(v___x_1268_, 2, v___x_1271_);
                        v___x_1273_ = v___x_1268_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_key_1264_);
                        lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_value_1265_);
                        lean_ctor_set(v_reuseFailAlloc_1274_, 2, v___x_1271_);
                        v___x_1273_ = v_reuseFailAlloc_1274_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_1265_);
                    lean_dec(v_key_1264_);
                    if v_isShared_1269_ == 0 {
                        lean_ctor_set(v___x_1268_, 1, v_b_1262_);
                        lean_ctor_set(v___x_1268_, 0, v_a_1261_);
                        v___x_1276_ = v___x_1268_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1261_);
                        lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_b_1262_);
                        lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_tail_1266_);
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
    mut v_x_1279_: *mut LeanObject,
    mut v_x_1280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1280_) == 0 {
                    return v_x_1279_;
                } else {
                    v_key_1281_ = lean_ctor_get(v_x_1280_, 0);
                    v_value_1282_ = lean_ctor_get(v_x_1280_, 1);
                    v_tail_1283_ = lean_ctor_get(v_x_1280_, 2);
                    v_isSharedCheck_1306_ = (!lean_is_exclusive(v_x_1280_)) as u8;
                    if v_isSharedCheck_1306_ == 0 {
                        v___x_1285_ = v_x_1280_;
                        v_isShared_1286_ = v_isSharedCheck_1306_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1283_);
                        lean_inc(v_value_1282_);
                        lean_inc(v_key_1281_);
                        lean_dec(v_x_1280_);
                        v___x_1285_ = lean_box(0);
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
                lean_inc(v___x_1300_);
                if v_isShared_1286_ == 0 {
                    lean_ctor_set(v___x_1285_, 2, v___x_1300_);
                    v___x_1302_ = v___x_1285_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_key_1281_);
                    lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_value_1282_);
                    lean_ctor_set(v_reuseFailAlloc_1305_, 2, v___x_1300_);
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
    mut v_i_1307_: *mut LeanObject,
    mut v_source_1308_: *mut LeanObject,
    mut v_target_1309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: u8 = 0;
    let mut v_es_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1310_ = lean_array_get_size(v_source_1308_);
                v___x_1311_ = lean_nat_dec_lt(v_i_1307_, v___x_1310_);
                if v___x_1311_ == 0 {
                    lean_dec_ref(v_source_1308_);
                    lean_dec(v_i_1307_);
                    return v_target_1309_;
                } else {
                    v_es_1312_ = lean_array_fget(v_source_1308_, v_i_1307_);
                    v___x_1313_ = lean_box(0);
                    v_source_1314_ = lean_array_fset(v_source_1308_, v_i_1307_, v___x_1313_);
                    v_target_1315_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_1309_, v_es_1312_);
                    v___x_1316_ = lean_unsigned_to_nat(1);
                    v___x_1317_ = lean_nat_add(v_i_1307_, v___x_1316_);
                    lean_dec(v_i_1307_);
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
    mut v_data_1319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    v___x_1320_ = lean_array_get_size(v_data_1319_);
    v___x_1321_ = lean_unsigned_to_nat(2);
    v_nbuckets_1322_ = lean_nat_mul(v___x_1320_, v___x_1321_);
    v___x_1323_ = lean_unsigned_to_nat(0);
    v___x_1324_ = lean_box(0);
    v___x_1325_ = lean_mk_array(v_nbuckets_1322_, v___x_1324_);
    v___x_1326_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1323_, v_data_1319_, v___x_1325_);
    return v___x_1326_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(
    mut v_a_1327_: *mut LeanObject,
    mut v_x_1328_: *mut LeanObject,
) -> u8 {
    let mut v___x_1329_: u8 = 0;
    let mut v_key_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1328_) == 0 {
                    v___x_1329_ = 0;
                    return v___x_1329_;
                } else {
                    v_key_1330_ = lean_ctor_get(v_x_1328_, 0);
                    v_tail_1331_ = lean_ctor_get(v_x_1328_, 2);
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
    mut v_a_1334_: *mut LeanObject,
    mut v_x_1335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1336_: u8 = 0;
    let mut v_r_1337_: *mut LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1334_, v_x_1335_);
    lean_dec(v_x_1335_);
    lean_dec_ref(v_a_1334_);
    v_r_1337_ = lean_box((v_res_1336_) as usize);
    return v_r_1337_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(
    mut v_m_1338_: *mut LeanObject,
    mut v_a_1339_: *mut LeanObject,
    mut v_b_1340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: u8 = 0;
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: u8 = 0;
    let mut v_val_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1385_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1341_ = lean_ctor_get(v_m_1338_, 0);
                v_buckets_1342_ = lean_ctor_get(v_m_1338_, 1);
                v_isSharedCheck_1385_ = (!lean_is_exclusive(v_m_1338_)) as u8;
                if v_isSharedCheck_1385_ == 0 {
                    v___x_1344_ = v_m_1338_;
                    v_isShared_1345_ = v_isSharedCheck_1385_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_1342_);
                    lean_inc(v_size_1341_);
                    lean_dec(v_m_1338_);
                    v___x_1344_ = lean_box(0);
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
                    v___x_1361_ = lean_unsigned_to_nat(1);
                    v_size_x27_1362_ = lean_nat_add(v_size_1341_, v___x_1361_);
                    lean_dec(v_size_1341_);
                    lean_inc(v_bkt_1359_);
                    v___x_1363_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1363_, 0, v_a_1339_);
                    lean_ctor_set(v___x_1363_, 1, v_b_1340_);
                    lean_ctor_set(v___x_1363_, 2, v_bkt_1359_);
                    v_buckets_x27_1364_ =
                        lean_array_uset(v_buckets_1342_, v___x_1358_, v___x_1363_);
                    v___x_1365_ = lean_unsigned_to_nat(4);
                    v___x_1366_ = lean_nat_mul(v_size_x27_1362_, v___x_1365_);
                    v___x_1367_ = lean_unsigned_to_nat(3);
                    v___x_1368_ = lean_nat_div(v___x_1366_, v___x_1367_);
                    lean_dec(v___x_1366_);
                    v___x_1369_ = lean_array_get_size(v_buckets_x27_1364_);
                    v___x_1370_ = lean_nat_dec_le(v___x_1368_, v___x_1369_);
                    lean_dec(v___x_1368_);
                    if v___x_1370_ == 0 {
                        v_val_1371_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1364_);
                        if v_isShared_1345_ == 0 {
                            lean_ctor_set(v___x_1344_, 1, v_val_1371_);
                            lean_ctor_set(v___x_1344_, 0, v_size_x27_1362_);
                            v___x_1373_ = v___x_1344_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_size_x27_1362_);
                            lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_val_1371_);
                            v___x_1373_ = v_reuseFailAlloc_1374_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1345_ == 0 {
                            lean_ctor_set(v___x_1344_, 1, v_buckets_x27_1364_);
                            lean_ctor_set(v___x_1344_, 0, v_size_x27_1362_);
                            v___x_1376_ = v___x_1344_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_size_x27_1362_);
                            lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_buckets_x27_1364_);
                            v___x_1376_ = v_reuseFailAlloc_1377_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1359_);
                    v___x_1378_ = lean_box(0);
                    v_buckets_x27_1379_ =
                        lean_array_uset(v_buckets_1342_, v___x_1358_, v___x_1378_);
                    v___x_1380_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1339_, v_b_1340_, v_bkt_1359_);
                    v___x_1381_ = lean_array_uset(v_buckets_x27_1379_, v___x_1358_, v___x_1380_);
                    if v_isShared_1345_ == 0 {
                        lean_ctor_set(v___x_1344_, 1, v___x_1381_);
                        v___x_1383_ = v___x_1344_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_size_1341_);
                        lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___x_1381_);
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
    mut v_a_1386_: *mut LeanObject,
    mut v_e_1387_: *mut LeanObject,
    mut v_a_1388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    v___x_1390_ = lean_st_ref_take(v_a_1386_);
    v___x_1391_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v___x_1390_, v_e_1387_, v_a_1388_);
    v___x_1392_ = lean_st_ref_set(v_a_1386_, v___x_1391_);
    v___x_1393_ = lean_box(0);
    return v___x_1393_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2___boxed(
    mut v_a_1394_: *mut LeanObject,
    mut v_e_1395_: *mut LeanObject,
    mut v_a_1396_: *mut LeanObject,
    mut v___y_1397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1398_: *mut LeanObject = core::ptr::null_mut();
    v_res_1398_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2(v_a_1394_, v_e_1395_, v_a_1396_);
    lean_dec(v_a_1394_);
    return v_res_1398_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    v___x_1399_ = lean_box(0);
    v___x_1400_ = l_Lean_interruptExceptionId;
    v___x_1401_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1401_, 0, v___x_1400_);
    lean_ctor_set(v___x_1401_, 1, v___x_1399_);
    return v___x_1401_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg()
-> *mut LeanObject {
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    v___x_1403_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
    v___x_1404_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1404_, 0, v___x_1403_);
    return v___x_1404_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___boxed(
    mut v___y_1405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1406_: *mut LeanObject = core::ptr::null_mut();
    v_res_1406_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg();
    return v_res_1406_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    v___x_1412_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1413_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1413_, 0, v___x_1412_);
    return v___x_1413_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    v___x_1414_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
    v___x_1415_ = l_Lean_MessageData_ofFormat(v___x_1414_);
    return v___x_1415_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    v___x_1416_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
    v___x_1417_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2;
    v___x_1418_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_1418_, 0, v___x_1417_);
    lean_ctor_set(v___x_1418_, 1, v___x_1416_);
    return v___x_1418_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(
    mut v_ref_1419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    v___x_1421_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
    v___x_1422_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1422_, 0, v_ref_1419_);
    lean_ctor_set(v___x_1422_, 1, v___x_1421_);
    v___x_1423_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1423_, 0, v___x_1422_);
    return v___x_1423_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___boxed(
    mut v_ref_1424_: *mut LeanObject,
    mut v___y_1425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1426_: *mut LeanObject = core::ptr::null_mut();
    v_res_1426_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1424_);
    return v_res_1426_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(
    mut v_x_1427_: *mut LeanObject,
    mut v___y_1428_: *mut LeanObject,
    mut v___y_1429_: *mut LeanObject,
    mut v___y_1430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1437_: u8 = 0;
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1441_: u8 = 0;
    let mut v___y_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: u8 = 0;
    let mut v___y_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1452_: u8 = 0;
    let mut v___y_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1475_: u8 = 0;
    let mut v_cancelTk_x3f_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1477_: u8 = 0;
    let mut v_inheritedTraceOptions_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: u8 = 0;
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1463_ = lean_ctor_get(v___y_1429_, 0);
                v_fileMap_1464_ = lean_ctor_get(v___y_1429_, 1);
                v_options_1465_ = lean_ctor_get(v___y_1429_, 2);
                v_currRecDepth_1466_ = lean_ctor_get(v___y_1429_, 3);
                v_maxRecDepth_1467_ = lean_ctor_get(v___y_1429_, 4);
                v_ref_1468_ = lean_ctor_get(v___y_1429_, 5);
                v_currNamespace_1469_ = lean_ctor_get(v___y_1429_, 6);
                v_openDecls_1470_ = lean_ctor_get(v___y_1429_, 7);
                v_initHeartbeats_1471_ = lean_ctor_get(v___y_1429_, 8);
                v_maxHeartbeats_1472_ = lean_ctor_get(v___y_1429_, 9);
                v_quotContext_1473_ = lean_ctor_get(v___y_1429_, 10);
                v_currMacroScope_1474_ = lean_ctor_get(v___y_1429_, 11);
                v_diag_1475_ = lean_ctor_get_uint8(
                    v___y_1429_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1476_ = lean_ctor_get(v___y_1429_, 12);
                v_suppressElabErrors_1477_ = lean_ctor_get_uint8(
                    v___y_1429_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1478_ = lean_ctor_get(v___y_1429_, 13);
                if lean_obj_tag(v_cancelTk_x3f_1476_) == 1 {
                    v_val_1484_ = lean_ctor_get(v_cancelTk_x3f_1476_, 0);
                    v___x_1485_ = l_IO_CancelToken_isSet(v_val_1484_);
                    if v___x_1485_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        lean_dec_ref(v_x_1427_);
                        v___x_1486_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg();
                        v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
                        v_isSharedCheck_1494_ = (!lean_is_exclusive(v___x_1486_)) as u8;
                        if v_isSharedCheck_1494_ == 0 {
                            v___x_1489_ = v___x_1486_;
                            v_isShared_1490_ = v_isSharedCheck_1494_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1487_);
                            lean_dec(v___x_1486_);
                            v___x_1489_ = lean_box(0);
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
                if lean_obj_tag(v___y_1433_) == 0 {
                    return v___y_1433_;
                } else {
                    v_a_1434_ = lean_ctor_get(v___y_1433_, 0);
                    v_isSharedCheck_1441_ = (!lean_is_exclusive(v___y_1433_)) as u8;
                    if v_isSharedCheck_1441_ == 0 {
                        v___x_1436_ = v___y_1433_;
                        v_isShared_1437_ = v_isSharedCheck_1441_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1434_);
                        lean_dec(v___y_1433_);
                        v___x_1436_ = lean_box(0);
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
                    v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
                    v___x_1439_ = v_reuseFailAlloc_1440_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1439_;
            }
            4 => {
                v___x_1459_ = lean_unsigned_to_nat(1);
                v___x_1460_ = lean_nat_add(v___y_1448_, v___x_1459_);
                lean_inc_ref(v___y_1456_);
                lean_inc(v___y_1449_);
                lean_inc(v___y_1447_);
                lean_inc(v___y_1455_);
                lean_inc(v___y_1450_);
                lean_inc(v___y_1454_);
                lean_inc(v___y_1453_);
                lean_inc(v___y_1458_);
                lean_inc(v___y_1457_);
                lean_inc_ref(v___y_1451_);
                lean_inc_ref(v___y_1445_);
                lean_inc_ref(v___y_1446_);
                v___x_1461_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_1461_, 0, v___y_1446_);
                lean_ctor_set(v___x_1461_, 1, v___y_1445_);
                lean_ctor_set(v___x_1461_, 2, v___y_1451_);
                lean_ctor_set(v___x_1461_, 3, v___x_1460_);
                lean_ctor_set(v___x_1461_, 4, v___y_1457_);
                lean_ctor_set(v___x_1461_, 5, v___y_1443_);
                lean_ctor_set(v___x_1461_, 6, v___y_1458_);
                lean_ctor_set(v___x_1461_, 7, v___y_1453_);
                lean_ctor_set(v___x_1461_, 8, v___y_1454_);
                lean_ctor_set(v___x_1461_, 9, v___y_1450_);
                lean_ctor_set(v___x_1461_, 10, v___y_1455_);
                lean_ctor_set(v___x_1461_, 11, v___y_1447_);
                lean_ctor_set(v___x_1461_, 12, v___y_1449_);
                lean_ctor_set(v___x_1461_, 13, v___y_1456_);
                lean_ctor_set_uint8(
                    v___x_1461_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___y_1452_,
                );
                lean_ctor_set_uint8(
                    v___x_1461_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v___y_1444_,
                );
                lean_inc(v___y_1430_);
                lean_inc(v___y_1428_);
                v___x_1462_ = lean_apply_4(
                    v_x_1427_,
                    v___y_1428_,
                    v___x_1461_,
                    v___y_1430_,
                    lean_box(0),
                );
                v___y_1433_ = v___x_1462_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1480_ = lean_unsigned_to_nat(0);
                v___x_1481_ = lean_nat_dec_eq(v_maxRecDepth_1467_, v___x_1480_);
                if v___x_1481_ == 0 {
                    v___x_1482_ = lean_nat_dec_eq(v_currRecDepth_1466_, v_maxRecDepth_1467_);
                    if v___x_1482_ == 0 {
                        lean_inc(v_ref_1468_);
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
                        lean_dec_ref(v_x_1427_);
                        lean_inc(v_ref_1468_);
                        v___x_1483_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1468_);
                        v___y_1433_ = v___x_1483_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_inc(v_ref_1468_);
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
                    v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
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
    mut v_x_1495_: *mut LeanObject,
    mut v___y_1496_: *mut LeanObject,
    mut v___y_1497_: *mut LeanObject,
    mut v___y_1498_: *mut LeanObject,
    mut v___y_1499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1500_: *mut LeanObject = core::ptr::null_mut();
    v_res_1500_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v_x_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
    lean_dec(v___y_1498_);
    lean_dec_ref(v___y_1497_);
    lean_dec(v___y_1496_);
    return v_res_1500_;
}
pub unsafe fn _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0()
-> *mut LeanObject {
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1503_: *mut LeanObject = core::ptr::null_mut();
    v___x_1502_ = lean_box(0);
    v_dummy_1503_ = l_Lean_Expr_sort___override(v___x_1502_);
    return v_dummy_1503_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(
    mut v_pre_1504_: *mut LeanObject,
    mut v_post_1505_: *mut LeanObject,
    mut v_sz_1506_: usize,
    mut v_i_1507_: usize,
    mut v_bs_1508_: *mut LeanObject,
    mut v___y_1509_: *mut LeanObject,
    mut v___y_1510_: *mut LeanObject,
    mut v___y_1511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1513_: u8 = 0;
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: usize = 0;
    let mut v___x_1521_: usize = 0;
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1527_: u8 = 0;
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1513_ = lean_usize_dec_lt(v_i_1507_, v_sz_1506_);
                if v___x_1513_ == 0 {
                    lean_dec_ref(v_post_1505_);
                    lean_dec_ref(v_pre_1504_);
                    v___x_1514_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1514_, 0, v_bs_1508_);
                    return v___x_1514_;
                } else {
                    v_v_1515_ = lean_array_uget_borrowed(v_bs_1508_, v_i_1507_);
                    lean_inc(v_v_1515_);
                    lean_inc_ref(v_post_1505_);
                    lean_inc_ref(v_pre_1504_);
                    v___x_1516_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1504_, v_post_1505_, v_v_1515_, v___y_1509_, v___y_1510_, v___y_1511_);
                    if lean_obj_tag(v___x_1516_) == 0 {
                        v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
                        lean_inc(v_a_1517_);
                        lean_dec_ref_known(v___x_1516_, 1);
                        v___x_1518_ = lean_unsigned_to_nat(0);
                        v_bs_x27_1519_ = lean_array_uset(v_bs_1508_, v_i_1507_, v___x_1518_);
                        v___x_1520_ = 1usize;
                        v___x_1521_ = lean_usize_add(v_i_1507_, v___x_1520_);
                        v___x_1522_ = lean_array_uset(v_bs_x27_1519_, v_i_1507_, v_a_1517_);
                        v_i_1507_ = v___x_1521_;
                        v_bs_1508_ = v___x_1522_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_1508_);
                        lean_dec_ref(v_post_1505_);
                        lean_dec_ref(v_pre_1504_);
                        v_a_1524_ = lean_ctor_get(v___x_1516_, 0);
                        v_isSharedCheck_1531_ = (!lean_is_exclusive(v___x_1516_)) as u8;
                        if v_isSharedCheck_1531_ == 0 {
                            v___x_1526_ = v___x_1516_;
                            v_isShared_1527_ = v_isSharedCheck_1531_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1524_);
                            lean_dec(v___x_1516_);
                            v___x_1526_ = lean_box(0);
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
                    v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
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
    mut v_pre_1532_: *mut LeanObject,
    mut v_post_1533_: *mut LeanObject,
    mut v_x_1534_: *mut LeanObject,
    mut v_x_1535_: *mut LeanObject,
    mut v_x_1536_: *mut LeanObject,
    mut v___y_1537_: *mut LeanObject,
    mut v___y_1538_: *mut LeanObject,
    mut v___y_1539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1549_: usize = 0;
    let mut v___x_1550_: usize = 0;
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1558_: u8 = 0;
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1534_) == 5 {
                    v_fn_1541_ = lean_ctor_get(v_x_1534_, 0);
                    lean_inc_ref(v_fn_1541_);
                    v_arg_1542_ = lean_ctor_get(v_x_1534_, 1);
                    lean_inc_ref(v_arg_1542_);
                    lean_dec_ref_known(v_x_1534_, 2);
                    v___x_1543_ = lean_array_set(v_x_1535_, v_x_1536_, v_arg_1542_);
                    v___x_1544_ = lean_unsigned_to_nat(1);
                    v___x_1545_ = lean_nat_sub(v_x_1536_, v___x_1544_);
                    lean_dec(v_x_1536_);
                    v_x_1534_ = v_fn_1541_;
                    v_x_1535_ = v___x_1543_;
                    v_x_1536_ = v___x_1545_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_1536_);
                    lean_inc_ref(v_post_1533_);
                    lean_inc_ref(v_pre_1532_);
                    v___x_1547_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1532_, v_post_1533_, v_x_1534_, v___y_1537_, v___y_1538_, v___y_1539_);
                    if lean_obj_tag(v___x_1547_) == 0 {
                        v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
                        lean_inc(v_a_1548_);
                        lean_dec_ref_known(v___x_1547_, 1);
                        v_sz_1549_ = lean_array_size(v_x_1535_);
                        v___x_1550_ = 0usize;
                        lean_inc_ref(v_post_1533_);
                        lean_inc_ref(v_pre_1532_);
                        v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(v_pre_1532_, v_post_1533_, v_sz_1549_, v___x_1550_, v_x_1535_, v___y_1537_, v___y_1538_, v___y_1539_);
                        if lean_obj_tag(v___x_1551_) == 0 {
                            v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
                            lean_inc(v_a_1552_);
                            lean_dec_ref_known(v___x_1551_, 1);
                            v___x_1553_ = l_Lean_mkAppN(v_a_1548_, v_a_1552_);
                            lean_dec(v_a_1552_);
                            v___x_1554_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1532_, v_post_1533_, v___x_1553_, v___y_1537_, v___y_1538_, v___y_1539_);
                            return v___x_1554_;
                        } else {
                            lean_dec(v_a_1548_);
                            lean_dec_ref(v_post_1533_);
                            lean_dec_ref(v_pre_1532_);
                            v_a_1555_ = lean_ctor_get(v___x_1551_, 0);
                            v_isSharedCheck_1562_ = (!lean_is_exclusive(v___x_1551_)) as u8;
                            if v_isSharedCheck_1562_ == 0 {
                                v___x_1557_ = v___x_1551_;
                                v_isShared_1558_ = v_isSharedCheck_1562_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1555_);
                                lean_dec(v___x_1551_);
                                v___x_1557_ = lean_box(0);
                                v_isShared_1558_ = v_isSharedCheck_1562_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_x_1535_);
                        lean_dec_ref(v_post_1533_);
                        lean_dec_ref(v_pre_1532_);
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
                    v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
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
    mut v___x_1563_: *mut LeanObject,
    mut v_pre_1564_: *mut LeanObject,
    mut v_e_1565_: *mut LeanObject,
    mut v_post_1566_: *mut LeanObject,
    mut v___y_1567_: *mut LeanObject,
    mut v___y_1568_: *mut LeanObject,
    mut v___y_1569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1575_: u8 = 0;
    let mut v___y_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1579_: u8 = 0;
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: usize = 0;
    let mut v___x_1583_: usize = 0;
    let mut v___x_1584_: u8 = 0;
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1592_: u8 = 0;
    let mut v___y_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1594_: u8 = 0;
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: u8 = 0;
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1605_: u8 = 0;
    let mut v___y_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1607_: u8 = 0;
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1619_: u8 = 0;
    let mut v___y_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1625_: u8 = 0;
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: usize = 0;
    let mut v___x_1631_: usize = 0;
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: usize = 0;
    let mut v___x_1634_: usize = 0;
    let mut v___x_1635_: u8 = 0;
    let mut v_binderName_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1639_: u8 = 0;
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: usize = 0;
    let mut v___x_1645_: usize = 0;
    let mut v___x_1646_: u8 = 0;
    let mut v___x_1647_: usize = 0;
    let mut v___x_1648_: usize = 0;
    let mut v___x_1649_: u8 = 0;
    let mut v_declName_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_1654_: u8 = 0;
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: usize = 0;
    let mut v___x_1662_: usize = 0;
    let mut v___x_1663_: u8 = 0;
    let mut v___x_1664_: usize = 0;
    let mut v___x_1665_: usize = 0;
    let mut v___x_1666_: u8 = 0;
    let mut v_dummy_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: usize = 0;
    let mut v___x_1678_: usize = 0;
    let mut v___x_1679_: u8 = 0;
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: usize = 0;
    let mut v___x_1689_: usize = 0;
    let mut v___x_1690_: u8 = 0;
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1705_: u8 = 0;
    let mut v_a_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1709_: u8 = 0;
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1713_: u8 = 0;
    let mut v_a_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1614_ = l_Lean_Core_checkSystem(v___x_1563_, v___y_1568_, v___y_1569_);
                if lean_obj_tag(v___x_1614_) == 0 {
                    lean_dec_ref_known(v___x_1614_, 1);
                    lean_inc_ref(v_pre_1564_);
                    lean_inc(v___y_1569_);
                    lean_inc_ref(v___y_1568_);
                    lean_inc_ref(v_e_1565_);
                    v___x_1615_ = lean_apply_4(
                        v_pre_1564_,
                        v_e_1565_,
                        v___y_1568_,
                        v___y_1569_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1615_) == 0 {
                        v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
                        v_isSharedCheck_1705_ = (!lean_is_exclusive(v___x_1615_)) as u8;
                        if v_isSharedCheck_1705_ == 0 {
                            v___x_1618_ = v___x_1615_;
                            v_isShared_1619_ = v_isSharedCheck_1705_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_1616_);
                            lean_dec(v___x_1615_);
                            v___x_1618_ = lean_box(0);
                            v_isShared_1619_ = v_isSharedCheck_1705_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_post_1566_);
                        lean_dec_ref(v_e_1565_);
                        lean_dec_ref(v_pre_1564_);
                        v_a_1706_ = lean_ctor_get(v___x_1615_, 0);
                        v_isSharedCheck_1713_ = (!lean_is_exclusive(v___x_1615_)) as u8;
                        if v_isSharedCheck_1713_ == 0 {
                            v___x_1708_ = v___x_1615_;
                            v_isShared_1709_ = v_isSharedCheck_1713_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1706_);
                            lean_dec(v___x_1615_);
                            v___x_1708_ = lean_box(0);
                            v_isShared_1709_ = v_isSharedCheck_1713_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_post_1566_);
                    lean_dec_ref(v_e_1565_);
                    lean_dec_ref(v_pre_1564_);
                    v_a_1714_ = lean_ctor_get(v___x_1614_, 0);
                    v_isSharedCheck_1721_ = (!lean_is_exclusive(v___x_1614_)) as u8;
                    if v_isSharedCheck_1721_ == 0 {
                        v___x_1716_ = v___x_1614_;
                        v_isShared_1717_ = v_isSharedCheck_1721_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1714_);
                        lean_dec(v___x_1614_);
                        v___x_1716_ = lean_box(0);
                        v_isShared_1717_ = v_isSharedCheck_1721_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1579_ == 0 {
                    lean_dec_ref(v___y_1576_);
                    lean_dec_ref(v___y_1572_);
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
                    lean_dec_ref(v___y_1576_);
                    v___x_1583_ = lean_ptr_addr(v___y_1578_);
                    v___x_1584_ = lean_usize_dec_eq(v___x_1582_, v___x_1583_);
                    if v___x_1584_ == 0 {
                        lean_dec_ref(v___y_1572_);
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
                        lean_dec_ref(v___y_1578_);
                        lean_dec(v___y_1577_);
                        lean_dec_ref(v___y_1574_);
                        lean_dec_ref(v___y_1573_);
                        v___x_1587_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___y_1572_, v___y_1567_, v___y_1568_, v___y_1569_);
                        return v___x_1587_;
                    }
                }
            }
            2 => {
                if v___y_1594_ == 0 {
                    lean_dec_ref(v___y_1589_);
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
                        lean_dec_ref(v___y_1589_);
                        v___x_1598_ = l_Lean_Expr_lam___override(
                            v___y_1593_,
                            v___y_1591_,
                            v___y_1590_,
                            v___y_1592_,
                        );
                        v___x_1599_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___x_1598_, v___y_1567_, v___y_1568_, v___y_1569_);
                        return v___x_1599_;
                    } else {
                        lean_dec(v___y_1593_);
                        lean_dec_ref(v___y_1591_);
                        lean_dec_ref(v___y_1590_);
                        v___x_1600_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___y_1589_, v___y_1567_, v___y_1568_, v___y_1569_);
                        return v___x_1600_;
                    }
                }
            }
            3 => {
                if v___y_1607_ == 0 {
                    lean_dec_ref(v___y_1602_);
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
                        lean_dec_ref(v___y_1602_);
                        v___x_1611_ = l_Lean_Expr_forallE___override(
                            v___y_1604_,
                            v___y_1603_,
                            v___y_1606_,
                            v___y_1605_,
                        );
                        v___x_1612_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___x_1611_, v___y_1567_, v___y_1568_, v___y_1569_);
                        return v___x_1612_;
                    } else {
                        lean_dec_ref(v___y_1606_);
                        lean_dec(v___y_1604_);
                        lean_dec_ref(v___y_1603_);
                        v___x_1613_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___y_1602_, v___y_1567_, v___y_1568_, v___y_1569_);
                        return v___x_1613_;
                    }
                }
            }
            4 => match lean_obj_tag(v_a_1616_) {
                0 => {
                    lean_dec_ref(v_post_1566_);
                    lean_dec_ref(v_e_1565_);
                    lean_dec_ref(v_pre_1564_);
                    v_e_1695_ = lean_ctor_get(v_a_1616_, 0);
                    lean_inc_ref(v_e_1695_);
                    lean_dec_ref_known(v_a_1616_, 1);
                    if v_isShared_1619_ == 0 {
                        lean_ctor_set(v___x_1618_, 0, v_e_1695_);
                        v___x_1697_ = v___x_1618_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_e_1695_);
                        v___x_1697_ = v_reuseFailAlloc_1698_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    lean_del_object(v___x_1618_);
                    lean_dec_ref(v_e_1565_);
                    v_e_1699_ = lean_ctor_get(v_a_1616_, 0);
                    lean_inc_ref(v_e_1699_);
                    lean_dec_ref_known(v_a_1616_, 1);
                    lean_inc_ref(v_post_1566_);
                    lean_inc_ref(v_pre_1564_);
                    v___x_1700_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_e_1699_, v___y_1567_, v___y_1568_, v___y_1569_);
                    if lean_obj_tag(v___x_1700_) == 0 {
                        v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
                        lean_inc(v_a_1701_);
                        lean_dec_ref_known(v___x_1700_, 1);
                        v___x_1702_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v_a_1701_, v___y_1567_, v___y_1568_, v___y_1569_);
                        return v___x_1702_;
                    } else {
                        lean_dec_ref(v_post_1566_);
                        lean_dec_ref(v_pre_1564_);
                        return v___x_1700_;
                    }
                }
                _ => {
                    lean_del_object(v___x_1618_);
                    v_e_x3f_1703_ = lean_ctor_get(v_a_1616_, 0);
                    lean_inc(v_e_x3f_1703_);
                    lean_dec_ref_known(v_a_1616_, 1);
                    if lean_obj_tag(v_e_x3f_1703_) == 0 {
                        v___y_1621_ = v_e_1565_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec_ref(v_e_1565_);
                        v_val_1704_ = lean_ctor_get(v_e_x3f_1703_, 0);
                        lean_inc(v_val_1704_);
                        lean_dec_ref_known(v_e_x3f_1703_, 1);
                        v___y_1621_ = v_val_1704_;
                        state = 5;
                        continue;
                    }
                }
            },
            5 => match lean_obj_tag(v___y_1621_) {
                7 => {
                    v_binderName_1622_ = lean_ctor_get(v___y_1621_, 0);
                    lean_inc(v_binderName_1622_);
                    v_binderType_1623_ = lean_ctor_get(v___y_1621_, 1);
                    v_body_1624_ = lean_ctor_get(v___y_1621_, 2);
                    v_binderInfo_1625_ = lean_ctor_get_uint8(
                        v___y_1621_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc_ref(v_binderType_1623_);
                    lean_inc_ref(v_post_1566_);
                    lean_inc_ref(v_pre_1564_);
                    v___x_1626_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_binderType_1623_, v___y_1567_, v___y_1568_, v___y_1569_);
                    if lean_obj_tag(v___x_1626_) == 0 {
                        v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
                        lean_inc(v_a_1627_);
                        lean_dec_ref_known(v___x_1626_, 1);
                        lean_inc_ref(v_body_1624_);
                        lean_inc_ref(v_post_1566_);
                        lean_inc_ref(v_pre_1564_);
                        v___x_1628_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_body_1624_, v___y_1567_, v___y_1568_, v___y_1569_);
                        if lean_obj_tag(v___x_1628_) == 0 {
                            v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
                            lean_inc(v_a_1629_);
                            lean_dec_ref_known(v___x_1628_, 1);
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
                            lean_dec(v_a_1627_);
                            lean_dec_ref_known(v___y_1621_, 3);
                            lean_dec(v_binderName_1622_);
                            lean_dec_ref(v_post_1566_);
                            lean_dec_ref(v_pre_1564_);
                            return v___x_1628_;
                        }
                    } else {
                        lean_dec_ref_known(v___y_1621_, 3);
                        lean_dec(v_binderName_1622_);
                        lean_dec_ref(v_post_1566_);
                        lean_dec_ref(v_pre_1564_);
                        return v___x_1626_;
                    }
                }
                6 => {
                    v_binderName_1636_ = lean_ctor_get(v___y_1621_, 0);
                    lean_inc(v_binderName_1636_);
                    v_binderType_1637_ = lean_ctor_get(v___y_1621_, 1);
                    v_body_1638_ = lean_ctor_get(v___y_1621_, 2);
                    v_binderInfo_1639_ = lean_ctor_get_uint8(
                        v___y_1621_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc_ref(v_binderType_1637_);
                    lean_inc_ref(v_post_1566_);
                    lean_inc_ref(v_pre_1564_);
                    v___x_1640_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_binderType_1637_, v___y_1567_, v___y_1568_, v___y_1569_);
                    if lean_obj_tag(v___x_1640_) == 0 {
                        v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
                        lean_inc(v_a_1641_);
                        lean_dec_ref_known(v___x_1640_, 1);
                        lean_inc_ref(v_body_1638_);
                        lean_inc_ref(v_post_1566_);
                        lean_inc_ref(v_pre_1564_);
                        v___x_1642_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_body_1638_, v___y_1567_, v___y_1568_, v___y_1569_);
                        if lean_obj_tag(v___x_1642_) == 0 {
                            v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
                            lean_inc(v_a_1643_);
                            lean_dec_ref_known(v___x_1642_, 1);
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
                            lean_dec(v_a_1641_);
                            lean_dec_ref_known(v___y_1621_, 3);
                            lean_dec(v_binderName_1636_);
                            lean_dec_ref(v_post_1566_);
                            lean_dec_ref(v_pre_1564_);
                            return v___x_1642_;
                        }
                    } else {
                        lean_dec_ref_known(v___y_1621_, 3);
                        lean_dec(v_binderName_1636_);
                        lean_dec_ref(v_post_1566_);
                        lean_dec_ref(v_pre_1564_);
                        return v___x_1640_;
                    }
                }
                8 => {
                    v_declName_1650_ = lean_ctor_get(v___y_1621_, 0);
                    lean_inc(v_declName_1650_);
                    v_type_1651_ = lean_ctor_get(v___y_1621_, 1);
                    v_value_1652_ = lean_ctor_get(v___y_1621_, 2);
                    v_body_1653_ = lean_ctor_get(v___y_1621_, 3);
                    lean_inc_ref(v_body_1653_);
                    v_nondep_1654_ = lean_ctor_get_uint8(
                        v___y_1621_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                    );
                    lean_inc_ref(v_type_1651_);
                    lean_inc_ref(v_post_1566_);
                    lean_inc_ref(v_pre_1564_);
                    v___x_1655_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_type_1651_, v___y_1567_, v___y_1568_, v___y_1569_);
                    if lean_obj_tag(v___x_1655_) == 0 {
                        v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
                        lean_inc(v_a_1656_);
                        lean_dec_ref_known(v___x_1655_, 1);
                        lean_inc_ref(v_value_1652_);
                        lean_inc_ref(v_post_1566_);
                        lean_inc_ref(v_pre_1564_);
                        v___x_1657_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_value_1652_, v___y_1567_, v___y_1568_, v___y_1569_);
                        if lean_obj_tag(v___x_1657_) == 0 {
                            v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
                            lean_inc(v_a_1658_);
                            lean_dec_ref_known(v___x_1657_, 1);
                            lean_inc_ref(v_body_1653_);
                            lean_inc_ref(v_post_1566_);
                            lean_inc_ref(v_pre_1564_);
                            v___x_1659_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_body_1653_, v___y_1567_, v___y_1568_, v___y_1569_);
                            if lean_obj_tag(v___x_1659_) == 0 {
                                v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
                                lean_inc(v_a_1660_);
                                lean_dec_ref_known(v___x_1659_, 1);
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
                                lean_dec(v_a_1658_);
                                lean_dec(v_a_1656_);
                                lean_dec_ref(v_body_1653_);
                                lean_dec(v_declName_1650_);
                                lean_dec_ref_known(v___y_1621_, 4);
                                lean_dec_ref(v_post_1566_);
                                lean_dec_ref(v_pre_1564_);
                                return v___x_1659_;
                            }
                        } else {
                            lean_dec(v_a_1656_);
                            lean_dec_ref(v_body_1653_);
                            lean_dec(v_declName_1650_);
                            lean_dec_ref_known(v___y_1621_, 4);
                            lean_dec_ref(v_post_1566_);
                            lean_dec_ref(v_pre_1564_);
                            return v___x_1657_;
                        }
                    } else {
                        lean_dec_ref(v_body_1653_);
                        lean_dec(v_declName_1650_);
                        lean_dec_ref_known(v___y_1621_, 4);
                        lean_dec_ref(v_post_1566_);
                        lean_dec_ref(v_pre_1564_);
                        return v___x_1655_;
                    }
                }
                5 => {
                    v_dummy_1667_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0);
                    v_nargs_1668_ = l_Lean_Expr_getAppNumArgs(v___y_1621_);
                    lean_inc(v_nargs_1668_);
                    v___x_1669_ = lean_mk_array(v_nargs_1668_, v_dummy_1667_);
                    v___x_1670_ = lean_unsigned_to_nat(1);
                    v___x_1671_ = lean_nat_sub(v_nargs_1668_, v___x_1670_);
                    lean_dec(v_nargs_1668_);
                    v___x_1672_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(v_pre_1564_, v_post_1566_, v___y_1621_, v___x_1669_, v___x_1671_, v___y_1567_, v___y_1568_, v___y_1569_);
                    return v___x_1672_;
                }
                10 => {
                    v_data_1673_ = lean_ctor_get(v___y_1621_, 0);
                    v_expr_1674_ = lean_ctor_get(v___y_1621_, 1);
                    lean_inc_ref(v_expr_1674_);
                    lean_inc_ref(v_post_1566_);
                    lean_inc_ref(v_pre_1564_);
                    v___x_1675_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_expr_1674_, v___y_1567_, v___y_1568_, v___y_1569_);
                    if lean_obj_tag(v___x_1675_) == 0 {
                        v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
                        lean_inc(v_a_1676_);
                        lean_dec_ref_known(v___x_1675_, 1);
                        v___x_1677_ = lean_ptr_addr(v_expr_1674_);
                        v___x_1678_ = lean_ptr_addr(v_a_1676_);
                        v___x_1679_ = lean_usize_dec_eq(v___x_1677_, v___x_1678_);
                        if v___x_1679_ == 0 {
                            lean_inc(v_data_1673_);
                            lean_dec_ref_known(v___y_1621_, 2);
                            v___x_1680_ = l_Lean_Expr_mdata___override(v_data_1673_, v_a_1676_);
                            v___x_1681_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___x_1680_, v___y_1567_, v___y_1568_, v___y_1569_);
                            return v___x_1681_;
                        } else {
                            lean_dec(v_a_1676_);
                            v___x_1682_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___y_1621_, v___y_1567_, v___y_1568_, v___y_1569_);
                            return v___x_1682_;
                        }
                    } else {
                        lean_dec_ref_known(v___y_1621_, 2);
                        lean_dec_ref(v_post_1566_);
                        lean_dec_ref(v_pre_1564_);
                        return v___x_1675_;
                    }
                }
                11 => {
                    v_typeName_1683_ = lean_ctor_get(v___y_1621_, 0);
                    v_idx_1684_ = lean_ctor_get(v___y_1621_, 1);
                    v_struct_1685_ = lean_ctor_get(v___y_1621_, 2);
                    lean_inc_ref(v_struct_1685_);
                    lean_inc_ref(v_post_1566_);
                    lean_inc_ref(v_pre_1564_);
                    v___x_1686_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1564_, v_post_1566_, v_struct_1685_, v___y_1567_, v___y_1568_, v___y_1569_);
                    if lean_obj_tag(v___x_1686_) == 0 {
                        v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
                        lean_inc(v_a_1687_);
                        lean_dec_ref_known(v___x_1686_, 1);
                        v___x_1688_ = lean_ptr_addr(v_struct_1685_);
                        v___x_1689_ = lean_ptr_addr(v_a_1687_);
                        v___x_1690_ = lean_usize_dec_eq(v___x_1688_, v___x_1689_);
                        if v___x_1690_ == 0 {
                            lean_inc(v_idx_1684_);
                            lean_inc(v_typeName_1683_);
                            lean_dec_ref_known(v___y_1621_, 3);
                            v___x_1691_ = l_Lean_Expr_proj___override(
                                v_typeName_1683_,
                                v_idx_1684_,
                                v_a_1687_,
                            );
                            v___x_1692_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___x_1691_, v___y_1567_, v___y_1568_, v___y_1569_);
                            return v___x_1692_;
                        } else {
                            lean_dec(v_a_1687_);
                            v___x_1693_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1564_, v_post_1566_, v___y_1621_, v___y_1567_, v___y_1568_, v___y_1569_);
                            return v___x_1693_;
                        }
                    } else {
                        lean_dec_ref_known(v___y_1621_, 3);
                        lean_dec_ref(v_post_1566_);
                        lean_dec_ref(v_pre_1564_);
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
                    v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
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
                    v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
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
    mut v___x_1722_: *mut LeanObject,
    mut v_pre_1723_: *mut LeanObject,
    mut v_e_1724_: *mut LeanObject,
    mut v_post_1725_: *mut LeanObject,
    mut v___y_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
    mut v___y_1729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1730_: *mut LeanObject = core::ptr::null_mut();
    v_res_1730_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1(v___x_1722_, v_pre_1723_, v_e_1724_, v_post_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
    lean_dec(v___y_1728_);
    lean_dec_ref(v___y_1727_);
    lean_dec(v___y_1726_);
    return v_res_1730_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(
    mut v_pre_1731_: *mut LeanObject,
    mut v_post_1732_: *mut LeanObject,
    mut v_e_1733_: *mut LeanObject,
    mut v_a_1734_: *mut LeanObject,
    mut v___y_1735_: *mut LeanObject,
    mut v___y_1736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1753_: u8 = 0;
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1757_: u8 = 0;
    let mut v_unused_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1762_: u8 = 0;
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut v_val_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1771_: u8 = 0;
    let mut v_a_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_1734_);
                v___x_1738_ =
                    lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
                lean_closure_set(v___x_1738_, 0, lean_box(0));
                lean_closure_set(v___x_1738_, 1, lean_box(0));
                lean_closure_set(v___x_1738_, 2, v_a_1734_);
                v___x_1739_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(lean_box(0), v___x_1738_, v___y_1735_, v___y_1736_);
                if lean_obj_tag(v___x_1739_) == 0 {
                    v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
                    v_isSharedCheck_1771_ = (!lean_is_exclusive(v___x_1739_)) as u8;
                    if v_isSharedCheck_1771_ == 0 {
                        v___x_1742_ = v___x_1739_;
                        v_isShared_1743_ = v_isSharedCheck_1771_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1740_);
                        lean_dec(v___x_1739_);
                        v___x_1742_ = lean_box(0);
                        v_isShared_1743_ = v_isSharedCheck_1771_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_1733_);
                    lean_dec_ref(v_post_1732_);
                    lean_dec_ref(v_pre_1731_);
                    v_a_1772_ = lean_ctor_get(v___x_1739_, 0);
                    v_isSharedCheck_1779_ = (!lean_is_exclusive(v___x_1739_)) as u8;
                    if v_isSharedCheck_1779_ == 0 {
                        v___x_1774_ = v___x_1739_;
                        v_isShared_1775_ = v_isSharedCheck_1779_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1772_);
                        lean_dec(v___x_1739_);
                        v___x_1774_ = lean_box(0);
                        v_isShared_1775_ = v_isSharedCheck_1779_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_a_1740_, v_e_1733_);
                lean_dec(v_a_1740_);
                if lean_obj_tag(v___x_1744_) == 0 {
                    lean_del_object(v___x_1742_);
                    v___x_1745_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___closed__0;
                    lean_inc_ref(v_e_1733_);
                    v___f_1746_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___boxed as *mut core::ffi::c_void, 8, 4);
                    lean_closure_set(v___f_1746_, 0, v___x_1745_);
                    lean_closure_set(v___f_1746_, 1, v_pre_1731_);
                    lean_closure_set(v___f_1746_, 2, v_e_1733_);
                    lean_closure_set(v___f_1746_, 3, v_post_1732_);
                    v___x_1747_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v___f_1746_, v_a_1734_, v___y_1735_, v___y_1736_);
                    if lean_obj_tag(v___x_1747_) == 0 {
                        v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
                        lean_inc_n(v_a_1748_, 2);
                        lean_dec_ref_known(v___x_1747_, 1);
                        lean_inc(v_a_1734_);
                        v___f_1749_ = lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        lean_closure_set(v___f_1749_, 0, v_a_1734_);
                        lean_closure_set(v___f_1749_, 1, v_e_1733_);
                        lean_closure_set(v___f_1749_, 2, v_a_1748_);
                        v___x_1750_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(lean_box(0), v___f_1749_, v___y_1735_, v___y_1736_);
                        if lean_obj_tag(v___x_1750_) == 0 {
                            v_isSharedCheck_1757_ = (!lean_is_exclusive(v___x_1750_)) as u8;
                            if v_isSharedCheck_1757_ == 0 {
                                v_unused_1758_ = lean_ctor_get(v___x_1750_, 0);
                                lean_dec(v_unused_1758_);
                                v___x_1752_ = v___x_1750_;
                                v_isShared_1753_ = v_isSharedCheck_1757_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v___x_1750_);
                                v___x_1752_ = lean_box(0);
                                v_isShared_1753_ = v_isSharedCheck_1757_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1748_);
                            v_a_1759_ = lean_ctor_get(v___x_1750_, 0);
                            v_isSharedCheck_1766_ = (!lean_is_exclusive(v___x_1750_)) as u8;
                            if v_isSharedCheck_1766_ == 0 {
                                v___x_1761_ = v___x_1750_;
                                v_isShared_1762_ = v_isSharedCheck_1766_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_1759_);
                                lean_dec(v___x_1750_);
                                v___x_1761_ = lean_box(0);
                                v_isShared_1762_ = v_isSharedCheck_1766_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_1733_);
                        return v___x_1747_;
                    }
                } else {
                    lean_dec_ref(v_e_1733_);
                    lean_dec_ref(v_post_1732_);
                    lean_dec_ref(v_pre_1731_);
                    v_val_1767_ = lean_ctor_get(v___x_1744_, 0);
                    lean_inc(v_val_1767_);
                    lean_dec_ref_known(v___x_1744_, 1);
                    if v_isShared_1743_ == 0 {
                        lean_ctor_set(v___x_1742_, 0, v_val_1767_);
                        v___x_1769_ = v___x_1742_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_val_1767_);
                        v___x_1769_ = v_reuseFailAlloc_1770_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1753_ == 0 {
                    lean_ctor_set(v___x_1752_, 0, v_a_1748_);
                    v___x_1755_ = v___x_1752_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1748_);
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
                    v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
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
                    v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
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
    mut v_pre_1780_: *mut LeanObject,
    mut v_post_1781_: *mut LeanObject,
    mut v_e_1782_: *mut LeanObject,
    mut v_a_1783_: *mut LeanObject,
    mut v___y_1784_: *mut LeanObject,
    mut v___y_1785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1791_: u8 = 0;
    let mut v_e_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v_a_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1810_: u8 = 0;
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_post_1781_);
                lean_inc(v___y_1785_);
                lean_inc_ref(v___y_1784_);
                lean_inc_ref(v_e_1782_);
                v___x_1787_ = lean_apply_4(
                    v_post_1781_,
                    v_e_1782_,
                    v___y_1784_,
                    v___y_1785_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1787_) == 0 {
                    v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
                    v_isSharedCheck_1806_ = (!lean_is_exclusive(v___x_1787_)) as u8;
                    if v_isSharedCheck_1806_ == 0 {
                        v___x_1790_ = v___x_1787_;
                        v_isShared_1791_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1788_);
                        lean_dec(v___x_1787_);
                        v___x_1790_ = lean_box(0);
                        v_isShared_1791_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_1782_);
                    lean_dec_ref(v_post_1781_);
                    lean_dec_ref(v_pre_1780_);
                    v_a_1807_ = lean_ctor_get(v___x_1787_, 0);
                    v_isSharedCheck_1814_ = (!lean_is_exclusive(v___x_1787_)) as u8;
                    if v_isSharedCheck_1814_ == 0 {
                        v___x_1809_ = v___x_1787_;
                        v_isShared_1810_ = v_isSharedCheck_1814_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1807_);
                        lean_dec(v___x_1787_);
                        v___x_1809_ = lean_box(0);
                        v_isShared_1810_ = v_isSharedCheck_1814_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match lean_obj_tag(v_a_1788_) {
                0 => {
                    lean_dec_ref(v_e_1782_);
                    lean_dec_ref(v_post_1781_);
                    lean_dec_ref(v_pre_1780_);
                    v_e_1792_ = lean_ctor_get(v_a_1788_, 0);
                    lean_inc_ref(v_e_1792_);
                    lean_dec_ref_known(v_a_1788_, 1);
                    if v_isShared_1791_ == 0 {
                        lean_ctor_set(v___x_1790_, 0, v_e_1792_);
                        v___x_1794_ = v___x_1790_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_e_1792_);
                        v___x_1794_ = v_reuseFailAlloc_1795_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    lean_del_object(v___x_1790_);
                    lean_dec_ref(v_e_1782_);
                    v_e_1796_ = lean_ctor_get(v_a_1788_, 0);
                    lean_inc_ref(v_e_1796_);
                    lean_dec_ref_known(v_a_1788_, 1);
                    v___x_1797_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1780_, v_post_1781_, v_e_1796_, v_a_1783_, v___y_1784_, v___y_1785_);
                    return v___x_1797_;
                }
                _ => {
                    lean_dec_ref(v_post_1781_);
                    lean_dec_ref(v_pre_1780_);
                    v_e_x3f_1798_ = lean_ctor_get(v_a_1788_, 0);
                    lean_inc(v_e_x3f_1798_);
                    lean_dec_ref_known(v_a_1788_, 1);
                    if lean_obj_tag(v_e_x3f_1798_) == 0 {
                        if v_isShared_1791_ == 0 {
                            lean_ctor_set(v___x_1790_, 0, v_e_1782_);
                            v___x_1800_ = v___x_1790_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_e_1782_);
                            v___x_1800_ = v_reuseFailAlloc_1801_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_1782_);
                        v_val_1802_ = lean_ctor_get(v_e_x3f_1798_, 0);
                        lean_inc(v_val_1802_);
                        lean_dec_ref_known(v_e_x3f_1798_, 1);
                        if v_isShared_1791_ == 0 {
                            lean_ctor_set(v___x_1790_, 0, v_val_1802_);
                            v___x_1804_ = v___x_1790_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_val_1802_);
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
                    v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
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
    mut v_pre_1815_: *mut LeanObject,
    mut v_post_1816_: *mut LeanObject,
    mut v_e_1817_: *mut LeanObject,
    mut v_a_1818_: *mut LeanObject,
    mut v___y_1819_: *mut LeanObject,
    mut v___y_1820_: *mut LeanObject,
    mut v___y_1821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1822_: *mut LeanObject = core::ptr::null_mut();
    v_res_1822_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_1815_, v_post_1816_, v_e_1817_, v_a_1818_, v___y_1819_, v___y_1820_);
    lean_dec(v___y_1820_);
    lean_dec_ref(v___y_1819_);
    lean_dec(v_a_1818_);
    return v_res_1822_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1___boxed(
    mut v_pre_1823_: *mut LeanObject,
    mut v_post_1824_: *mut LeanObject,
    mut v_sz_1825_: *mut LeanObject,
    mut v_i_1826_: *mut LeanObject,
    mut v_bs_1827_: *mut LeanObject,
    mut v___y_1828_: *mut LeanObject,
    mut v___y_1829_: *mut LeanObject,
    mut v___y_1830_: *mut LeanObject,
    mut v___y_1831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1832_: usize = 0;
    let mut v_i_boxed_1833_: usize = 0;
    let mut v_res_1834_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1832_ = lean_unbox_usize(v_sz_1825_);
    lean_dec(v_sz_1825_);
    v_i_boxed_1833_ = lean_unbox_usize(v_i_1826_);
    lean_dec(v_i_1826_);
    v_res_1834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(v_pre_1823_, v_post_1824_, v_sz_boxed_1832_, v_i_boxed_1833_, v_bs_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
    lean_dec(v___y_1830_);
    lean_dec_ref(v___y_1829_);
    lean_dec(v___y_1828_);
    return v_res_1834_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4___boxed(
    mut v_pre_1835_: *mut LeanObject,
    mut v_post_1836_: *mut LeanObject,
    mut v_x_1837_: *mut LeanObject,
    mut v_x_1838_: *mut LeanObject,
    mut v_x_1839_: *mut LeanObject,
    mut v___y_1840_: *mut LeanObject,
    mut v___y_1841_: *mut LeanObject,
    mut v___y_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1844_: *mut LeanObject = core::ptr::null_mut();
    v_res_1844_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(v_pre_1835_, v_post_1836_, v_x_1837_, v_x_1838_, v_x_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
    lean_dec(v___y_1842_);
    lean_dec_ref(v___y_1841_);
    lean_dec(v___y_1840_);
    return v_res_1844_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___boxed(
    mut v_pre_1845_: *mut LeanObject,
    mut v_post_1846_: *mut LeanObject,
    mut v_e_1847_: *mut LeanObject,
    mut v_a_1848_: *mut LeanObject,
    mut v___y_1849_: *mut LeanObject,
    mut v___y_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1852_: *mut LeanObject = core::ptr::null_mut();
    v_res_1852_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1845_, v_post_1846_, v_e_1847_, v_a_1848_, v___y_1849_, v___y_1850_);
    lean_dec(v___y_1850_);
    lean_dec_ref(v___y_1849_);
    lean_dec(v_a_1848_);
    return v_res_1852_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(
    mut v_00_u03b1_1853_: *mut LeanObject,
    mut v_x_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
    mut v___y_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    v___x_1858_ = lean_apply_1(v_x_1854_, lean_box(0));
    v___x_1859_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1859_, 0, v___x_1858_);
    return v___x_1859_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0___boxed(
    mut v_00_u03b1_1860_: *mut LeanObject,
    mut v_x_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1865_: *mut LeanObject = core::ptr::null_mut();
    v_res_1865_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(
        v_00_u03b1_1860_,
        v_x_1861_,
        v___y_1862_,
        v___y_1863_,
    );
    lean_dec(v___y_1863_);
    lean_dec_ref(v___y_1862_);
    return v_res_1865_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    v___x_1866_ = lean_box(0);
    v___x_1867_ = lean_unsigned_to_nat(16);
    v___x_1868_ = lean_mk_array(v___x_1867_, v___x_1866_);
    return v___x_1868_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    v___x_1869_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0_once
        ),
        _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0,
    );
    v___x_1870_ = lean_unsigned_to_nat(0);
    v___x_1871_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1871_, 0, v___x_1870_);
    lean_ctor_set(v___x_1871_, 1, v___x_1869_);
    return v___x_1871_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    v___x_1872_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1_once
        ),
        _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1,
    );
    v___x_1873_ = lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_1873_, 0, lean_box(0));
    lean_closure_set(v___x_1873_, 1, lean_box(0));
    lean_closure_set(v___x_1873_, 2, v___x_1872_);
    return v___x_1873_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(
    mut v_input_1874_: *mut LeanObject,
    mut v_pre_1875_: *mut LeanObject,
    mut v_post_1876_: *mut LeanObject,
    mut v___y_1877_: *mut LeanObject,
    mut v___y_1878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1889_: u8 = 0;
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut v_unused_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1880_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2_once), _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2);
                v___x_1881_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(
                    lean_box(0),
                    v___x_1880_,
                    v___y_1877_,
                    v___y_1878_,
                );
                v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
                lean_inc(v_a_1882_);
                lean_dec_ref(v___x_1881_);
                v___x_1883_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_1875_, v_post_1876_, v_input_1874_, v_a_1882_, v___y_1877_, v___y_1878_);
                if lean_obj_tag(v___x_1883_) == 0 {
                    v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
                    lean_inc(v_a_1884_);
                    lean_dec_ref_known(v___x_1883_, 1);
                    v___x_1885_ = lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___x_1885_, 0, lean_box(0));
                    lean_closure_set(v___x_1885_, 1, lean_box(0));
                    lean_closure_set(v___x_1885_, 2, v_a_1882_);
                    v___x_1886_ =
                        l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(
                            lean_box(0),
                            v___x_1885_,
                            v___y_1877_,
                            v___y_1878_,
                        );
                    v_isSharedCheck_1893_ = (!lean_is_exclusive(v___x_1886_)) as u8;
                    if v_isSharedCheck_1893_ == 0 {
                        v_unused_1894_ = lean_ctor_get(v___x_1886_, 0);
                        lean_dec(v_unused_1894_);
                        v___x_1888_ = v___x_1886_;
                        v_isShared_1889_ = v_isSharedCheck_1893_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1886_);
                        v___x_1888_ = lean_box(0);
                        v_isShared_1889_ = v_isSharedCheck_1893_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1882_);
                    return v___x_1883_;
                }
            }
            1 => {
                if v_isShared_1889_ == 0 {
                    lean_ctor_set(v___x_1888_, 0, v_a_1884_);
                    v___x_1891_ = v___x_1888_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1884_);
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
    mut v_input_1895_: *mut LeanObject,
    mut v_pre_1896_: *mut LeanObject,
    mut v_post_1897_: *mut LeanObject,
    mut v___y_1898_: *mut LeanObject,
    mut v___y_1899_: *mut LeanObject,
    mut v___y_1900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1901_: *mut LeanObject = core::ptr::null_mut();
    v_res_1901_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(
        v_input_1895_,
        v_pre_1896_,
        v_post_1897_,
        v___y_1898_,
        v___y_1899_,
    );
    lean_dec(v___y_1899_);
    lean_dec_ref(v___y_1898_);
    return v_res_1901_;
}
pub unsafe fn l_Lean_Meta_deltaExpand(
    mut v_e_1903_: *mut LeanObject,
    mut v_p_1904_: *mut LeanObject,
    mut v_allowOpaque_1905_: u8,
    mut v_a_1906_: *mut LeanObject,
    mut v_a_1907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    v___x_1909_ = lean_box((v_allowOpaque_1905_) as usize);
    v___f_1910_ = lean_alloc_closure(
        l_Lean_Meta_deltaExpand___lam__0___boxed as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_1910_, 0, v_p_1904_);
    lean_closure_set(v___f_1910_, 1, v___x_1909_);
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
    mut v_e_1913_: *mut LeanObject,
    mut v_p_1914_: *mut LeanObject,
    mut v_allowOpaque_1915_: *mut LeanObject,
    mut v_a_1916_: *mut LeanObject,
    mut v_a_1917_: *mut LeanObject,
    mut v_a_1918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowOpaque_boxed_1919_: u8 = 0;
    let mut v_res_1920_: *mut LeanObject = core::ptr::null_mut();
    v_allowOpaque_boxed_1919_ = (lean_unbox(v_allowOpaque_1915_) as u8);
    v_res_1920_ = l_Lean_Meta_deltaExpand(
        v_e_1913_,
        v_p_1914_,
        v_allowOpaque_boxed_1919_,
        v_a_1916_,
        v_a_1917_,
    );
    lean_dec(v_a_1917_);
    lean_dec_ref(v_a_1916_);
    return v_res_1920_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3(
    mut v_00_u03b2_1921_: *mut LeanObject,
    mut v_m_1922_: *mut LeanObject,
    mut v_a_1923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    v___x_1924_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_m_1922_, v_a_1923_);
    return v___x_1924_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_1925_: *mut LeanObject,
    mut v_m_1926_: *mut LeanObject,
    mut v_a_1927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1928_: *mut LeanObject = core::ptr::null_mut();
    v_res_1928_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3(v_00_u03b2_1925_, v_m_1926_, v_a_1927_);
    lean_dec_ref(v_a_1927_);
    lean_dec_ref(v_m_1926_);
    return v_res_1928_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7(
    mut v_00_u03b1_1929_: *mut LeanObject,
    mut v_ref_1930_: *mut LeanObject,
    mut v___y_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    v___x_1934_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1930_);
    return v___x_1934_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___boxed(
    mut v_00_u03b1_1935_: *mut LeanObject,
    mut v_ref_1936_: *mut LeanObject,
    mut v___y_1937_: *mut LeanObject,
    mut v___y_1938_: *mut LeanObject,
    mut v___y_1939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1940_: *mut LeanObject = core::ptr::null_mut();
    v_res_1940_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1935_, v_ref_1936_, v___y_1937_, v___y_1938_);
    lean_dec(v___y_1938_);
    lean_dec_ref(v___y_1937_);
    return v_res_1940_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8(
    mut v_00_u03b1_1941_: *mut LeanObject,
    mut v___y_1942_: *mut LeanObject,
    mut v___y_1943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg();
    return v___x_1945_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___boxed(
    mut v_00_u03b1_1946_: *mut LeanObject,
    mut v___y_1947_: *mut LeanObject,
    mut v___y_1948_: *mut LeanObject,
    mut v___y_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1950_: *mut LeanObject = core::ptr::null_mut();
    v_res_1950_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1946_, v___y_1947_, v___y_1948_);
    lean_dec(v___y_1948_);
    lean_dec_ref(v___y_1947_);
    return v_res_1950_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(
    mut v_00_u03b1_1951_: *mut LeanObject,
    mut v_x_1952_: *mut LeanObject,
    mut v___y_1953_: *mut LeanObject,
    mut v___y_1954_: *mut LeanObject,
    mut v___y_1955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    v___x_1957_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v_x_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
    return v___x_1957_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___boxed(
    mut v_00_u03b1_1958_: *mut LeanObject,
    mut v_x_1959_: *mut LeanObject,
    mut v___y_1960_: *mut LeanObject,
    mut v___y_1961_: *mut LeanObject,
    mut v___y_1962_: *mut LeanObject,
    mut v___y_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1964_: *mut LeanObject = core::ptr::null_mut();
    v_res_1964_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(v_00_u03b1_1958_, v_x_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
    lean_dec(v___y_1962_);
    lean_dec_ref(v___y_1961_);
    lean_dec(v___y_1960_);
    return v_res_1964_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6(
    mut v_00_u03b2_1965_: *mut LeanObject,
    mut v_m_1966_: *mut LeanObject,
    mut v_a_1967_: *mut LeanObject,
    mut v_b_1968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    v___x_1969_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v_m_1966_, v_a_1967_, v_b_1968_);
    return v___x_1969_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(
    mut v_00_u03b2_1970_: *mut LeanObject,
    mut v_a_1971_: *mut LeanObject,
    mut v_x_1972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    v___x_1973_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1971_, v_x_1972_);
    return v___x_1973_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___boxed(
    mut v_00_u03b2_1974_: *mut LeanObject,
    mut v_a_1975_: *mut LeanObject,
    mut v_x_1976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1977_: *mut LeanObject = core::ptr::null_mut();
    v_res_1977_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1974_, v_a_1975_, v_x_1976_);
    lean_dec(v_x_1976_);
    lean_dec_ref(v_a_1975_);
    return v_res_1977_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10(
    mut v_00_u03b2_1978_: *mut LeanObject,
    mut v_a_1979_: *mut LeanObject,
    mut v_x_1980_: *mut LeanObject,
) -> u8 {
    let mut v___x_1981_: u8 = 0;
    v___x_1981_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1979_, v_x_1980_);
    return v___x_1981_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___boxed(
    mut v_00_u03b2_1982_: *mut LeanObject,
    mut v_a_1983_: *mut LeanObject,
    mut v_x_1984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1985_: u8 = 0;
    let mut v_r_1986_: *mut LeanObject = core::ptr::null_mut();
    v_res_1985_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1982_, v_a_1983_, v_x_1984_);
    lean_dec(v_x_1984_);
    lean_dec_ref(v_a_1983_);
    v_r_1986_ = lean_box((v_res_1985_) as usize);
    return v_r_1986_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11(
    mut v_00_u03b2_1987_: *mut LeanObject,
    mut v_data_1988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    v___x_1989_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1988_);
    return v___x_1989_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12(
    mut v_00_u03b2_1990_: *mut LeanObject,
    mut v_a_1991_: *mut LeanObject,
    mut v_b_1992_: *mut LeanObject,
    mut v_x_1993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    v___x_1994_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1991_, v_b_1992_, v_x_1993_);
    return v___x_1994_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12(
    mut v_00_u03b2_1995_: *mut LeanObject,
    mut v_i_1996_: *mut LeanObject,
    mut v_source_1997_: *mut LeanObject,
    mut v_target_1998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    v___x_1999_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1996_, v_source_1997_, v_target_1998_);
    return v___x_1999_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(
    mut v_00_u03b2_2000_: *mut LeanObject,
    mut v_x_2001_: *mut LeanObject,
    mut v_x_2002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    v___x_2003_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_2001_, v_x_2002_);
    return v___x_2003_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(
    mut v_mvarId_2004_: *mut LeanObject,
    mut v_x_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
    mut v___y_2008_: *mut LeanObject,
    mut v___y_2009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2015_: u8 = 0;
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut v_a_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2023_: u8 = 0;
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2027_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2011_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_2004_,
                    v_x_2005_,
                    v___y_2006_,
                    v___y_2007_,
                    v___y_2008_,
                    v___y_2009_,
                );
                if lean_obj_tag(v___x_2011_) == 0 {
                    v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
                    v_isSharedCheck_2019_ = (!lean_is_exclusive(v___x_2011_)) as u8;
                    if v_isSharedCheck_2019_ == 0 {
                        v___x_2014_ = v___x_2011_;
                        v_isShared_2015_ = v_isSharedCheck_2019_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2012_);
                        lean_dec(v___x_2011_);
                        v___x_2014_ = lean_box(0);
                        v_isShared_2015_ = v_isSharedCheck_2019_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2020_ = lean_ctor_get(v___x_2011_, 0);
                    v_isSharedCheck_2027_ = (!lean_is_exclusive(v___x_2011_)) as u8;
                    if v_isSharedCheck_2027_ == 0 {
                        v___x_2022_ = v___x_2011_;
                        v_isShared_2023_ = v_isSharedCheck_2027_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2020_);
                        lean_dec(v___x_2011_);
                        v___x_2022_ = lean_box(0);
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
                    v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
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
                    v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
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
    mut v_mvarId_2028_: *mut LeanObject,
    mut v_x_2029_: *mut LeanObject,
    mut v___y_2030_: *mut LeanObject,
    mut v___y_2031_: *mut LeanObject,
    mut v___y_2032_: *mut LeanObject,
    mut v___y_2033_: *mut LeanObject,
    mut v___y_2034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2035_: *mut LeanObject = core::ptr::null_mut();
    v_res_2035_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(
        v_mvarId_2028_,
        v_x_2029_,
        v___y_2030_,
        v___y_2031_,
        v___y_2032_,
        v___y_2033_,
    );
    lean_dec(v___y_2033_);
    lean_dec_ref(v___y_2032_);
    lean_dec(v___y_2031_);
    lean_dec_ref(v___y_2030_);
    return v_res_2035_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0(
    mut v_00_u03b1_2036_: *mut LeanObject,
    mut v_mvarId_2037_: *mut LeanObject,
    mut v_x_2038_: *mut LeanObject,
    mut v___y_2039_: *mut LeanObject,
    mut v___y_2040_: *mut LeanObject,
    mut v___y_2041_: *mut LeanObject,
    mut v___y_2042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2045_: *mut LeanObject,
    mut v_mvarId_2046_: *mut LeanObject,
    mut v_x_2047_: *mut LeanObject,
    mut v___y_2048_: *mut LeanObject,
    mut v___y_2049_: *mut LeanObject,
    mut v___y_2050_: *mut LeanObject,
    mut v___y_2051_: *mut LeanObject,
    mut v___y_2052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2053_: *mut LeanObject = core::ptr::null_mut();
    v_res_2053_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0(
        v_00_u03b1_2045_,
        v_mvarId_2046_,
        v_x_2047_,
        v___y_2048_,
        v___y_2049_,
        v___y_2050_,
        v___y_2051_,
    );
    lean_dec(v___y_2051_);
    lean_dec_ref(v___y_2050_);
    lean_dec(v___y_2049_);
    lean_dec_ref(v___y_2048_);
    return v_res_2053_;
}
pub unsafe fn l_Lean_MVarId_deltaTarget___lam__0(
    mut v_mvarId_2054_: *mut LeanObject,
    mut v___x_2055_: *mut LeanObject,
    mut v_p_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
    mut v___y_2059_: *mut LeanObject,
    mut v___y_2060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: u8 = 0;
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2072_: u8 = 0;
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2076_: u8 = 0;
    let mut v_a_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2080_: u8 = 0;
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut v_a_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2088_: u8 = 0;
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2092_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_2054_);
                v___x_2062_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2054_,
                    v___x_2055_,
                    v___y_2057_,
                    v___y_2058_,
                    v___y_2059_,
                    v___y_2060_,
                );
                if lean_obj_tag(v___x_2062_) == 0 {
                    lean_dec_ref_known(v___x_2062_, 1);
                    lean_inc(v_mvarId_2054_);
                    v___x_2063_ = l_Lean_MVarId_getType(
                        v_mvarId_2054_,
                        v___y_2057_,
                        v___y_2058_,
                        v___y_2059_,
                        v___y_2060_,
                    );
                    if lean_obj_tag(v___x_2063_) == 0 {
                        v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
                        lean_inc(v_a_2064_);
                        lean_dec_ref_known(v___x_2063_, 1);
                        v___x_2065_ = 0;
                        v___x_2066_ = l_Lean_Meta_deltaExpand(
                            v_a_2064_,
                            v_p_2056_,
                            v___x_2065_,
                            v___y_2059_,
                            v___y_2060_,
                        );
                        if lean_obj_tag(v___x_2066_) == 0 {
                            v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
                            lean_inc(v_a_2067_);
                            lean_dec_ref_known(v___x_2066_, 1);
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
                            lean_dec(v_mvarId_2054_);
                            v_a_2069_ = lean_ctor_get(v___x_2066_, 0);
                            v_isSharedCheck_2076_ = (!lean_is_exclusive(v___x_2066_)) as u8;
                            if v_isSharedCheck_2076_ == 0 {
                                v___x_2071_ = v___x_2066_;
                                v_isShared_2072_ = v_isSharedCheck_2076_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2069_);
                                lean_dec(v___x_2066_);
                                v___x_2071_ = lean_box(0);
                                v_isShared_2072_ = v_isSharedCheck_2076_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_p_2056_);
                        lean_dec(v_mvarId_2054_);
                        v_a_2077_ = lean_ctor_get(v___x_2063_, 0);
                        v_isSharedCheck_2084_ = (!lean_is_exclusive(v___x_2063_)) as u8;
                        if v_isSharedCheck_2084_ == 0 {
                            v___x_2079_ = v___x_2063_;
                            v_isShared_2080_ = v_isSharedCheck_2084_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2077_);
                            lean_dec(v___x_2063_);
                            v___x_2079_ = lean_box(0);
                            v_isShared_2080_ = v_isSharedCheck_2084_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_p_2056_);
                    lean_dec(v_mvarId_2054_);
                    v_a_2085_ = lean_ctor_get(v___x_2062_, 0);
                    v_isSharedCheck_2092_ = (!lean_is_exclusive(v___x_2062_)) as u8;
                    if v_isSharedCheck_2092_ == 0 {
                        v___x_2087_ = v___x_2062_;
                        v_isShared_2088_ = v_isSharedCheck_2092_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2085_);
                        lean_dec(v___x_2062_);
                        v___x_2087_ = lean_box(0);
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
                    v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
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
                    v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
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
                    v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
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
    mut v_mvarId_2093_: *mut LeanObject,
    mut v___x_2094_: *mut LeanObject,
    mut v_p_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
    mut v___y_2098_: *mut LeanObject,
    mut v___y_2099_: *mut LeanObject,
    mut v___y_2100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2101_: *mut LeanObject = core::ptr::null_mut();
    v_res_2101_ = l_Lean_MVarId_deltaTarget___lam__0(
        v_mvarId_2093_,
        v___x_2094_,
        v_p_2095_,
        v___y_2096_,
        v___y_2097_,
        v___y_2098_,
        v___y_2099_,
    );
    lean_dec(v___y_2099_);
    lean_dec_ref(v___y_2098_);
    lean_dec(v___y_2097_);
    lean_dec_ref(v___y_2096_);
    return v_res_2101_;
}
pub unsafe fn l_Lean_MVarId_deltaTarget(
    mut v_mvarId_2105_: *mut LeanObject,
    mut v_p_2106_: *mut LeanObject,
    mut v_a_2107_: *mut LeanObject,
    mut v_a_2108_: *mut LeanObject,
    mut v_a_2109_: *mut LeanObject,
    mut v_a_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    v___x_2112_ = l_Lean_MVarId_deltaTarget___closed__1;
    lean_inc(v_mvarId_2105_);
    v___f_2113_ = lean_alloc_closure(
        l_Lean_MVarId_deltaTarget___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___f_2113_, 0, v_mvarId_2105_);
    lean_closure_set(v___f_2113_, 1, v___x_2112_);
    lean_closure_set(v___f_2113_, 2, v_p_2106_);
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
    mut v_mvarId_2115_: *mut LeanObject,
    mut v_p_2116_: *mut LeanObject,
    mut v_a_2117_: *mut LeanObject,
    mut v_a_2118_: *mut LeanObject,
    mut v_a_2119_: *mut LeanObject,
    mut v_a_2120_: *mut LeanObject,
    mut v_a_2121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2122_: *mut LeanObject = core::ptr::null_mut();
    v_res_2122_ = l_Lean_MVarId_deltaTarget(
        v_mvarId_2115_,
        v_p_2116_,
        v_a_2117_,
        v_a_2118_,
        v_a_2119_,
        v_a_2120_,
    );
    lean_dec(v_a_2120_);
    lean_dec_ref(v_a_2119_);
    lean_dec(v_a_2118_);
    lean_dec_ref(v_a_2117_);
    return v_res_2122_;
}
pub unsafe fn l_Lean_MVarId_deltaLocalDecl___lam__0(
    mut v_mvarId_2123_: *mut LeanObject,
    mut v___x_2124_: *mut LeanObject,
    mut v_fvarId_2125_: *mut LeanObject,
    mut v_p_2126_: *mut LeanObject,
    mut v___y_2127_: *mut LeanObject,
    mut v___y_2128_: *mut LeanObject,
    mut v___y_2129_: *mut LeanObject,
    mut v___y_2130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: u8 = 0;
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2142_: u8 = 0;
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2146_: u8 = 0;
    let mut v_a_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2150_: u8 = 0;
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2154_: u8 = 0;
    let mut v_a_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_2123_);
                v___x_2132_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2123_,
                    v___x_2124_,
                    v___y_2127_,
                    v___y_2128_,
                    v___y_2129_,
                    v___y_2130_,
                );
                if lean_obj_tag(v___x_2132_) == 0 {
                    lean_dec_ref_known(v___x_2132_, 1);
                    lean_inc(v_fvarId_2125_);
                    v___x_2133_ = l_Lean_FVarId_getType___redArg(
                        v_fvarId_2125_,
                        v___y_2127_,
                        v___y_2129_,
                        v___y_2130_,
                    );
                    if lean_obj_tag(v___x_2133_) == 0 {
                        v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
                        lean_inc(v_a_2134_);
                        lean_dec_ref_known(v___x_2133_, 1);
                        v___x_2135_ = 0;
                        v___x_2136_ = l_Lean_Meta_deltaExpand(
                            v_a_2134_,
                            v_p_2126_,
                            v___x_2135_,
                            v___y_2129_,
                            v___y_2130_,
                        );
                        if lean_obj_tag(v___x_2136_) == 0 {
                            v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
                            lean_inc(v_a_2137_);
                            lean_dec_ref_known(v___x_2136_, 1);
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
                            lean_dec(v_fvarId_2125_);
                            lean_dec(v_mvarId_2123_);
                            v_a_2139_ = lean_ctor_get(v___x_2136_, 0);
                            v_isSharedCheck_2146_ = (!lean_is_exclusive(v___x_2136_)) as u8;
                            if v_isSharedCheck_2146_ == 0 {
                                v___x_2141_ = v___x_2136_;
                                v_isShared_2142_ = v_isSharedCheck_2146_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2139_);
                                lean_dec(v___x_2136_);
                                v___x_2141_ = lean_box(0);
                                v_isShared_2142_ = v_isSharedCheck_2146_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_p_2126_);
                        lean_dec(v_fvarId_2125_);
                        lean_dec(v_mvarId_2123_);
                        v_a_2147_ = lean_ctor_get(v___x_2133_, 0);
                        v_isSharedCheck_2154_ = (!lean_is_exclusive(v___x_2133_)) as u8;
                        if v_isSharedCheck_2154_ == 0 {
                            v___x_2149_ = v___x_2133_;
                            v_isShared_2150_ = v_isSharedCheck_2154_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2147_);
                            lean_dec(v___x_2133_);
                            v___x_2149_ = lean_box(0);
                            v_isShared_2150_ = v_isSharedCheck_2154_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_p_2126_);
                    lean_dec(v_fvarId_2125_);
                    lean_dec(v_mvarId_2123_);
                    v_a_2155_ = lean_ctor_get(v___x_2132_, 0);
                    v_isSharedCheck_2162_ = (!lean_is_exclusive(v___x_2132_)) as u8;
                    if v_isSharedCheck_2162_ == 0 {
                        v___x_2157_ = v___x_2132_;
                        v_isShared_2158_ = v_isSharedCheck_2162_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2155_);
                        lean_dec(v___x_2132_);
                        v___x_2157_ = lean_box(0);
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
                    v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
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
                    v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
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
                    v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
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
    mut v_mvarId_2163_: *mut LeanObject,
    mut v___x_2164_: *mut LeanObject,
    mut v_fvarId_2165_: *mut LeanObject,
    mut v_p_2166_: *mut LeanObject,
    mut v___y_2167_: *mut LeanObject,
    mut v___y_2168_: *mut LeanObject,
    mut v___y_2169_: *mut LeanObject,
    mut v___y_2170_: *mut LeanObject,
    mut v___y_2171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2172_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2170_);
    lean_dec_ref(v___y_2169_);
    lean_dec(v___y_2168_);
    lean_dec_ref(v___y_2167_);
    return v_res_2172_;
}
pub unsafe fn l_Lean_MVarId_deltaLocalDecl(
    mut v_mvarId_2173_: *mut LeanObject,
    mut v_fvarId_2174_: *mut LeanObject,
    mut v_p_2175_: *mut LeanObject,
    mut v_a_2176_: *mut LeanObject,
    mut v_a_2177_: *mut LeanObject,
    mut v_a_2178_: *mut LeanObject,
    mut v_a_2179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    v___x_2181_ = l_Lean_MVarId_deltaTarget___closed__1;
    lean_inc(v_mvarId_2173_);
    v___f_2182_ = lean_alloc_closure(
        l_Lean_MVarId_deltaLocalDecl___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___f_2182_, 0, v_mvarId_2173_);
    lean_closure_set(v___f_2182_, 1, v___x_2181_);
    lean_closure_set(v___f_2182_, 2, v_fvarId_2174_);
    lean_closure_set(v___f_2182_, 3, v_p_2175_);
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
    mut v_mvarId_2184_: *mut LeanObject,
    mut v_fvarId_2185_: *mut LeanObject,
    mut v_p_2186_: *mut LeanObject,
    mut v_a_2187_: *mut LeanObject,
    mut v_a_2188_: *mut LeanObject,
    mut v_a_2189_: *mut LeanObject,
    mut v_a_2190_: *mut LeanObject,
    mut v_a_2191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2192_: *mut LeanObject = core::ptr::null_mut();
    v_res_2192_ = l_Lean_MVarId_deltaLocalDecl(
        v_mvarId_2184_,
        v_fvarId_2185_,
        v_p_2186_,
        v_a_2187_,
        v_a_2188_,
        v_a_2189_,
        v_a_2190_,
    );
    lean_dec(v_a_2190_);
    lean_dec_ref(v_a_2189_);
    lean_dec(v_a_2188_);
    lean_dec_ref(v_a_2187_);
    return v_res_2192_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Delta(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Delta(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Delta(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Replace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Transform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Delta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Delta(builtin);
}
