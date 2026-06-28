// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.EmbeddedConstraint
// Imports: Std.Tactic.BVDecide.Normalize.Bool Lean.Meta.Tactic.BVDecide.Normalize.Basic
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_hash,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
};
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_toExpr;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_FVarId_getType___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::Basic::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic,
};
use crate::r#gen::Lean::Meta::Tactic::Clear::l_Lean_MVarId_tryClearMany;
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::l_Lean_Meta_simpGoal;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::l_Lean_Meta_getSimpCongrTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    l_Lean_Meta_SimpTheoremsArray_addTheorem, l_Lean_Meta_simpGlobalConfig,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_mkContext___redArg;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_getPropHyps;
use crate::r#gen::Std::Tactic::BVDecide::Normalize::Bool::{
    initialize_Std_Tactic_BVDecide_Normalize_Bool,
    runtime_initialize_Std_Tactic_BVDecide_Normalize_Bool,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8, lean_ctor_set_usize,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__0_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__3_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__2_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__3_value) as *mut LeanObject,9255189395584251158 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__5:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__7:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__8:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__9:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__10:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__11:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__1_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__2_value:
    LeanStringObject<31> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        101, 109, 98, 101, 100, 100, 101, 100, 67, 111, 110, 115, 116, 114, 97, 105, 110, 116, 83,
        117, 98, 115, 116, 105, 116, 117, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__3_value:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__2_value
        ) as *mut LeanObject,
        15708030456876490904 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__4_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__4_value
) as *mut LeanObject;
pub static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__4_value
)
    as *mut LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg___lam__0(
    mut v_x_586_: *mut LeanObject,
    mut v___y_587_: *mut LeanObject,
    mut v___y_588_: *mut LeanObject,
    mut v___y_589_: *mut LeanObject,
    mut v___y_590_: *mut LeanObject,
    mut v___y_591_: *mut LeanObject,
    mut v___y_592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_588_);
    lean_inc_ref(v___y_587_);
    v___x_594_ = lean_apply_7(
        v_x_586_,
        v___y_587_,
        v___y_588_,
        v___y_589_,
        v___y_590_,
        v___y_591_,
        v___y_592_,
        lean_box(0),
    );
    return v___x_594_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg___lam__0___boxed(
    mut v_x_595_: *mut LeanObject,
    mut v___y_596_: *mut LeanObject,
    mut v___y_597_: *mut LeanObject,
    mut v___y_598_: *mut LeanObject,
    mut v___y_599_: *mut LeanObject,
    mut v___y_600_: *mut LeanObject,
    mut v___y_601_: *mut LeanObject,
    mut v___y_602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_603_: *mut LeanObject = core::ptr::null_mut();
    v_res_603_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg___lam__0(v_x_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
    lean_dec(v___y_597_);
    lean_dec_ref(v___y_596_);
    return v_res_603_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(
    mut v_mvarId_604_: *mut LeanObject,
    mut v_x_605_: *mut LeanObject,
    mut v___y_606_: *mut LeanObject,
    mut v___y_607_: *mut LeanObject,
    mut v___y_608_: *mut LeanObject,
    mut v___y_609_: *mut LeanObject,
    mut v___y_610_: *mut LeanObject,
    mut v___y_611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_618_: u8 = 0;
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_622_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_607_);
                lean_inc_ref(v___y_606_);
                v___f_613_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                lean_closure_set(v___f_613_, 0, v_x_605_);
                lean_closure_set(v___f_613_, 1, v___y_606_);
                lean_closure_set(v___f_613_, 2, v___y_607_);
                v___x_614_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_604_,
                    v___f_613_,
                    v___y_608_,
                    v___y_609_,
                    v___y_610_,
                    v___y_611_,
                );
                if lean_obj_tag(v___x_614_) == 0 {
                    return v___x_614_;
                } else {
                    v_a_615_ = lean_ctor_get(v___x_614_, 0);
                    v_isSharedCheck_622_ = (!lean_is_exclusive(v___x_614_)) as u8;
                    if v_isSharedCheck_622_ == 0 {
                        v___x_617_ = v___x_614_;
                        v_isShared_618_ = v_isSharedCheck_622_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_615_);
                        lean_dec(v___x_614_);
                        v___x_617_ = lean_box(0);
                        v_isShared_618_ = v_isSharedCheck_622_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_618_ == 0 {
                    v___x_620_ = v___x_617_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
                    v___x_620_ = v_reuseFailAlloc_621_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_620_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg___boxed(
    mut v_mvarId_623_: *mut LeanObject,
    mut v_x_624_: *mut LeanObject,
    mut v___y_625_: *mut LeanObject,
    mut v___y_626_: *mut LeanObject,
    mut v___y_627_: *mut LeanObject,
    mut v___y_628_: *mut LeanObject,
    mut v___y_629_: *mut LeanObject,
    mut v___y_630_: *mut LeanObject,
    mut v___y_631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_632_: *mut LeanObject = core::ptr::null_mut();
    v_res_632_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_mvarId_623_, v_x_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
    lean_dec(v___y_630_);
    lean_dec_ref(v___y_629_);
    lean_dec(v___y_628_);
    lean_dec_ref(v___y_627_);
    lean_dec(v___y_626_);
    lean_dec_ref(v___y_625_);
    return v_res_632_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(
    mut v_00_u03b1_633_: *mut LeanObject,
    mut v_mvarId_634_: *mut LeanObject,
    mut v_x_635_: *mut LeanObject,
    mut v___y_636_: *mut LeanObject,
    mut v___y_637_: *mut LeanObject,
    mut v___y_638_: *mut LeanObject,
    mut v___y_639_: *mut LeanObject,
    mut v___y_640_: *mut LeanObject,
    mut v___y_641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    v___x_643_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_mvarId_634_, v_x_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
    return v___x_643_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___boxed(
    mut v_00_u03b1_644_: *mut LeanObject,
    mut v_mvarId_645_: *mut LeanObject,
    mut v_x_646_: *mut LeanObject,
    mut v___y_647_: *mut LeanObject,
    mut v___y_648_: *mut LeanObject,
    mut v___y_649_: *mut LeanObject,
    mut v___y_650_: *mut LeanObject,
    mut v___y_651_: *mut LeanObject,
    mut v___y_652_: *mut LeanObject,
    mut v___y_653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_654_: *mut LeanObject = core::ptr::null_mut();
    v_res_654_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(v_00_u03b1_644_, v_mvarId_645_, v_x_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
    lean_dec(v___y_652_);
    lean_dec_ref(v___y_651_);
    lean_dec(v___y_650_);
    lean_dec_ref(v___y_649_);
    lean_dec(v___y_648_);
    lean_dec_ref(v___y_647_);
    return v_res_654_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(
    mut v___y_655_: *mut LeanObject,
    mut v___y_656_: *mut LeanObject,
    mut v___y_657_: *mut LeanObject,
    mut v___y_658_: *mut LeanObject,
    mut v___y_659_: *mut LeanObject,
    mut v___y_660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    v___x_662_ = l_Lean_Meta_getPropHyps(v___y_657_, v___y_658_, v___y_659_, v___y_660_);
    return v___x_662_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___boxed(
    mut v___y_663_: *mut LeanObject,
    mut v___y_664_: *mut LeanObject,
    mut v___y_665_: *mut LeanObject,
    mut v___y_666_: *mut LeanObject,
    mut v___y_667_: *mut LeanObject,
    mut v___y_668_: *mut LeanObject,
    mut v___y_669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_670_: *mut LeanObject = core::ptr::null_mut();
    v_res_670_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(
        v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_,
    );
    lean_dec(v___y_668_);
    lean_dec_ref(v___y_667_);
    lean_dec(v___y_666_);
    lean_dec_ref(v___y_665_);
    lean_dec(v___y_664_);
    lean_dec_ref(v___y_663_);
    return v_res_670_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_x_671_: *mut LeanObject,
    mut v_x_672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_678_: u8 = 0;
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: u64 = 0;
    let mut v___x_681_: u64 = 0;
    let mut v___x_682_: u64 = 0;
    let mut v_fold_683_: u64 = 0;
    let mut v___x_684_: u64 = 0;
    let mut v___x_685_: u64 = 0;
    let mut v___x_686_: u64 = 0;
    let mut v___x_687_: usize = 0;
    let mut v___x_688_: usize = 0;
    let mut v___x_689_: usize = 0;
    let mut v___x_690_: usize = 0;
    let mut v___x_691_: usize = 0;
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_698_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_672_) == 0 {
                    return v_x_671_;
                } else {
                    v_key_673_ = lean_ctor_get(v_x_672_, 0);
                    v_value_674_ = lean_ctor_get(v_x_672_, 1);
                    v_tail_675_ = lean_ctor_get(v_x_672_, 2);
                    v_isSharedCheck_698_ = (!lean_is_exclusive(v_x_672_)) as u8;
                    if v_isSharedCheck_698_ == 0 {
                        v___x_677_ = v_x_672_;
                        v_isShared_678_ = v_isSharedCheck_698_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_675_);
                        lean_inc(v_value_674_);
                        lean_inc(v_key_673_);
                        lean_dec(v_x_672_);
                        v___x_677_ = lean_box(0);
                        v_isShared_678_ = v_isSharedCheck_698_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_679_ = lean_array_get_size(v_x_671_);
                v___x_680_ = l_Lean_Expr_hash(v_key_673_);
                v___x_681_ = 32u64;
                v___x_682_ = lean_uint64_shift_right(v___x_680_, v___x_681_);
                v_fold_683_ = lean_uint64_xor(v___x_680_, v___x_682_);
                v___x_684_ = 16u64;
                v___x_685_ = lean_uint64_shift_right(v_fold_683_, v___x_684_);
                v___x_686_ = lean_uint64_xor(v_fold_683_, v___x_685_);
                v___x_687_ = lean_uint64_to_usize(v___x_686_);
                v___x_688_ = lean_usize_of_nat(v___x_679_);
                v___x_689_ = 1usize;
                v___x_690_ = lean_usize_sub(v___x_688_, v___x_689_);
                v___x_691_ = lean_usize_land(v___x_687_, v___x_690_);
                v___x_692_ = lean_array_uget_borrowed(v_x_671_, v___x_691_);
                lean_inc(v___x_692_);
                if v_isShared_678_ == 0 {
                    lean_ctor_set(v___x_677_, 2, v___x_692_);
                    v___x_694_ = v___x_677_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_697_, 0, v_key_673_);
                    lean_ctor_set(v_reuseFailAlloc_697_, 1, v_value_674_);
                    lean_ctor_set(v_reuseFailAlloc_697_, 2, v___x_692_);
                    v___x_694_ = v_reuseFailAlloc_697_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_695_ = lean_array_uset(v_x_671_, v___x_691_, v___x_694_);
                v_x_671_ = v___x_695_;
                v_x_672_ = v_tail_675_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4___redArg(
    mut v_i_699_: *mut LeanObject,
    mut v_source_700_: *mut LeanObject,
    mut v_target_701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: u8 = 0;
    let mut v_es_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_702_ = lean_array_get_size(v_source_700_);
                v___x_703_ = lean_nat_dec_lt(v_i_699_, v___x_702_);
                if v___x_703_ == 0 {
                    lean_dec_ref(v_source_700_);
                    lean_dec(v_i_699_);
                    return v_target_701_;
                } else {
                    v_es_704_ = lean_array_fget(v_source_700_, v_i_699_);
                    v___x_705_ = lean_box(0);
                    v_source_706_ = lean_array_fset(v_source_700_, v_i_699_, v___x_705_);
                    v_target_707_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4_spec__6___redArg(v_target_701_, v_es_704_);
                    v___x_708_ = lean_unsigned_to_nat(1);
                    v___x_709_ = lean_nat_add(v_i_699_, v___x_708_);
                    lean_dec(v_i_699_);
                    v_i_699_ = v___x_709_;
                    v_source_700_ = v_source_706_;
                    v_target_701_ = v_target_707_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2___redArg(
    mut v_data_711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    v___x_712_ = lean_array_get_size(v_data_711_);
    v___x_713_ = lean_unsigned_to_nat(2);
    v_nbuckets_714_ = lean_nat_mul(v___x_712_, v___x_713_);
    v___x_715_ = lean_unsigned_to_nat(0);
    v___x_716_ = lean_box(0);
    v___x_717_ = lean_mk_array(v_nbuckets_714_, v___x_716_);
    v___x_718_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4___redArg(v___x_715_, v_data_711_, v___x_717_);
    return v___x_718_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg(
    mut v_a_719_: *mut LeanObject,
    mut v_x_720_: *mut LeanObject,
) -> u8 {
    let mut v___x_721_: u8 = 0;
    let mut v_key_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_720_) == 0 {
                    v___x_721_ = 0;
                    return v___x_721_;
                } else {
                    v_key_722_ = lean_ctor_get(v_x_720_, 0);
                    v_tail_723_ = lean_ctor_get(v_x_720_, 2);
                    v___x_724_ = lean_expr_eqv(v_key_722_, v_a_719_);
                    if v___x_724_ == 0 {
                        v_x_720_ = v_tail_723_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_724_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg___boxed(
    mut v_a_726_: *mut LeanObject,
    mut v_x_727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_728_: u8 = 0;
    let mut v_r_729_: *mut LeanObject = core::ptr::null_mut();
    v_res_728_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg(v_a_726_, v_x_727_);
    lean_dec(v_x_727_);
    lean_dec_ref(v_a_726_);
    v_r_729_ = lean_box((v_res_728_) as usize);
    return v_r_729_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(
    mut v_m_730_: *mut LeanObject,
    mut v_a_731_: *mut LeanObject,
    mut v_b_732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: u64 = 0;
    let mut v___x_737_: u64 = 0;
    let mut v___x_738_: u64 = 0;
    let mut v_fold_739_: u64 = 0;
    let mut v___x_740_: u64 = 0;
    let mut v___x_741_: u64 = 0;
    let mut v___x_742_: u64 = 0;
    let mut v___x_743_: usize = 0;
    let mut v___x_744_: usize = 0;
    let mut v___x_745_: usize = 0;
    let mut v___x_746_: usize = 0;
    let mut v___x_747_: usize = 0;
    let mut v_bkt_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: u8 = 0;
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_752_: u8 = 0;
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: u8 = 0;
    let mut v_val_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_770_: u8 = 0;
    let mut v_unused_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_772_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_733_ = lean_ctor_get(v_m_730_, 0);
                v_buckets_734_ = lean_ctor_get(v_m_730_, 1);
                v___x_735_ = lean_array_get_size(v_buckets_734_);
                v___x_736_ = l_Lean_Expr_hash(v_a_731_);
                v___x_737_ = 32u64;
                v___x_738_ = lean_uint64_shift_right(v___x_736_, v___x_737_);
                v_fold_739_ = lean_uint64_xor(v___x_736_, v___x_738_);
                v___x_740_ = 16u64;
                v___x_741_ = lean_uint64_shift_right(v_fold_739_, v___x_740_);
                v___x_742_ = lean_uint64_xor(v_fold_739_, v___x_741_);
                v___x_743_ = lean_uint64_to_usize(v___x_742_);
                v___x_744_ = lean_usize_of_nat(v___x_735_);
                v___x_745_ = 1usize;
                v___x_746_ = lean_usize_sub(v___x_744_, v___x_745_);
                v___x_747_ = lean_usize_land(v___x_743_, v___x_746_);
                v_bkt_748_ = lean_array_uget_borrowed(v_buckets_734_, v___x_747_);
                v___x_749_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg(v_a_731_, v_bkt_748_);
                if v___x_749_ == 0 {
                    lean_inc_ref(v_buckets_734_);
                    lean_inc(v_size_733_);
                    v_isSharedCheck_770_ = (!lean_is_exclusive(v_m_730_)) as u8;
                    if v_isSharedCheck_770_ == 0 {
                        v_unused_771_ = lean_ctor_get(v_m_730_, 1);
                        lean_dec(v_unused_771_);
                        v_unused_772_ = lean_ctor_get(v_m_730_, 0);
                        lean_dec(v_unused_772_);
                        v___x_751_ = v_m_730_;
                        v_isShared_752_ = v_isSharedCheck_770_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_730_);
                        v___x_751_ = lean_box(0);
                        v_isShared_752_ = v_isSharedCheck_770_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_732_);
                    lean_dec_ref(v_a_731_);
                    return v_m_730_;
                }
            }
            1 => {
                v___x_753_ = lean_unsigned_to_nat(1);
                v_size_x27_754_ = lean_nat_add(v_size_733_, v___x_753_);
                lean_dec(v_size_733_);
                lean_inc(v_bkt_748_);
                v___x_755_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_755_, 0, v_a_731_);
                lean_ctor_set(v___x_755_, 1, v_b_732_);
                lean_ctor_set(v___x_755_, 2, v_bkt_748_);
                v_buckets_x27_756_ = lean_array_uset(v_buckets_734_, v___x_747_, v___x_755_);
                v___x_757_ = lean_unsigned_to_nat(4);
                v___x_758_ = lean_nat_mul(v_size_x27_754_, v___x_757_);
                v___x_759_ = lean_unsigned_to_nat(3);
                v___x_760_ = lean_nat_div(v___x_758_, v___x_759_);
                lean_dec(v___x_758_);
                v___x_761_ = lean_array_get_size(v_buckets_x27_756_);
                v___x_762_ = lean_nat_dec_le(v___x_760_, v___x_761_);
                lean_dec(v___x_760_);
                if v___x_762_ == 0 {
                    v_val_763_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2___redArg(v_buckets_x27_756_);
                    if v_isShared_752_ == 0 {
                        lean_ctor_set(v___x_751_, 1, v_val_763_);
                        lean_ctor_set(v___x_751_, 0, v_size_x27_754_);
                        v___x_765_ = v___x_751_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_766_, 0, v_size_x27_754_);
                        lean_ctor_set(v_reuseFailAlloc_766_, 1, v_val_763_);
                        v___x_765_ = v_reuseFailAlloc_766_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_752_ == 0 {
                        lean_ctor_set(v___x_751_, 1, v_buckets_x27_756_);
                        lean_ctor_set(v___x_751_, 0, v_size_x27_754_);
                        v___x_768_ = v___x_751_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_769_, 0, v_size_x27_754_);
                        lean_ctor_set(v_reuseFailAlloc_769_, 1, v_buckets_x27_756_);
                        v___x_768_ = v_reuseFailAlloc_769_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_765_;
            }
            3 => {
                return v___x_768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg(
    mut v_m_773_: *mut LeanObject,
    mut v_a_774_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: u64 = 0;
    let mut v___x_778_: u64 = 0;
    let mut v___x_779_: u64 = 0;
    let mut v_fold_780_: u64 = 0;
    let mut v___x_781_: u64 = 0;
    let mut v___x_782_: u64 = 0;
    let mut v___x_783_: u64 = 0;
    let mut v___x_784_: usize = 0;
    let mut v___x_785_: usize = 0;
    let mut v___x_786_: usize = 0;
    let mut v___x_787_: usize = 0;
    let mut v___x_788_: usize = 0;
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: u8 = 0;
    v_buckets_775_ = lean_ctor_get(v_m_773_, 1);
    v___x_776_ = lean_array_get_size(v_buckets_775_);
    v___x_777_ = l_Lean_Expr_hash(v_a_774_);
    v___x_778_ = 32u64;
    v___x_779_ = lean_uint64_shift_right(v___x_777_, v___x_778_);
    v_fold_780_ = lean_uint64_xor(v___x_777_, v___x_779_);
    v___x_781_ = 16u64;
    v___x_782_ = lean_uint64_shift_right(v_fold_780_, v___x_781_);
    v___x_783_ = lean_uint64_xor(v_fold_780_, v___x_782_);
    v___x_784_ = lean_uint64_to_usize(v___x_783_);
    v___x_785_ = lean_usize_of_nat(v___x_776_);
    v___x_786_ = 1usize;
    v___x_787_ = lean_usize_sub(v___x_785_, v___x_786_);
    v___x_788_ = lean_usize_land(v___x_784_, v___x_787_);
    v___x_789_ = lean_array_uget_borrowed(v_buckets_775_, v___x_788_);
    v___x_790_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg(v_a_774_, v___x_789_);
    return v___x_790_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg___boxed(
    mut v_m_791_: *mut LeanObject,
    mut v_a_792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_793_: u8 = 0;
    let mut v_r_794_: *mut LeanObject = core::ptr::null_mut();
    v_res_793_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg(v_m_791_, v_a_792_);
    lean_dec_ref(v_a_792_);
    lean_dec_ref(v_m_791_);
    v_r_794_ = lean_box((v_res_793_) as usize);
    return v_r_794_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(
    mut v_as_803_: *mut LeanObject,
    mut v_sz_804_: usize,
    mut v_i_805_: usize,
    mut v_b_806_: *mut LeanObject,
    mut v___y_807_: *mut LeanObject,
    mut v___y_808_: *mut LeanObject,
    mut v___y_809_: *mut LeanObject,
    mut v___y_810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: usize = 0;
    let mut v___x_815_: usize = 0;
    let mut v___x_817_: u8 = 0;
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v_fst_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_831_: u8 = 0;
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: u8 = 0;
    let mut v_arg_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: u8 = 0;
    let mut v_arg_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: u8 = 0;
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: u8 = 0;
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: u8 = 0;
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: u8 = 0;
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_870_: u8 = 0;
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut v_a_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_878_: u8 = 0;
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_882_: u8 = 0;
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_886_: u8 = 0;
    let mut v_isSharedCheck_887_: u8 = 0;
    let mut v_unused_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_892_: u8 = 0;
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_817_ = lean_usize_dec_lt(v_i_805_, v_sz_804_);
                if v___x_817_ == 0 {
                    v___x_818_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_818_, 0, v_b_806_);
                    return v___x_818_;
                } else {
                    v_a_819_ = lean_array_uget_borrowed(v_as_803_, v_i_805_);
                    lean_inc(v_a_819_);
                    v___x_820_ = l_Lean_FVarId_getType___redArg(
                        v_a_819_, v___y_807_, v___y_809_, v___y_810_,
                    );
                    if lean_obj_tag(v___x_820_) == 0 {
                        v_snd_821_ = lean_ctor_get(v_b_806_, 1);
                        lean_inc(v_snd_821_);
                        v_a_822_ = lean_ctor_get(v___x_820_, 0);
                        lean_inc(v_a_822_);
                        lean_dec_ref_known(v___x_820_, 1);
                        v_fst_823_ = lean_ctor_get(v_b_806_, 0);
                        v_isSharedCheck_887_ = (!lean_is_exclusive(v_b_806_)) as u8;
                        if v_isSharedCheck_887_ == 0 {
                            v_unused_888_ = lean_ctor_get(v_b_806_, 1);
                            lean_dec(v_unused_888_);
                            v___x_825_ = v_b_806_;
                            v_isShared_826_ = v_isSharedCheck_887_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_fst_823_);
                            lean_dec(v_b_806_);
                            v___x_825_ = lean_box(0);
                            v_isShared_826_ = v_isSharedCheck_887_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_806_);
                        v_a_889_ = lean_ctor_get(v___x_820_, 0);
                        v_isSharedCheck_896_ = (!lean_is_exclusive(v___x_820_)) as u8;
                        if v_isSharedCheck_896_ == 0 {
                            v___x_891_ = v___x_820_;
                            v_isShared_892_ = v_isSharedCheck_896_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_889_);
                            lean_dec(v___x_820_);
                            v___x_891_ = lean_box(0);
                            v_isShared_892_ = v_isSharedCheck_896_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_814_ = 1usize;
                v___x_815_ = lean_usize_add(v_i_805_, v___x_814_);
                v_i_805_ = v___x_815_;
                v_b_806_ = v_a_813_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_827_ = lean_ctor_get(v_snd_821_, 0);
                v_snd_828_ = lean_ctor_get(v_snd_821_, 1);
                v_isSharedCheck_886_ = (!lean_is_exclusive(v_snd_821_)) as u8;
                if v_isSharedCheck_886_ == 0 {
                    v___x_830_ = v_snd_821_;
                    v_isShared_831_ = v_isSharedCheck_886_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_828_);
                    lean_inc(v_fst_827_);
                    lean_dec(v_snd_821_);
                    v___x_830_ = lean_box(0);
                    v_isShared_831_ = v_isSharedCheck_886_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_839_ = l_Lean_Expr_cleanupAnnotations(v_a_822_);
                v___x_840_ = l_Lean_Expr_isApp(v___x_839_);
                if v___x_840_ == 0 {
                    lean_dec_ref(v___x_839_);
                    state = 4;
                    continue;
                } else {
                    v_arg_841_ = lean_ctor_get(v___x_839_, 1);
                    lean_inc_ref(v_arg_841_);
                    v___x_842_ = l_Lean_Expr_appFnCleanup___redArg(v___x_839_);
                    v___x_843_ = l_Lean_Expr_isApp(v___x_842_);
                    if v___x_843_ == 0 {
                        lean_dec_ref(v___x_842_);
                        lean_dec_ref(v_arg_841_);
                        state = 4;
                        continue;
                    } else {
                        v_arg_844_ = lean_ctor_get(v___x_842_, 1);
                        lean_inc_ref(v_arg_844_);
                        v___x_845_ = l_Lean_Expr_appFnCleanup___redArg(v___x_842_);
                        v___x_846_ = l_Lean_Expr_isApp(v___x_845_);
                        if v___x_846_ == 0 {
                            lean_dec_ref(v___x_845_);
                            lean_dec_ref(v_arg_844_);
                            lean_dec_ref(v_arg_841_);
                            state = 4;
                            continue;
                        } else {
                            v___x_847_ = l_Lean_Expr_appFnCleanup___redArg(v___x_845_);
                            v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__1;
                            v___x_849_ = l_Lean_Expr_isConstOf(v___x_847_, v___x_848_);
                            lean_dec_ref(v___x_847_);
                            if v___x_849_ == 0 {
                                lean_dec_ref(v_arg_844_);
                                lean_dec_ref(v_arg_841_);
                                state = 4;
                                continue;
                            } else {
                                lean_del_object(v___x_830_);
                                lean_del_object(v___x_825_);
                                v___x_850_ = l_Lean_Expr_cleanupAnnotations(v_arg_841_);
                                v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4;
                                v___x_852_ = l_Lean_Expr_isConstOf(v___x_850_, v___x_851_);
                                lean_dec_ref(v___x_850_);
                                if v___x_852_ == 0 {
                                    lean_dec_ref(v_arg_844_);
                                    v___x_853_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_853_, 0, v_fst_827_);
                                    lean_ctor_set(v___x_853_, 1, v_snd_828_);
                                    v___x_854_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_854_, 0, v_fst_823_);
                                    lean_ctor_set(v___x_854_, 1, v___x_853_);
                                    v_a_813_ = v___x_854_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_855_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg(v_fst_827_, v_arg_844_);
                                    if v___x_855_ == 0 {
                                        lean_inc(v_a_819_);
                                        v___x_856_ = l_Lean_FVarId_getDecl___redArg(
                                            v_a_819_, v___y_807_, v___y_809_, v___y_810_,
                                        );
                                        if lean_obj_tag(v___x_856_) == 0 {
                                            v_a_857_ = lean_ctor_get(v___x_856_, 0);
                                            lean_inc(v_a_857_);
                                            lean_dec_ref_known(v___x_856_, 1);
                                            v___x_858_ = l_Lean_LocalDecl_toExpr(v_a_857_);
                                            lean_inc(v_a_819_);
                                            v___x_859_ = lean_alloc_ctor(1, 1, (0) as u32);
                                            lean_ctor_set(v___x_859_, 0, v_a_819_);
                                            v___x_860_ = l_Lean_Meta_simpGlobalConfig;
                                            v___x_861_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(
                                                v_fst_823_, v___x_859_, v___x_858_, v___x_860_,
                                                v___y_807_, v___y_808_, v___y_809_, v___y_810_,
                                            );
                                            if lean_obj_tag(v___x_861_) == 0 {
                                                v_a_862_ = lean_ctor_get(v___x_861_, 0);
                                                lean_inc(v_a_862_);
                                                lean_dec_ref_known(v___x_861_, 1);
                                                v___x_863_ = lean_box(0);
                                                v___x_864_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_fst_827_, v_arg_844_, v___x_863_);
                                                v___x_865_ = lean_alloc_ctor(0, 2, (0) as u32);
                                                lean_ctor_set(v___x_865_, 0, v___x_864_);
                                                lean_ctor_set(v___x_865_, 1, v_snd_828_);
                                                v___x_866_ = lean_alloc_ctor(0, 2, (0) as u32);
                                                lean_ctor_set(v___x_866_, 0, v_a_862_);
                                                lean_ctor_set(v___x_866_, 1, v___x_865_);
                                                v_a_813_ = v___x_866_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec_ref(v_arg_844_);
                                                lean_dec(v_snd_828_);
                                                lean_dec(v_fst_827_);
                                                v_a_867_ = lean_ctor_get(v___x_861_, 0);
                                                v_isSharedCheck_874_ =
                                                    (!lean_is_exclusive(v___x_861_)) as u8;
                                                if v_isSharedCheck_874_ == 0 {
                                                    v___x_869_ = v___x_861_;
                                                    v_isShared_870_ = v_isSharedCheck_874_;
                                                    state = 7;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_867_);
                                                    lean_dec(v___x_861_);
                                                    v___x_869_ = lean_box(0);
                                                    v_isShared_870_ = v_isSharedCheck_874_;
                                                    state = 7;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v_arg_844_);
                                            lean_dec(v_snd_828_);
                                            lean_dec(v_fst_827_);
                                            lean_dec(v_fst_823_);
                                            v_a_875_ = lean_ctor_get(v___x_856_, 0);
                                            v_isSharedCheck_882_ =
                                                (!lean_is_exclusive(v___x_856_)) as u8;
                                            if v_isSharedCheck_882_ == 0 {
                                                v___x_877_ = v___x_856_;
                                                v_isShared_878_ = v_isSharedCheck_882_;
                                                state = 9;
                                                continue;
                                            } else {
                                                lean_inc(v_a_875_);
                                                lean_dec(v___x_856_);
                                                v___x_877_ = lean_box(0);
                                                v_isShared_878_ = v_isSharedCheck_882_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v_arg_844_);
                                        lean_inc(v_a_819_);
                                        v___x_883_ = lean_array_push(v_snd_828_, v_a_819_);
                                        v___x_884_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_884_, 0, v_fst_827_);
                                        lean_ctor_set(v___x_884_, 1, v___x_883_);
                                        v___x_885_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_885_, 0, v_fst_823_);
                                        lean_ctor_set(v___x_885_, 1, v___x_884_);
                                        v_a_813_ = v___x_885_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            4 => {
                if v_isShared_831_ == 0 {
                    v___x_834_ = v___x_830_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_838_, 0, v_fst_827_);
                    lean_ctor_set(v_reuseFailAlloc_838_, 1, v_snd_828_);
                    v___x_834_ = v_reuseFailAlloc_838_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_826_ == 0 {
                    lean_ctor_set(v___x_825_, 1, v___x_834_);
                    v___x_836_ = v___x_825_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_837_, 0, v_fst_823_);
                    lean_ctor_set(v_reuseFailAlloc_837_, 1, v___x_834_);
                    v___x_836_ = v_reuseFailAlloc_837_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_813_ = v___x_836_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_870_ == 0 {
                    v___x_872_ = v___x_869_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
                    v___x_872_ = v_reuseFailAlloc_873_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_872_;
            }
            9 => {
                if v_isShared_878_ == 0 {
                    v___x_880_ = v___x_877_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
                    v___x_880_ = v_reuseFailAlloc_881_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_880_;
            }
            11 => {
                if v_isShared_892_ == 0 {
                    v___x_894_ = v___x_891_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
                    v___x_894_ = v_reuseFailAlloc_895_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_894_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___boxed(
    mut v_as_897_: *mut LeanObject,
    mut v_sz_898_: *mut LeanObject,
    mut v_i_899_: *mut LeanObject,
    mut v_b_900_: *mut LeanObject,
    mut v___y_901_: *mut LeanObject,
    mut v___y_902_: *mut LeanObject,
    mut v___y_903_: *mut LeanObject,
    mut v___y_904_: *mut LeanObject,
    mut v___y_905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_906_: usize = 0;
    let mut v_i_boxed_907_: usize = 0;
    let mut v_res_908_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_906_ = lean_unbox_usize(v_sz_898_);
    lean_dec(v_sz_898_);
    v_i_boxed_907_ = lean_unbox_usize(v_i_899_);
    lean_dec(v_i_899_);
    v_res_908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v_as_897_, v_sz_boxed_906_, v_i_boxed_907_, v_b_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
    lean_dec(v___y_904_);
    lean_dec_ref(v___y_903_);
    lean_dec(v___y_902_);
    lean_dec_ref(v___y_901_);
    lean_dec_ref(v_as_897_);
    return v_res_908_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    v___x_911_ = lean_box(0);
    v___x_912_ = lean_unsigned_to_nat(16);
    v___x_913_ = lean_mk_array(v___x_912_, v___x_911_);
    return v___x_913_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__2()
-> *mut LeanObject {
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seen_916_: *mut LeanObject = core::ptr::null_mut();
    v___x_914_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__1,
    );
    v___x_915_ = lean_unsigned_to_nat(0);
    v_seen_916_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_seen_916_, 0, v___x_915_);
    lean_ctor_set(v_seen_916_, 1, v___x_914_);
    return v_seen_916_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__3()
-> *mut LeanObject {
    let mut v_relevantHyps_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seen_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    v_relevantHyps_917_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__0;
    v_seen_918_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__2,
    );
    v___x_919_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_919_, 0, v_seen_918_);
    lean_ctor_set(v___x_919_, 1, v_relevantHyps_917_);
    return v___x_919_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__4()
-> *mut LeanObject {
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    v___x_920_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__3_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__3,
    );
    v_relevantHyps_921_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__0;
    v___x_922_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_922_, 0, v_relevantHyps_921_);
    lean_ctor_set(v___x_922_, 1, v___x_920_);
    return v___x_922_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__5()
-> *mut LeanObject {
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    v___x_923_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_923_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6()
-> *mut LeanObject {
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    v___x_924_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__5_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__5,
    );
    v___x_925_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_925_, 0, v___x_924_);
    return v___x_925_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__7()
-> *mut LeanObject {
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    v___x_926_ = lean_unsigned_to_nat(0);
    v___x_927_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6,
    );
    v___x_928_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_928_, 0, v___x_927_);
    lean_ctor_set(v___x_928_, 1, v___x_926_);
    return v___x_928_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__8()
-> *mut LeanObject {
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    v___x_929_ = lean_unsigned_to_nat(32);
    v___x_930_ = lean_mk_empty_array_with_capacity(v___x_929_);
    v___x_931_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_931_, 0, v___x_930_);
    return v___x_931_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__9()
-> *mut LeanObject {
    let mut v___x_932_: usize = 0;
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    v___x_932_ = 5usize;
    v___x_933_ = lean_unsigned_to_nat(0);
    v___x_934_ = lean_unsigned_to_nat(32);
    v___x_935_ = lean_mk_empty_array_with_capacity(v___x_934_);
    v___x_936_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__8_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__8,
    );
    v___x_937_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_937_, 0, v___x_936_);
    lean_ctor_set(v___x_937_, 1, v___x_935_);
    lean_ctor_set(v___x_937_, 2, v___x_933_);
    lean_ctor_set(v___x_937_, 3, v___x_933_);
    lean_ctor_set_usize(v___x_937_, 4, v___x_932_);
    return v___x_937_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__10()
-> *mut LeanObject {
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    v___x_938_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__9_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__9,
    );
    v___x_939_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6,
    );
    v___x_940_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_940_, 0, v___x_939_);
    lean_ctor_set(v___x_940_, 1, v___x_939_);
    lean_ctor_set(v___x_940_, 2, v___x_939_);
    lean_ctor_set(v___x_940_, 3, v___x_938_);
    return v___x_940_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__11()
-> *mut LeanObject {
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    v___x_941_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__10_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__10,
    );
    v___x_942_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__7_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__7,
    );
    v___x_943_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_943_, 0, v___x_942_);
    lean_ctor_set(v___x_943_, 1, v___x_941_);
    return v___x_943_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(
    mut v_goal_944_: *mut LeanObject,
    mut v___f_945_: *mut LeanObject,
    mut v___y_946_: *mut LeanObject,
    mut v___y_947_: *mut LeanObject,
    mut v___y_948_: *mut LeanObject,
    mut v___y_949_: *mut LeanObject,
    mut v___y_950_: *mut LeanObject,
    mut v___y_951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_958_: usize = 0;
    let mut v___x_959_: usize = 0;
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_969_: u8 = 0;
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: u8 = 0;
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxSteps_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: u8 = 0;
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: u8 = 0;
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v_fst_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v_snd_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1003_: u8 = 0;
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1007_: u8 = 0;
    let mut v_a_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1011_: u8 = 0;
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1015_: u8 = 0;
    let mut v_a_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1019_: u8 = 0;
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1023_: u8 = 0;
    let mut v_a_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1027_: u8 = 0;
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1031_: u8 = 0;
    let mut v_a_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1035_: u8 = 0;
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1039_: u8 = 0;
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1044_: u8 = 0;
    let mut v_a_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1048_: u8 = 0;
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1052_: u8 = 0;
    let mut v_a_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1056_: u8 = 0;
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut v_a_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1064_: u8 = 0;
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_953_ =
                    l_Lean_Meta_getPropHyps(v___y_948_, v___y_949_, v___y_950_, v___y_951_);
                if lean_obj_tag(v___x_953_) == 0 {
                    v_a_954_ = lean_ctor_get(v___x_953_, 0);
                    lean_inc(v_a_954_);
                    lean_dec_ref_known(v___x_953_, 1);
                    v___x_955_ = lean_unsigned_to_nat(0);
                    v_relevantHyps_956_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__0;
                    v___x_957_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__4_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__4);
                    v_sz_958_ = lean_array_size(v_a_954_);
                    v___x_959_ = 0usize;
                    v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v_a_954_, v_sz_958_, v___x_959_, v___x_957_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
                    lean_dec(v_a_954_);
                    if lean_obj_tag(v___x_960_) == 0 {
                        v_a_961_ = lean_ctor_get(v___x_960_, 0);
                        lean_inc(v_a_961_);
                        lean_dec_ref_known(v___x_960_, 1);
                        v_snd_962_ = lean_ctor_get(v_a_961_, 1);
                        lean_inc(v_snd_962_);
                        v_fst_963_ = lean_ctor_get(v_a_961_, 0);
                        lean_inc(v_fst_963_);
                        lean_dec(v_a_961_);
                        v_snd_964_ = lean_ctor_get(v_snd_962_, 1);
                        lean_inc(v_snd_964_);
                        lean_dec(v_snd_962_);
                        v___x_965_ = l_Lean_MVarId_tryClearMany(
                            v_goal_944_,
                            v_snd_964_,
                            v___y_948_,
                            v___y_949_,
                            v___y_950_,
                            v___y_951_,
                        );
                        lean_dec(v_snd_964_);
                        if lean_obj_tag(v___x_965_) == 0 {
                            v_a_966_ = lean_ctor_get(v___x_965_, 0);
                            v_isSharedCheck_1044_ = (!lean_is_exclusive(v___x_965_)) as u8;
                            if v_isSharedCheck_1044_ == 0 {
                                v___x_968_ = v___x_965_;
                                v_isShared_969_ = v_isSharedCheck_1044_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_966_);
                                lean_dec(v___x_965_);
                                v___x_968_ = lean_box(0);
                                v_isShared_969_ = v_isSharedCheck_1044_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_fst_963_);
                            lean_dec_ref(v___f_945_);
                            v_a_1045_ = lean_ctor_get(v___x_965_, 0);
                            v_isSharedCheck_1052_ = (!lean_is_exclusive(v___x_965_)) as u8;
                            if v_isSharedCheck_1052_ == 0 {
                                v___x_1047_ = v___x_965_;
                                v_isShared_1048_ = v_isSharedCheck_1052_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_1045_);
                                lean_dec(v___x_965_);
                                v___x_1047_ = lean_box(0);
                                v_isShared_1048_ = v_isSharedCheck_1052_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___f_945_);
                        lean_dec(v_goal_944_);
                        v_a_1053_ = lean_ctor_get(v___x_960_, 0);
                        v_isSharedCheck_1060_ = (!lean_is_exclusive(v___x_960_)) as u8;
                        if v_isSharedCheck_1060_ == 0 {
                            v___x_1055_ = v___x_960_;
                            v_isShared_1056_ = v_isSharedCheck_1060_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_1053_);
                            lean_dec(v___x_960_);
                            v___x_1055_ = lean_box(0);
                            v_isShared_1056_ = v_isSharedCheck_1060_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___f_945_);
                    lean_dec(v_goal_944_);
                    v_a_1061_ = lean_ctor_get(v___x_953_, 0);
                    v_isSharedCheck_1068_ = (!lean_is_exclusive(v___x_953_)) as u8;
                    if v_isSharedCheck_1068_ == 0 {
                        v___x_1063_ = v___x_953_;
                        v_isShared_1064_ = v_isSharedCheck_1068_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_1061_);
                        lean_dec(v___x_953_);
                        v___x_1063_ = lean_box(0);
                        v_isShared_1064_ = v_isSharedCheck_1068_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                v___x_970_ = lean_array_get_size(v_fst_963_);
                v___x_971_ = lean_nat_dec_eq(v___x_970_, v___x_955_);
                if v___x_971_ == 0 {
                    lean_del_object(v___x_968_);
                    lean_inc(v_a_966_);
                    v___x_972_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_a_966_, v___f_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
                    if lean_obj_tag(v___x_972_) == 0 {
                        v_a_973_ = lean_ctor_get(v___x_972_, 0);
                        lean_inc(v_a_973_);
                        lean_dec_ref_known(v___x_972_, 1);
                        v___x_974_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_951_);
                        if lean_obj_tag(v___x_974_) == 0 {
                            v_a_975_ = lean_ctor_get(v___x_974_, 0);
                            lean_inc(v_a_975_);
                            lean_dec_ref_known(v___x_974_, 1);
                            v_maxSteps_976_ = lean_ctor_get(v___y_946_, 1);
                            v___x_977_ = 1;
                            v___x_978_ = lean_unsigned_to_nat(2);
                            v___x_979_ = 0;
                            v___x_980_ = lean_box(0);
                            lean_inc(v_maxSteps_976_);
                            v___x_981_ = lean_alloc_ctor(0, 3, (29) as u32);
                            lean_ctor_set(v___x_981_, 0, v_maxSteps_976_);
                            lean_ctor_set(v___x_981_, 1, v___x_978_);
                            lean_ctor_set(v___x_981_, 2, v___x_980_);
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                                v___x_971_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                                v___x_971_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 5) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 6) as u32,
                                v___x_979_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 7) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 9) as u32,
                                v___x_971_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 10) as u32,
                                v___x_971_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 11) as u32,
                                v___x_971_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 12) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 13) as u32,
                                v___x_971_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 14) as u32,
                                v___x_971_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 15) as u32,
                                v___x_971_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                                v___x_971_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 17) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 18) as u32,
                                v___x_971_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 19) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 20) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 21) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 22) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 23) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 24) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 25) as u32,
                                v___x_977_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 26) as u32,
                                v___x_971_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 27) as u32,
                                v___x_971_,
                            );
                            lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 28) as u32,
                                v___x_977_,
                            );
                            v___x_982_ = l_Lean_Options_empty;
                            v___x_983_ = l_Lean_Meta_Simp_mkContext___redArg(
                                v___x_981_, v_fst_963_, v_a_975_, v___x_982_, v___y_948_,
                                v___y_950_, v___y_951_,
                            );
                            if lean_obj_tag(v___x_983_) == 0 {
                                v_a_984_ = lean_ctor_get(v___x_983_, 0);
                                lean_inc(v_a_984_);
                                lean_dec_ref_known(v___x_983_, 1);
                                v___x_985_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__11), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__11_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__11);
                                v___x_986_ = l_Lean_Meta_simpGoal(
                                    v_a_966_,
                                    v_a_984_,
                                    v_relevantHyps_956_,
                                    v___x_980_,
                                    v___x_977_,
                                    v_a_973_,
                                    v___x_985_,
                                    v___y_948_,
                                    v___y_949_,
                                    v___y_950_,
                                    v___y_951_,
                                );
                                if lean_obj_tag(v___x_986_) == 0 {
                                    v_a_987_ = lean_ctor_get(v___x_986_, 0);
                                    v_isSharedCheck_1007_ = (!lean_is_exclusive(v___x_986_)) as u8;
                                    if v_isSharedCheck_1007_ == 0 {
                                        v___x_989_ = v___x_986_;
                                        v_isShared_990_ = v_isSharedCheck_1007_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_987_);
                                        lean_dec(v___x_986_);
                                        v___x_989_ = lean_box(0);
                                        v_isShared_990_ = v_isSharedCheck_1007_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_a_1008_ = lean_ctor_get(v___x_986_, 0);
                                    v_isSharedCheck_1015_ = (!lean_is_exclusive(v___x_986_)) as u8;
                                    if v_isSharedCheck_1015_ == 0 {
                                        v___x_1010_ = v___x_986_;
                                        v_isShared_1011_ = v_isSharedCheck_1015_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1008_);
                                        lean_dec(v___x_986_);
                                        v___x_1010_ = lean_box(0);
                                        v_isShared_1011_ = v_isSharedCheck_1015_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_973_);
                                lean_dec(v_a_966_);
                                v_a_1016_ = lean_ctor_get(v___x_983_, 0);
                                v_isSharedCheck_1023_ = (!lean_is_exclusive(v___x_983_)) as u8;
                                if v_isSharedCheck_1023_ == 0 {
                                    v___x_1018_ = v___x_983_;
                                    v_isShared_1019_ = v_isSharedCheck_1023_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_1016_);
                                    lean_dec(v___x_983_);
                                    v___x_1018_ = lean_box(0);
                                    v_isShared_1019_ = v_isSharedCheck_1023_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_973_);
                            lean_dec(v_a_966_);
                            lean_dec(v_fst_963_);
                            v_a_1024_ = lean_ctor_get(v___x_974_, 0);
                            v_isSharedCheck_1031_ = (!lean_is_exclusive(v___x_974_)) as u8;
                            if v_isSharedCheck_1031_ == 0 {
                                v___x_1026_ = v___x_974_;
                                v_isShared_1027_ = v_isSharedCheck_1031_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_1024_);
                                lean_dec(v___x_974_);
                                v___x_1026_ = lean_box(0);
                                v_isShared_1027_ = v_isSharedCheck_1031_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_966_);
                        lean_dec(v_fst_963_);
                        v_a_1032_ = lean_ctor_get(v___x_972_, 0);
                        v_isSharedCheck_1039_ = (!lean_is_exclusive(v___x_972_)) as u8;
                        if v_isSharedCheck_1039_ == 0 {
                            v___x_1034_ = v___x_972_;
                            v_isShared_1035_ = v_isSharedCheck_1039_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_1032_);
                            lean_dec(v___x_972_);
                            v___x_1034_ = lean_box(0);
                            v_isShared_1035_ = v_isSharedCheck_1039_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fst_963_);
                    lean_dec_ref(v___f_945_);
                    v___x_1040_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1040_, 0, v_a_966_);
                    if v_isShared_969_ == 0 {
                        lean_ctor_set(v___x_968_, 0, v___x_1040_);
                        v___x_1042_ = v___x_968_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
                        v___x_1042_ = v_reuseFailAlloc_1043_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_991_ = lean_ctor_get(v_a_987_, 0);
                lean_inc(v_fst_991_);
                lean_dec(v_a_987_);
                if lean_obj_tag(v_fst_991_) == 1 {
                    v_val_992_ = lean_ctor_get(v_fst_991_, 0);
                    v_isSharedCheck_1003_ = (!lean_is_exclusive(v_fst_991_)) as u8;
                    if v_isSharedCheck_1003_ == 0 {
                        v___x_994_ = v_fst_991_;
                        v_isShared_995_ = v_isSharedCheck_1003_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_992_);
                        lean_dec(v_fst_991_);
                        v___x_994_ = lean_box(0);
                        v_isShared_995_ = v_isSharedCheck_1003_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_991_);
                    if v_isShared_990_ == 0 {
                        lean_ctor_set(v___x_989_, 0, v___x_980_);
                        v___x_1005_ = v___x_989_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_980_);
                        v___x_1005_ = v_reuseFailAlloc_1006_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v_snd_996_ = lean_ctor_get(v_val_992_, 1);
                lean_inc(v_snd_996_);
                lean_dec(v_val_992_);
                if v_isShared_995_ == 0 {
                    lean_ctor_set(v___x_994_, 0, v_snd_996_);
                    v___x_998_ = v___x_994_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_snd_996_);
                    v___x_998_ = v_reuseFailAlloc_1002_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_990_ == 0 {
                    lean_ctor_set(v___x_989_, 0, v___x_998_);
                    v___x_1000_ = v___x_989_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
                    v___x_1000_ = v_reuseFailAlloc_1001_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1000_;
            }
            6 => {
                return v___x_1005_;
            }
            7 => {
                if v_isShared_1011_ == 0 {
                    v___x_1013_ = v___x_1010_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
                    v___x_1013_ = v_reuseFailAlloc_1014_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1013_;
            }
            9 => {
                if v_isShared_1019_ == 0 {
                    v___x_1021_ = v___x_1018_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
                    v___x_1021_ = v_reuseFailAlloc_1022_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1021_;
            }
            11 => {
                if v_isShared_1027_ == 0 {
                    v___x_1029_ = v___x_1026_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
                    v___x_1029_ = v_reuseFailAlloc_1030_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1029_;
            }
            13 => {
                if v_isShared_1035_ == 0 {
                    v___x_1037_ = v___x_1034_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
                    v___x_1037_ = v_reuseFailAlloc_1038_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1037_;
            }
            15 => {
                return v___x_1042_;
            }
            16 => {
                if v_isShared_1048_ == 0 {
                    v___x_1050_ = v___x_1047_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
                    v___x_1050_ = v_reuseFailAlloc_1051_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1050_;
            }
            18 => {
                if v_isShared_1056_ == 0 {
                    v___x_1058_ = v___x_1055_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
                    v___x_1058_ = v_reuseFailAlloc_1059_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1058_;
            }
            20 => {
                if v_isShared_1064_ == 0 {
                    v___x_1066_ = v___x_1063_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
                    v___x_1066_ = v_reuseFailAlloc_1067_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___boxed(
    mut v_goal_1069_: *mut LeanObject,
    mut v___f_1070_: *mut LeanObject,
    mut v___y_1071_: *mut LeanObject,
    mut v___y_1072_: *mut LeanObject,
    mut v___y_1073_: *mut LeanObject,
    mut v___y_1074_: *mut LeanObject,
    mut v___y_1075_: *mut LeanObject,
    mut v___y_1076_: *mut LeanObject,
    mut v___y_1077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1078_: *mut LeanObject = core::ptr::null_mut();
    v_res_1078_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(
        v_goal_1069_,
        v___f_1070_,
        v___y_1071_,
        v___y_1072_,
        v___y_1073_,
        v___y_1074_,
        v___y_1075_,
        v___y_1076_,
    );
    lean_dec(v___y_1076_);
    lean_dec_ref(v___y_1075_);
    lean_dec(v___y_1074_);
    lean_dec_ref(v___y_1073_);
    lean_dec(v___y_1072_);
    lean_dec_ref(v___y_1071_);
    return v_res_1078_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__2(
    mut v___f_1079_: *mut LeanObject,
    mut v_goal_1080_: *mut LeanObject,
    mut v___y_1081_: *mut LeanObject,
    mut v___y_1082_: *mut LeanObject,
    mut v___y_1083_: *mut LeanObject,
    mut v___y_1084_: *mut LeanObject,
    mut v___y_1085_: *mut LeanObject,
    mut v___y_1086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_goal_1080_);
    v___f_1088_ = lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___boxed
            as *mut core::ffi::c_void,
        9,
        2,
    );
    lean_closure_set(v___f_1088_, 0, v_goal_1080_);
    lean_closure_set(v___f_1088_, 1, v___f_1079_);
    v___x_1089_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_goal_1080_, v___f_1088_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
    return v___x_1089_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__2___boxed(
    mut v___f_1090_: *mut LeanObject,
    mut v_goal_1091_: *mut LeanObject,
    mut v___y_1092_: *mut LeanObject,
    mut v___y_1093_: *mut LeanObject,
    mut v___y_1094_: *mut LeanObject,
    mut v___y_1095_: *mut LeanObject,
    mut v___y_1096_: *mut LeanObject,
    mut v___y_1097_: *mut LeanObject,
    mut v___y_1098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1099_: *mut LeanObject = core::ptr::null_mut();
    v_res_1099_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__2(
        v___f_1090_,
        v_goal_1091_,
        v___y_1092_,
        v___y_1093_,
        v___y_1094_,
        v___y_1095_,
        v___y_1096_,
        v___y_1097_,
    );
    lean_dec(v___y_1097_);
    lean_dec_ref(v___y_1096_);
    lean_dec(v___y_1095_);
    lean_dec_ref(v___y_1094_);
    lean_dec(v___y_1093_);
    lean_dec_ref(v___y_1092_);
    return v_res_1099_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0(
    mut v_00_u03b2_1110_: *mut LeanObject,
    mut v_m_1111_: *mut LeanObject,
    mut v_a_1112_: *mut LeanObject,
) -> u8 {
    let mut v___x_1113_: u8 = 0;
    v___x_1113_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg(v_m_1111_, v_a_1112_);
    return v___x_1113_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___boxed(
    mut v_00_u03b2_1114_: *mut LeanObject,
    mut v_m_1115_: *mut LeanObject,
    mut v_a_1116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1117_: u8 = 0;
    let mut v_r_1118_: *mut LeanObject = core::ptr::null_mut();
    v_res_1117_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0(v_00_u03b2_1114_, v_m_1115_, v_a_1116_);
    lean_dec_ref(v_a_1116_);
    lean_dec_ref(v_m_1115_);
    v_r_1118_ = lean_box((v_res_1117_) as usize);
    return v_r_1118_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1(
    mut v_00_u03b2_1119_: *mut LeanObject,
    mut v_m_1120_: *mut LeanObject,
    mut v_a_1121_: *mut LeanObject,
    mut v_b_1122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_m_1120_, v_a_1121_, v_b_1122_);
    return v___x_1123_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(
    mut v_as_1124_: *mut LeanObject,
    mut v_sz_1125_: usize,
    mut v_i_1126_: usize,
    mut v_b_1127_: *mut LeanObject,
    mut v___y_1128_: *mut LeanObject,
    mut v___y_1129_: *mut LeanObject,
    mut v___y_1130_: *mut LeanObject,
    mut v___y_1131_: *mut LeanObject,
    mut v___y_1132_: *mut LeanObject,
    mut v___y_1133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    v___x_1135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v_as_1124_, v_sz_1125_, v_i_1126_, v_b_1127_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
    return v___x_1135_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___boxed(
    mut v_as_1136_: *mut LeanObject,
    mut v_sz_1137_: *mut LeanObject,
    mut v_i_1138_: *mut LeanObject,
    mut v_b_1139_: *mut LeanObject,
    mut v___y_1140_: *mut LeanObject,
    mut v___y_1141_: *mut LeanObject,
    mut v___y_1142_: *mut LeanObject,
    mut v___y_1143_: *mut LeanObject,
    mut v___y_1144_: *mut LeanObject,
    mut v___y_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1147_: usize = 0;
    let mut v_i_boxed_1148_: usize = 0;
    let mut v_res_1149_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1147_ = lean_unbox_usize(v_sz_1137_);
    lean_dec(v_sz_1137_);
    v_i_boxed_1148_ = lean_unbox_usize(v_i_1138_);
    lean_dec(v_i_1138_);
    v_res_1149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(v_as_1136_, v_sz_boxed_1147_, v_i_boxed_1148_, v_b_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
    lean_dec(v___y_1145_);
    lean_dec_ref(v___y_1144_);
    lean_dec(v___y_1143_);
    lean_dec_ref(v___y_1142_);
    lean_dec(v___y_1141_);
    lean_dec_ref(v___y_1140_);
    lean_dec_ref(v_as_1136_);
    return v_res_1149_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0(
    mut v_00_u03b2_1150_: *mut LeanObject,
    mut v_a_1151_: *mut LeanObject,
    mut v_x_1152_: *mut LeanObject,
) -> u8 {
    let mut v___x_1153_: u8 = 0;
    v___x_1153_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg(v_a_1151_, v_x_1152_);
    return v___x_1153_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0___boxed(
    mut v_00_u03b2_1154_: *mut LeanObject,
    mut v_a_1155_: *mut LeanObject,
    mut v_x_1156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1157_: u8 = 0;
    let mut v_r_1158_: *mut LeanObject = core::ptr::null_mut();
    v_res_1157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0(v_00_u03b2_1154_, v_a_1155_, v_x_1156_);
    lean_dec(v_x_1156_);
    lean_dec_ref(v_a_1155_);
    v_r_1158_ = lean_box((v_res_1157_) as usize);
    return v_r_1158_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2(
    mut v_00_u03b2_1159_: *mut LeanObject,
    mut v_data_1160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2___redArg(v_data_1160_);
    return v___x_1161_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4(
    mut v_00_u03b2_1162_: *mut LeanObject,
    mut v_i_1163_: *mut LeanObject,
    mut v_source_1164_: *mut LeanObject,
    mut v_target_1165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    v___x_1166_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4___redArg(v_i_1163_, v_source_1164_, v_target_1165_);
    return v___x_1166_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b2_1167_: *mut LeanObject,
    mut v_x_1168_: *mut LeanObject,
    mut v_x_1169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    v___x_1170_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4_spec__6___redArg(v_x_1168_, v_x_1169_);
    return v___x_1170_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
}
