// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.EmbeddedConstraint
// Imports: Std.Tactic.BVDecide.Normalize.Bool Lean.Meta.Tactic.BVDecide.Normalize.Basic
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
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__3_value) as *mut crate::leanh::LeanObject,9255189395584251158 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__2_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__3_value:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        15708030456876490904 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__4_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__4_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg___lam__0(
    mut v_x_586_: *mut crate::leanh::LeanObject,
    mut v___y_587_: *mut crate::leanh::LeanObject,
    mut v___y_588_: *mut crate::leanh::LeanObject,
    mut v___y_589_: *mut crate::leanh::LeanObject,
    mut v___y_590_: *mut crate::leanh::LeanObject,
    mut v___y_591_: *mut crate::leanh::LeanObject,
    mut v___y_592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_588_);
    crate::leanh::lean_inc_ref(v___y_587_);
    v___x_594_ = crate::leanh::lean_apply_7(
        v_x_586_,
        v___y_587_,
        v___y_588_,
        v___y_589_,
        v___y_590_,
        v___y_591_,
        v___y_592_,
        crate::leanh::lean_box(0),
    );
    return v___x_594_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg___lam__0___boxed(
    mut v_x_595_: *mut crate::leanh::LeanObject,
    mut v___y_596_: *mut crate::leanh::LeanObject,
    mut v___y_597_: *mut crate::leanh::LeanObject,
    mut v___y_598_: *mut crate::leanh::LeanObject,
    mut v___y_599_: *mut crate::leanh::LeanObject,
    mut v___y_600_: *mut crate::leanh::LeanObject,
    mut v___y_601_: *mut crate::leanh::LeanObject,
    mut v___y_602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_603_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg___lam__0(v_x_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
    crate::leanh::lean_dec(v___y_597_);
    crate::leanh::lean_dec_ref(v___y_596_);
    return v_res_603_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(
    mut v_mvarId_604_: *mut crate::leanh::LeanObject,
    mut v_x_605_: *mut crate::leanh::LeanObject,
    mut v___y_606_: *mut crate::leanh::LeanObject,
    mut v___y_607_: *mut crate::leanh::LeanObject,
    mut v___y_608_: *mut crate::leanh::LeanObject,
    mut v___y_609_: *mut crate::leanh::LeanObject,
    mut v___y_610_: *mut crate::leanh::LeanObject,
    mut v___y_611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_618_: u8 = 0;
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_622_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_607_);
                crate::leanh::lean_inc_ref(v___y_606_);
                v___f_613_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                crate::leanh::lean_closure_set(v___f_613_, 0, v_x_605_);
                crate::leanh::lean_closure_set(v___f_613_, 1, v___y_606_);
                crate::leanh::lean_closure_set(v___f_613_, 2, v___y_607_);
                v___x_614_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_604_,
                    v___f_613_,
                    v___y_608_,
                    v___y_609_,
                    v___y_610_,
                    v___y_611_,
                );
                if crate::leanh::lean_obj_tag(v___x_614_) == 0 {
                    return v___x_614_;
                } else {
                    v_a_615_ = crate::leanh::lean_ctor_get(v___x_614_, 0);
                    v_isSharedCheck_622_ = (!crate::leanh::lean_is_exclusive(v___x_614_)) as u8;
                    if v_isSharedCheck_622_ == 0 {
                        v___x_617_ = v___x_614_;
                        v_isShared_618_ = v_isSharedCheck_622_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_615_);
                        crate::leanh::lean_dec(v___x_614_);
                        v___x_617_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_621_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
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
    mut v_mvarId_623_: *mut crate::leanh::LeanObject,
    mut v_x_624_: *mut crate::leanh::LeanObject,
    mut v___y_625_: *mut crate::leanh::LeanObject,
    mut v___y_626_: *mut crate::leanh::LeanObject,
    mut v___y_627_: *mut crate::leanh::LeanObject,
    mut v___y_628_: *mut crate::leanh::LeanObject,
    mut v___y_629_: *mut crate::leanh::LeanObject,
    mut v___y_630_: *mut crate::leanh::LeanObject,
    mut v___y_631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_632_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_mvarId_623_, v_x_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
    crate::leanh::lean_dec(v___y_630_);
    crate::leanh::lean_dec_ref(v___y_629_);
    crate::leanh::lean_dec(v___y_628_);
    crate::leanh::lean_dec_ref(v___y_627_);
    crate::leanh::lean_dec(v___y_626_);
    crate::leanh::lean_dec_ref(v___y_625_);
    return v_res_632_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(
    mut v_00_u03b1_633_: *mut crate::leanh::LeanObject,
    mut v_mvarId_634_: *mut crate::leanh::LeanObject,
    mut v_x_635_: *mut crate::leanh::LeanObject,
    mut v___y_636_: *mut crate::leanh::LeanObject,
    mut v___y_637_: *mut crate::leanh::LeanObject,
    mut v___y_638_: *mut crate::leanh::LeanObject,
    mut v___y_639_: *mut crate::leanh::LeanObject,
    mut v___y_640_: *mut crate::leanh::LeanObject,
    mut v___y_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_643_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_mvarId_634_, v_x_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
    return v___x_643_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___boxed(
    mut v_00_u03b1_644_: *mut crate::leanh::LeanObject,
    mut v_mvarId_645_: *mut crate::leanh::LeanObject,
    mut v_x_646_: *mut crate::leanh::LeanObject,
    mut v___y_647_: *mut crate::leanh::LeanObject,
    mut v___y_648_: *mut crate::leanh::LeanObject,
    mut v___y_649_: *mut crate::leanh::LeanObject,
    mut v___y_650_: *mut crate::leanh::LeanObject,
    mut v___y_651_: *mut crate::leanh::LeanObject,
    mut v___y_652_: *mut crate::leanh::LeanObject,
    mut v___y_653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_654_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(v_00_u03b1_644_, v_mvarId_645_, v_x_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
    crate::leanh::lean_dec(v___y_652_);
    crate::leanh::lean_dec_ref(v___y_651_);
    crate::leanh::lean_dec(v___y_650_);
    crate::leanh::lean_dec_ref(v___y_649_);
    crate::leanh::lean_dec(v___y_648_);
    crate::leanh::lean_dec_ref(v___y_647_);
    return v_res_654_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(
    mut v___y_655_: *mut crate::leanh::LeanObject,
    mut v___y_656_: *mut crate::leanh::LeanObject,
    mut v___y_657_: *mut crate::leanh::LeanObject,
    mut v___y_658_: *mut crate::leanh::LeanObject,
    mut v___y_659_: *mut crate::leanh::LeanObject,
    mut v___y_660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_662_ = l_Lean_Meta_getPropHyps(v___y_657_, v___y_658_, v___y_659_, v___y_660_);
    return v___x_662_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___boxed(
    mut v___y_663_: *mut crate::leanh::LeanObject,
    mut v___y_664_: *mut crate::leanh::LeanObject,
    mut v___y_665_: *mut crate::leanh::LeanObject,
    mut v___y_666_: *mut crate::leanh::LeanObject,
    mut v___y_667_: *mut crate::leanh::LeanObject,
    mut v___y_668_: *mut crate::leanh::LeanObject,
    mut v___y_669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_670_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(
        v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_,
    );
    crate::leanh::lean_dec(v___y_668_);
    crate::leanh::lean_dec_ref(v___y_667_);
    crate::leanh::lean_dec(v___y_666_);
    crate::leanh::lean_dec_ref(v___y_665_);
    crate::leanh::lean_dec(v___y_664_);
    crate::leanh::lean_dec_ref(v___y_663_);
    return v_res_670_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_x_671_: *mut crate::leanh::LeanObject,
    mut v_x_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_678_: u8 = 0;
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_698_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_672_) == 0 {
                    return v_x_671_;
                } else {
                    v_key_673_ = crate::leanh::lean_ctor_get(v_x_672_, 0);
                    v_value_674_ = crate::leanh::lean_ctor_get(v_x_672_, 1);
                    v_tail_675_ = crate::leanh::lean_ctor_get(v_x_672_, 2);
                    v_isSharedCheck_698_ = (!crate::leanh::lean_is_exclusive(v_x_672_)) as u8;
                    if v_isSharedCheck_698_ == 0 {
                        v___x_677_ = v_x_672_;
                        v_isShared_678_ = v_isSharedCheck_698_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_675_);
                        crate::leanh::lean_inc(v_value_674_);
                        crate::leanh::lean_inc(v_key_673_);
                        crate::leanh::lean_dec(v_x_672_);
                        v___x_677_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_inc(v___x_692_);
                if v_isShared_678_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_677_, 2, v___x_692_);
                    v___x_694_ = v___x_677_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_697_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_697_, 0, v_key_673_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_697_, 1, v_value_674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_697_, 2, v___x_692_);
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
    mut v_i_699_: *mut crate::leanh::LeanObject,
    mut v_source_700_: *mut crate::leanh::LeanObject,
    mut v_target_701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: u8 = 0;
    let mut v_es_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_702_ = lean_array_get_size(v_source_700_);
                v___x_703_ = lean_nat_dec_lt(v_i_699_, v___x_702_);
                if v___x_703_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_700_);
                    crate::leanh::lean_dec(v_i_699_);
                    return v_target_701_;
                } else {
                    v_es_704_ = lean_array_fget(v_source_700_, v_i_699_);
                    v___x_705_ = crate::leanh::lean_box(0);
                    v_source_706_ = lean_array_fset(v_source_700_, v_i_699_, v___x_705_);
                    v_target_707_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4_spec__6___redArg(v_target_701_, v_es_704_);
                    v___x_708_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_709_ = lean_nat_add(v_i_699_, v___x_708_);
                    crate::leanh::lean_dec(v_i_699_);
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
    mut v_data_711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_712_ = lean_array_get_size(v_data_711_);
    v___x_713_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_714_ = lean_nat_mul(v___x_712_, v___x_713_);
    v___x_715_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_716_ = crate::leanh::lean_box(0);
    v___x_717_ = lean_mk_array(v_nbuckets_714_, v___x_716_);
    v___x_718_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4___redArg(v___x_715_, v_data_711_, v___x_717_);
    return v___x_718_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg(
    mut v_a_719_: *mut crate::leanh::LeanObject,
    mut v_x_720_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_721_: u8 = 0;
    let mut v_key_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_720_) == 0 {
                    v___x_721_ = 0;
                    return v___x_721_;
                } else {
                    v_key_722_ = crate::leanh::lean_ctor_get(v_x_720_, 0);
                    v_tail_723_ = crate::leanh::lean_ctor_get(v_x_720_, 2);
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
    mut v_a_726_: *mut crate::leanh::LeanObject,
    mut v_x_727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_728_: u8 = 0;
    let mut v_r_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_728_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg(v_a_726_, v_x_727_);
    crate::leanh::lean_dec(v_x_727_);
    crate::leanh::lean_dec_ref(v_a_726_);
    v_r_729_ = crate::leanh::lean_box((v_res_728_) as usize);
    return v_r_729_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(
    mut v_m_730_: *mut crate::leanh::LeanObject,
    mut v_a_731_: *mut crate::leanh::LeanObject,
    mut v_b_732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: u8 = 0;
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_752_: u8 = 0;
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: u8 = 0;
    let mut v_val_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_770_: u8 = 0;
    let mut v_unused_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_733_ = crate::leanh::lean_ctor_get(v_m_730_, 0);
                v_buckets_734_ = crate::leanh::lean_ctor_get(v_m_730_, 1);
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
                    crate::leanh::lean_inc_ref(v_buckets_734_);
                    crate::leanh::lean_inc(v_size_733_);
                    v_isSharedCheck_770_ = (!crate::leanh::lean_is_exclusive(v_m_730_)) as u8;
                    if v_isSharedCheck_770_ == 0 {
                        v_unused_771_ = crate::leanh::lean_ctor_get(v_m_730_, 1);
                        crate::leanh::lean_dec(v_unused_771_);
                        v_unused_772_ = crate::leanh::lean_ctor_get(v_m_730_, 0);
                        crate::leanh::lean_dec(v_unused_772_);
                        v___x_751_ = v_m_730_;
                        v_isShared_752_ = v_isSharedCheck_770_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_730_);
                        v___x_751_ = crate::leanh::lean_box(0);
                        v_isShared_752_ = v_isSharedCheck_770_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_732_);
                    crate::leanh::lean_dec_ref(v_a_731_);
                    return v_m_730_;
                }
            }
            1 => {
                v___x_753_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_754_ = lean_nat_add(v_size_733_, v___x_753_);
                crate::leanh::lean_dec(v_size_733_);
                crate::leanh::lean_inc(v_bkt_748_);
                v___x_755_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_755_, 0, v_a_731_);
                crate::leanh::lean_ctor_set(v___x_755_, 1, v_b_732_);
                crate::leanh::lean_ctor_set(v___x_755_, 2, v_bkt_748_);
                v_buckets_x27_756_ = lean_array_uset(v_buckets_734_, v___x_747_, v___x_755_);
                v___x_757_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_758_ = lean_nat_mul(v_size_x27_754_, v___x_757_);
                v___x_759_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_760_ = lean_nat_div(v___x_758_, v___x_759_);
                crate::leanh::lean_dec(v___x_758_);
                v___x_761_ = lean_array_get_size(v_buckets_x27_756_);
                v___x_762_ = lean_nat_dec_le(v___x_760_, v___x_761_);
                crate::leanh::lean_dec(v___x_760_);
                if v___x_762_ == 0 {
                    v_val_763_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2___redArg(v_buckets_x27_756_);
                    if v_isShared_752_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_751_, 1, v_val_763_);
                        crate::leanh::lean_ctor_set(v___x_751_, 0, v_size_x27_754_);
                        v___x_765_ = v___x_751_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_766_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_766_, 0, v_size_x27_754_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_766_, 1, v_val_763_);
                        v___x_765_ = v_reuseFailAlloc_766_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_752_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_751_, 1, v_buckets_x27_756_);
                        crate::leanh::lean_ctor_set(v___x_751_, 0, v_size_x27_754_);
                        v___x_768_ = v___x_751_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_769_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_769_, 0, v_size_x27_754_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_769_, 1, v_buckets_x27_756_);
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
    mut v_m_773_: *mut crate::leanh::LeanObject,
    mut v_a_774_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: u8 = 0;
    v_buckets_775_ = crate::leanh::lean_ctor_get(v_m_773_, 1);
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
    mut v_m_791_: *mut crate::leanh::LeanObject,
    mut v_a_792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_793_: u8 = 0;
    let mut v_r_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_793_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg(v_m_791_, v_a_792_);
    crate::leanh::lean_dec_ref(v_a_792_);
    crate::leanh::lean_dec_ref(v_m_791_);
    v_r_794_ = crate::leanh::lean_box((v_res_793_) as usize);
    return v_r_794_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(
    mut v_as_803_: *mut crate::leanh::LeanObject,
    mut v_sz_804_: usize,
    mut v_i_805_: usize,
    mut v_b_806_: *mut crate::leanh::LeanObject,
    mut v___y_807_: *mut crate::leanh::LeanObject,
    mut v___y_808_: *mut crate::leanh::LeanObject,
    mut v___y_809_: *mut crate::leanh::LeanObject,
    mut v___y_810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: usize = 0;
    let mut v___x_815_: usize = 0;
    let mut v___x_817_: u8 = 0;
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v_fst_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_831_: u8 = 0;
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: u8 = 0;
    let mut v_arg_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: u8 = 0;
    let mut v_arg_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: u8 = 0;
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: u8 = 0;
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: u8 = 0;
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: u8 = 0;
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_870_: u8 = 0;
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut v_a_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_878_: u8 = 0;
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_882_: u8 = 0;
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_886_: u8 = 0;
    let mut v_isSharedCheck_887_: u8 = 0;
    let mut v_unused_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_892_: u8 = 0;
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_817_ = lean_usize_dec_lt(v_i_805_, v_sz_804_);
                if v___x_817_ == 0 {
                    v___x_818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_818_, 0, v_b_806_);
                    return v___x_818_;
                } else {
                    v_a_819_ = lean_array_uget_borrowed(v_as_803_, v_i_805_);
                    crate::leanh::lean_inc(v_a_819_);
                    v___x_820_ = l_Lean_FVarId_getType___redArg(
                        v_a_819_, v___y_807_, v___y_809_, v___y_810_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_820_) == 0 {
                        v_snd_821_ = crate::leanh::lean_ctor_get(v_b_806_, 1);
                        crate::leanh::lean_inc(v_snd_821_);
                        v_a_822_ = crate::leanh::lean_ctor_get(v___x_820_, 0);
                        crate::leanh::lean_inc(v_a_822_);
                        crate::leanh::lean_dec_ref_known(v___x_820_, 1);
                        v_fst_823_ = crate::leanh::lean_ctor_get(v_b_806_, 0);
                        v_isSharedCheck_887_ = (!crate::leanh::lean_is_exclusive(v_b_806_)) as u8;
                        if v_isSharedCheck_887_ == 0 {
                            v_unused_888_ = crate::leanh::lean_ctor_get(v_b_806_, 1);
                            crate::leanh::lean_dec(v_unused_888_);
                            v___x_825_ = v_b_806_;
                            v_isShared_826_ = v_isSharedCheck_887_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fst_823_);
                            crate::leanh::lean_dec(v_b_806_);
                            v___x_825_ = crate::leanh::lean_box(0);
                            v_isShared_826_ = v_isSharedCheck_887_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_806_);
                        v_a_889_ = crate::leanh::lean_ctor_get(v___x_820_, 0);
                        v_isSharedCheck_896_ = (!crate::leanh::lean_is_exclusive(v___x_820_)) as u8;
                        if v_isSharedCheck_896_ == 0 {
                            v___x_891_ = v___x_820_;
                            v_isShared_892_ = v_isSharedCheck_896_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_889_);
                            crate::leanh::lean_dec(v___x_820_);
                            v___x_891_ = crate::leanh::lean_box(0);
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
                v_fst_827_ = crate::leanh::lean_ctor_get(v_snd_821_, 0);
                v_snd_828_ = crate::leanh::lean_ctor_get(v_snd_821_, 1);
                v_isSharedCheck_886_ = (!crate::leanh::lean_is_exclusive(v_snd_821_)) as u8;
                if v_isSharedCheck_886_ == 0 {
                    v___x_830_ = v_snd_821_;
                    v_isShared_831_ = v_isSharedCheck_886_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_828_);
                    crate::leanh::lean_inc(v_fst_827_);
                    crate::leanh::lean_dec(v_snd_821_);
                    v___x_830_ = crate::leanh::lean_box(0);
                    v_isShared_831_ = v_isSharedCheck_886_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_839_ = l_Lean_Expr_cleanupAnnotations(v_a_822_);
                v___x_840_ = l_Lean_Expr_isApp(v___x_839_);
                if v___x_840_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_839_);
                    state = 4;
                    continue;
                } else {
                    v_arg_841_ = crate::leanh::lean_ctor_get(v___x_839_, 1);
                    crate::leanh::lean_inc_ref(v_arg_841_);
                    v___x_842_ = l_Lean_Expr_appFnCleanup___redArg(v___x_839_);
                    v___x_843_ = l_Lean_Expr_isApp(v___x_842_);
                    if v___x_843_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_842_);
                        crate::leanh::lean_dec_ref(v_arg_841_);
                        state = 4;
                        continue;
                    } else {
                        v_arg_844_ = crate::leanh::lean_ctor_get(v___x_842_, 1);
                        crate::leanh::lean_inc_ref(v_arg_844_);
                        v___x_845_ = l_Lean_Expr_appFnCleanup___redArg(v___x_842_);
                        v___x_846_ = l_Lean_Expr_isApp(v___x_845_);
                        if v___x_846_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_845_);
                            crate::leanh::lean_dec_ref(v_arg_844_);
                            crate::leanh::lean_dec_ref(v_arg_841_);
                            state = 4;
                            continue;
                        } else {
                            v___x_847_ = l_Lean_Expr_appFnCleanup___redArg(v___x_845_);
                            v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__1;
                            v___x_849_ = l_Lean_Expr_isConstOf(v___x_847_, v___x_848_);
                            crate::leanh::lean_dec_ref(v___x_847_);
                            if v___x_849_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_844_);
                                crate::leanh::lean_dec_ref(v_arg_841_);
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_830_);
                                crate::leanh::lean_del_object(v___x_825_);
                                v___x_850_ = l_Lean_Expr_cleanupAnnotations(v_arg_841_);
                                v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4;
                                v___x_852_ = l_Lean_Expr_isConstOf(v___x_850_, v___x_851_);
                                crate::leanh::lean_dec_ref(v___x_850_);
                                if v___x_852_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_844_);
                                    v___x_853_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_853_, 0, v_fst_827_);
                                    crate::leanh::lean_ctor_set(v___x_853_, 1, v_snd_828_);
                                    v___x_854_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_854_, 0, v_fst_823_);
                                    crate::leanh::lean_ctor_set(v___x_854_, 1, v___x_853_);
                                    v_a_813_ = v___x_854_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_855_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg(v_fst_827_, v_arg_844_);
                                    if v___x_855_ == 0 {
                                        crate::leanh::lean_inc(v_a_819_);
                                        v___x_856_ = l_Lean_FVarId_getDecl___redArg(
                                            v_a_819_, v___y_807_, v___y_809_, v___y_810_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_856_) == 0 {
                                            v_a_857_ = crate::leanh::lean_ctor_get(v___x_856_, 0);
                                            crate::leanh::lean_inc(v_a_857_);
                                            crate::leanh::lean_dec_ref_known(v___x_856_, 1);
                                            v___x_858_ = l_Lean_LocalDecl_toExpr(v_a_857_);
                                            crate::leanh::lean_inc(v_a_819_);
                                            v___x_859_ =
                                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_859_, 0, v_a_819_);
                                            v___x_860_ = l_Lean_Meta_simpGlobalConfig;
                                            v___x_861_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(
                                                v_fst_823_, v___x_859_, v___x_858_, v___x_860_,
                                                v___y_807_, v___y_808_, v___y_809_, v___y_810_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_861_) == 0 {
                                                v_a_862_ =
                                                    crate::leanh::lean_ctor_get(v___x_861_, 0);
                                                crate::leanh::lean_inc(v_a_862_);
                                                crate::leanh::lean_dec_ref_known(v___x_861_, 1);
                                                v___x_863_ = crate::leanh::lean_box(0);
                                                v___x_864_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_fst_827_, v_arg_844_, v___x_863_);
                                                v___x_865_ =
                                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_865_, 0, v___x_864_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_865_, 1, v_snd_828_,
                                                );
                                                v___x_866_ =
                                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_866_, 0, v_a_862_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_866_, 1, v___x_865_,
                                                );
                                                v_a_813_ = v___x_866_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref(v_arg_844_);
                                                crate::leanh::lean_dec(v_snd_828_);
                                                crate::leanh::lean_dec(v_fst_827_);
                                                v_a_867_ =
                                                    crate::leanh::lean_ctor_get(v___x_861_, 0);
                                                v_isSharedCheck_874_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_861_))
                                                        as u8;
                                                if v_isSharedCheck_874_ == 0 {
                                                    v___x_869_ = v___x_861_;
                                                    v_isShared_870_ = v_isSharedCheck_874_;
                                                    state = 7;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_867_);
                                                    crate::leanh::lean_dec(v___x_861_);
                                                    v___x_869_ = crate::leanh::lean_box(0);
                                                    v_isShared_870_ = v_isSharedCheck_874_;
                                                    state = 7;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_arg_844_);
                                            crate::leanh::lean_dec(v_snd_828_);
                                            crate::leanh::lean_dec(v_fst_827_);
                                            crate::leanh::lean_dec(v_fst_823_);
                                            v_a_875_ = crate::leanh::lean_ctor_get(v___x_856_, 0);
                                            v_isSharedCheck_882_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_856_))
                                                    as u8;
                                            if v_isSharedCheck_882_ == 0 {
                                                v___x_877_ = v___x_856_;
                                                v_isShared_878_ = v_isSharedCheck_882_;
                                                state = 9;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_875_);
                                                crate::leanh::lean_dec(v___x_856_);
                                                v___x_877_ = crate::leanh::lean_box(0);
                                                v_isShared_878_ = v_isSharedCheck_882_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_arg_844_);
                                        crate::leanh::lean_inc(v_a_819_);
                                        v___x_883_ = lean_array_push(v_snd_828_, v_a_819_);
                                        v___x_884_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_884_, 0, v_fst_827_);
                                        crate::leanh::lean_ctor_set(v___x_884_, 1, v___x_883_);
                                        v___x_885_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_885_, 0, v_fst_823_);
                                        crate::leanh::lean_ctor_set(v___x_885_, 1, v___x_884_);
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
                    v_reuseFailAlloc_838_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_838_, 0, v_fst_827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_838_, 1, v_snd_828_);
                    v___x_834_ = v_reuseFailAlloc_838_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_826_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_825_, 1, v___x_834_);
                    v___x_836_ = v___x_825_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_837_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_837_, 0, v_fst_823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_837_, 1, v___x_834_);
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
                    v_reuseFailAlloc_873_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
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
                    v_reuseFailAlloc_881_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
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
                    v_reuseFailAlloc_895_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
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
    mut v_as_897_: *mut crate::leanh::LeanObject,
    mut v_sz_898_: *mut crate::leanh::LeanObject,
    mut v_i_899_: *mut crate::leanh::LeanObject,
    mut v_b_900_: *mut crate::leanh::LeanObject,
    mut v___y_901_: *mut crate::leanh::LeanObject,
    mut v___y_902_: *mut crate::leanh::LeanObject,
    mut v___y_903_: *mut crate::leanh::LeanObject,
    mut v___y_904_: *mut crate::leanh::LeanObject,
    mut v___y_905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_906_: usize = 0;
    let mut v_i_boxed_907_: usize = 0;
    let mut v_res_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_906_ = crate::leanh::lean_unbox_usize(v_sz_898_);
    crate::leanh::lean_dec(v_sz_898_);
    v_i_boxed_907_ = crate::leanh::lean_unbox_usize(v_i_899_);
    crate::leanh::lean_dec(v_i_899_);
    v_res_908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v_as_897_, v_sz_boxed_906_, v_i_boxed_907_, v_b_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
    crate::leanh::lean_dec(v___y_904_);
    crate::leanh::lean_dec_ref(v___y_903_);
    crate::leanh::lean_dec(v___y_902_);
    crate::leanh::lean_dec_ref(v___y_901_);
    crate::leanh::lean_dec_ref(v_as_897_);
    return v_res_908_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_911_ = crate::leanh::lean_box(0);
    v___x_912_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_913_ = lean_mk_array(v___x_912_, v___x_911_);
    return v___x_913_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seen_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_914_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__1,
    );
    v___x_915_ = crate::leanh::lean_unsigned_to_nat(0);
    v_seen_916_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_seen_916_, 0, v___x_915_);
    crate::leanh::lean_ctor_set(v_seen_916_, 1, v___x_914_);
    return v_seen_916_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v_relevantHyps_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seen_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_relevantHyps_917_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__0;
    v_seen_918_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__2,
    );
    v___x_919_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_919_, 0, v_seen_918_);
    crate::leanh::lean_ctor_set(v___x_919_, 1, v_relevantHyps_917_);
    return v___x_919_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_920_ = crate::leanh::lean_obj_once(
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
    v___x_922_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_922_, 0, v_relevantHyps_921_);
    crate::leanh::lean_ctor_set(v___x_922_, 1, v___x_920_);
    return v___x_922_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_923_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_923_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__5_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__5,
    );
    v___x_925_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_925_, 0, v___x_924_);
    return v___x_925_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_926_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_927_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6,
    );
    v___x_928_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_928_, 0, v___x_927_);
    crate::leanh::lean_ctor_set(v___x_928_, 1, v___x_926_);
    return v___x_928_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_929_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_930_ = lean_mk_empty_array_with_capacity(v___x_929_);
    v___x_931_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_931_, 0, v___x_930_);
    return v___x_931_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_932_: usize = 0;
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_932_ = 5usize;
    v___x_933_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_934_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_935_ = lean_mk_empty_array_with_capacity(v___x_934_);
    v___x_936_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__8_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__8,
    );
    v___x_937_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_937_, 0, v___x_936_);
    crate::leanh::lean_ctor_set(v___x_937_, 1, v___x_935_);
    crate::leanh::lean_ctor_set(v___x_937_, 2, v___x_933_);
    crate::leanh::lean_ctor_set(v___x_937_, 3, v___x_933_);
    crate::leanh::lean_ctor_set_usize(v___x_937_, 4, v___x_932_);
    return v___x_937_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_938_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__9_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__9,
    );
    v___x_939_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__6,
    );
    v___x_940_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_940_, 0, v___x_939_);
    crate::leanh::lean_ctor_set(v___x_940_, 1, v___x_939_);
    crate::leanh::lean_ctor_set(v___x_940_, 2, v___x_939_);
    crate::leanh::lean_ctor_set(v___x_940_, 3, v___x_938_);
    return v___x_940_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_941_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__10_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__10,
    );
    v___x_942_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__7_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__7,
    );
    v___x_943_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_943_, 0, v___x_942_);
    crate::leanh::lean_ctor_set(v___x_943_, 1, v___x_941_);
    return v___x_943_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(
    mut v_goal_944_: *mut crate::leanh::LeanObject,
    mut v___f_945_: *mut crate::leanh::LeanObject,
    mut v___y_946_: *mut crate::leanh::LeanObject,
    mut v___y_947_: *mut crate::leanh::LeanObject,
    mut v___y_948_: *mut crate::leanh::LeanObject,
    mut v___y_949_: *mut crate::leanh::LeanObject,
    mut v___y_950_: *mut crate::leanh::LeanObject,
    mut v___y_951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_958_: usize = 0;
    let mut v___x_959_: usize = 0;
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_969_: u8 = 0;
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: u8 = 0;
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxSteps_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: u8 = 0;
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: u8 = 0;
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v_fst_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v_snd_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1003_: u8 = 0;
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1007_: u8 = 0;
    let mut v_a_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1011_: u8 = 0;
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1015_: u8 = 0;
    let mut v_a_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1019_: u8 = 0;
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1023_: u8 = 0;
    let mut v_a_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1027_: u8 = 0;
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1031_: u8 = 0;
    let mut v_a_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1035_: u8 = 0;
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1039_: u8 = 0;
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1044_: u8 = 0;
    let mut v_a_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1048_: u8 = 0;
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1052_: u8 = 0;
    let mut v_a_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1056_: u8 = 0;
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut v_a_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1064_: u8 = 0;
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_953_ =
                    l_Lean_Meta_getPropHyps(v___y_948_, v___y_949_, v___y_950_, v___y_951_);
                if crate::leanh::lean_obj_tag(v___x_953_) == 0 {
                    v_a_954_ = crate::leanh::lean_ctor_get(v___x_953_, 0);
                    crate::leanh::lean_inc(v_a_954_);
                    crate::leanh::lean_dec_ref_known(v___x_953_, 1);
                    v___x_955_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_relevantHyps_956_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__0;
                    v___x_957_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__4_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__4);
                    v_sz_958_ = lean_array_size(v_a_954_);
                    v___x_959_ = 0usize;
                    v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v_a_954_, v_sz_958_, v___x_959_, v___x_957_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
                    crate::leanh::lean_dec(v_a_954_);
                    if crate::leanh::lean_obj_tag(v___x_960_) == 0 {
                        v_a_961_ = crate::leanh::lean_ctor_get(v___x_960_, 0);
                        crate::leanh::lean_inc(v_a_961_);
                        crate::leanh::lean_dec_ref_known(v___x_960_, 1);
                        v_snd_962_ = crate::leanh::lean_ctor_get(v_a_961_, 1);
                        crate::leanh::lean_inc(v_snd_962_);
                        v_fst_963_ = crate::leanh::lean_ctor_get(v_a_961_, 0);
                        crate::leanh::lean_inc(v_fst_963_);
                        crate::leanh::lean_dec(v_a_961_);
                        v_snd_964_ = crate::leanh::lean_ctor_get(v_snd_962_, 1);
                        crate::leanh::lean_inc(v_snd_964_);
                        crate::leanh::lean_dec(v_snd_962_);
                        v___x_965_ = l_Lean_MVarId_tryClearMany(
                            v_goal_944_,
                            v_snd_964_,
                            v___y_948_,
                            v___y_949_,
                            v___y_950_,
                            v___y_951_,
                        );
                        crate::leanh::lean_dec(v_snd_964_);
                        if crate::leanh::lean_obj_tag(v___x_965_) == 0 {
                            v_a_966_ = crate::leanh::lean_ctor_get(v___x_965_, 0);
                            v_isSharedCheck_1044_ =
                                (!crate::leanh::lean_is_exclusive(v___x_965_)) as u8;
                            if v_isSharedCheck_1044_ == 0 {
                                v___x_968_ = v___x_965_;
                                v_isShared_969_ = v_isSharedCheck_1044_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_966_);
                                crate::leanh::lean_dec(v___x_965_);
                                v___x_968_ = crate::leanh::lean_box(0);
                                v_isShared_969_ = v_isSharedCheck_1044_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_963_);
                            crate::leanh::lean_dec_ref(v___f_945_);
                            v_a_1045_ = crate::leanh::lean_ctor_get(v___x_965_, 0);
                            v_isSharedCheck_1052_ =
                                (!crate::leanh::lean_is_exclusive(v___x_965_)) as u8;
                            if v_isSharedCheck_1052_ == 0 {
                                v___x_1047_ = v___x_965_;
                                v_isShared_1048_ = v_isSharedCheck_1052_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1045_);
                                crate::leanh::lean_dec(v___x_965_);
                                v___x_1047_ = crate::leanh::lean_box(0);
                                v_isShared_1048_ = v_isSharedCheck_1052_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___f_945_);
                        crate::leanh::lean_dec(v_goal_944_);
                        v_a_1053_ = crate::leanh::lean_ctor_get(v___x_960_, 0);
                        v_isSharedCheck_1060_ =
                            (!crate::leanh::lean_is_exclusive(v___x_960_)) as u8;
                        if v_isSharedCheck_1060_ == 0 {
                            v___x_1055_ = v___x_960_;
                            v_isShared_1056_ = v_isSharedCheck_1060_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1053_);
                            crate::leanh::lean_dec(v___x_960_);
                            v___x_1055_ = crate::leanh::lean_box(0);
                            v_isShared_1056_ = v_isSharedCheck_1060_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_945_);
                    crate::leanh::lean_dec(v_goal_944_);
                    v_a_1061_ = crate::leanh::lean_ctor_get(v___x_953_, 0);
                    v_isSharedCheck_1068_ = (!crate::leanh::lean_is_exclusive(v___x_953_)) as u8;
                    if v_isSharedCheck_1068_ == 0 {
                        v___x_1063_ = v___x_953_;
                        v_isShared_1064_ = v_isSharedCheck_1068_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1061_);
                        crate::leanh::lean_dec(v___x_953_);
                        v___x_1063_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_del_object(v___x_968_);
                    crate::leanh::lean_inc(v_a_966_);
                    v___x_972_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_a_966_, v___f_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
                    if crate::leanh::lean_obj_tag(v___x_972_) == 0 {
                        v_a_973_ = crate::leanh::lean_ctor_get(v___x_972_, 0);
                        crate::leanh::lean_inc(v_a_973_);
                        crate::leanh::lean_dec_ref_known(v___x_972_, 1);
                        v___x_974_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_951_);
                        if crate::leanh::lean_obj_tag(v___x_974_) == 0 {
                            v_a_975_ = crate::leanh::lean_ctor_get(v___x_974_, 0);
                            crate::leanh::lean_inc(v_a_975_);
                            crate::leanh::lean_dec_ref_known(v___x_974_, 1);
                            v_maxSteps_976_ = crate::leanh::lean_ctor_get(v___y_946_, 1);
                            v___x_977_ = 1;
                            v___x_978_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_979_ = 0;
                            v___x_980_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v_maxSteps_976_);
                            v___x_981_ = crate::leanh::lean_alloc_ctor(0, 3, (29) as u32);
                            crate::leanh::lean_ctor_set(v___x_981_, 0, v_maxSteps_976_);
                            crate::leanh::lean_ctor_set(v___x_981_, 1, v___x_978_);
                            crate::leanh::lean_ctor_set(v___x_981_, 2, v___x_980_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                                v___x_971_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2)
                                    as u32,
                                v___x_971_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 5)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 6)
                                    as u32,
                                v___x_979_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 7)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 9)
                                    as u32,
                                v___x_971_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 10)
                                    as u32,
                                v___x_971_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 11)
                                    as u32,
                                v___x_971_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 12)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 13)
                                    as u32,
                                v___x_971_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 14)
                                    as u32,
                                v___x_971_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 15)
                                    as u32,
                                v___x_971_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16)
                                    as u32,
                                v___x_971_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 17)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 18)
                                    as u32,
                                v___x_971_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 19)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 20)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 21)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 22)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 23)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 24)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 25)
                                    as u32,
                                v___x_977_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 26)
                                    as u32,
                                v___x_971_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 27)
                                    as u32,
                                v___x_971_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_981_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 28)
                                    as u32,
                                v___x_977_,
                            );
                            v___x_982_ = l_Lean_Options_empty;
                            v___x_983_ = l_Lean_Meta_Simp_mkContext___redArg(
                                v___x_981_, v_fst_963_, v_a_975_, v___x_982_, v___y_948_,
                                v___y_950_, v___y_951_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_983_) == 0 {
                                v_a_984_ = crate::leanh::lean_ctor_get(v___x_983_, 0);
                                crate::leanh::lean_inc(v_a_984_);
                                crate::leanh::lean_dec_ref_known(v___x_983_, 1);
                                v___x_985_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__11), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__11_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___closed__11);
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
                                if crate::leanh::lean_obj_tag(v___x_986_) == 0 {
                                    v_a_987_ = crate::leanh::lean_ctor_get(v___x_986_, 0);
                                    v_isSharedCheck_1007_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_986_)) as u8;
                                    if v_isSharedCheck_1007_ == 0 {
                                        v___x_989_ = v___x_986_;
                                        v_isShared_990_ = v_isSharedCheck_1007_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_987_);
                                        crate::leanh::lean_dec(v___x_986_);
                                        v___x_989_ = crate::leanh::lean_box(0);
                                        v_isShared_990_ = v_isSharedCheck_1007_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_a_1008_ = crate::leanh::lean_ctor_get(v___x_986_, 0);
                                    v_isSharedCheck_1015_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_986_)) as u8;
                                    if v_isSharedCheck_1015_ == 0 {
                                        v___x_1010_ = v___x_986_;
                                        v_isShared_1011_ = v_isSharedCheck_1015_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1008_);
                                        crate::leanh::lean_dec(v___x_986_);
                                        v___x_1010_ = crate::leanh::lean_box(0);
                                        v_isShared_1011_ = v_isSharedCheck_1015_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_973_);
                                crate::leanh::lean_dec(v_a_966_);
                                v_a_1016_ = crate::leanh::lean_ctor_get(v___x_983_, 0);
                                v_isSharedCheck_1023_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_983_)) as u8;
                                if v_isSharedCheck_1023_ == 0 {
                                    v___x_1018_ = v___x_983_;
                                    v_isShared_1019_ = v_isSharedCheck_1023_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1016_);
                                    crate::leanh::lean_dec(v___x_983_);
                                    v___x_1018_ = crate::leanh::lean_box(0);
                                    v_isShared_1019_ = v_isSharedCheck_1023_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_973_);
                            crate::leanh::lean_dec(v_a_966_);
                            crate::leanh::lean_dec(v_fst_963_);
                            v_a_1024_ = crate::leanh::lean_ctor_get(v___x_974_, 0);
                            v_isSharedCheck_1031_ =
                                (!crate::leanh::lean_is_exclusive(v___x_974_)) as u8;
                            if v_isSharedCheck_1031_ == 0 {
                                v___x_1026_ = v___x_974_;
                                v_isShared_1027_ = v_isSharedCheck_1031_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1024_);
                                crate::leanh::lean_dec(v___x_974_);
                                v___x_1026_ = crate::leanh::lean_box(0);
                                v_isShared_1027_ = v_isSharedCheck_1031_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_966_);
                        crate::leanh::lean_dec(v_fst_963_);
                        v_a_1032_ = crate::leanh::lean_ctor_get(v___x_972_, 0);
                        v_isSharedCheck_1039_ =
                            (!crate::leanh::lean_is_exclusive(v___x_972_)) as u8;
                        if v_isSharedCheck_1039_ == 0 {
                            v___x_1034_ = v___x_972_;
                            v_isShared_1035_ = v_isSharedCheck_1039_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1032_);
                            crate::leanh::lean_dec(v___x_972_);
                            v___x_1034_ = crate::leanh::lean_box(0);
                            v_isShared_1035_ = v_isSharedCheck_1039_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_963_);
                    crate::leanh::lean_dec_ref(v___f_945_);
                    v___x_1040_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1040_, 0, v_a_966_);
                    if v_isShared_969_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_968_, 0, v___x_1040_);
                        v___x_1042_ = v___x_968_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_1043_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
                        v___x_1042_ = v_reuseFailAlloc_1043_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_991_ = crate::leanh::lean_ctor_get(v_a_987_, 0);
                crate::leanh::lean_inc(v_fst_991_);
                crate::leanh::lean_dec(v_a_987_);
                if crate::leanh::lean_obj_tag(v_fst_991_) == 1 {
                    v_val_992_ = crate::leanh::lean_ctor_get(v_fst_991_, 0);
                    v_isSharedCheck_1003_ = (!crate::leanh::lean_is_exclusive(v_fst_991_)) as u8;
                    if v_isSharedCheck_1003_ == 0 {
                        v___x_994_ = v_fst_991_;
                        v_isShared_995_ = v_isSharedCheck_1003_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_992_);
                        crate::leanh::lean_dec(v_fst_991_);
                        v___x_994_ = crate::leanh::lean_box(0);
                        v_isShared_995_ = v_isSharedCheck_1003_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_991_);
                    if v_isShared_990_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_989_, 0, v___x_980_);
                        v___x_1005_ = v___x_989_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1006_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_980_);
                        v___x_1005_ = v_reuseFailAlloc_1006_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v_snd_996_ = crate::leanh::lean_ctor_get(v_val_992_, 1);
                crate::leanh::lean_inc(v_snd_996_);
                crate::leanh::lean_dec(v_val_992_);
                if v_isShared_995_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_994_, 0, v_snd_996_);
                    v___x_998_ = v___x_994_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_snd_996_);
                    v___x_998_ = v_reuseFailAlloc_1002_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_990_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_989_, 0, v___x_998_);
                    v___x_1000_ = v___x_989_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1001_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
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
                    v_reuseFailAlloc_1014_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
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
                    v_reuseFailAlloc_1022_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
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
                    v_reuseFailAlloc_1030_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
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
                    v_reuseFailAlloc_1038_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
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
                    v_reuseFailAlloc_1051_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
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
                    v_reuseFailAlloc_1059_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
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
                    v_reuseFailAlloc_1067_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
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
    mut v_goal_1069_: *mut crate::leanh::LeanObject,
    mut v___f_1070_: *mut crate::leanh::LeanObject,
    mut v___y_1071_: *mut crate::leanh::LeanObject,
    mut v___y_1072_: *mut crate::leanh::LeanObject,
    mut v___y_1073_: *mut crate::leanh::LeanObject,
    mut v___y_1074_: *mut crate::leanh::LeanObject,
    mut v___y_1075_: *mut crate::leanh::LeanObject,
    mut v___y_1076_: *mut crate::leanh::LeanObject,
    mut v___y_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1076_);
    crate::leanh::lean_dec_ref(v___y_1075_);
    crate::leanh::lean_dec(v___y_1074_);
    crate::leanh::lean_dec_ref(v___y_1073_);
    crate::leanh::lean_dec(v___y_1072_);
    crate::leanh::lean_dec_ref(v___y_1071_);
    return v_res_1078_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__2(
    mut v___f_1079_: *mut crate::leanh::LeanObject,
    mut v_goal_1080_: *mut crate::leanh::LeanObject,
    mut v___y_1081_: *mut crate::leanh::LeanObject,
    mut v___y_1082_: *mut crate::leanh::LeanObject,
    mut v___y_1083_: *mut crate::leanh::LeanObject,
    mut v___y_1084_: *mut crate::leanh::LeanObject,
    mut v___y_1085_: *mut crate::leanh::LeanObject,
    mut v___y_1086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_goal_1080_);
    v___f_1088_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___boxed
            as *mut core::ffi::c_void,
        9,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1088_, 0, v_goal_1080_);
    crate::leanh::lean_closure_set(v___f_1088_, 1, v___f_1079_);
    v___x_1089_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_goal_1080_, v___f_1088_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
    return v___x_1089_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__2___boxed(
    mut v___f_1090_: *mut crate::leanh::LeanObject,
    mut v_goal_1091_: *mut crate::leanh::LeanObject,
    mut v___y_1092_: *mut crate::leanh::LeanObject,
    mut v___y_1093_: *mut crate::leanh::LeanObject,
    mut v___y_1094_: *mut crate::leanh::LeanObject,
    mut v___y_1095_: *mut crate::leanh::LeanObject,
    mut v___y_1096_: *mut crate::leanh::LeanObject,
    mut v___y_1097_: *mut crate::leanh::LeanObject,
    mut v___y_1098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1097_);
    crate::leanh::lean_dec_ref(v___y_1096_);
    crate::leanh::lean_dec(v___y_1095_);
    crate::leanh::lean_dec_ref(v___y_1094_);
    crate::leanh::lean_dec(v___y_1093_);
    crate::leanh::lean_dec_ref(v___y_1092_);
    return v_res_1099_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0(
    mut v_00_u03b2_1110_: *mut crate::leanh::LeanObject,
    mut v_m_1111_: *mut crate::leanh::LeanObject,
    mut v_a_1112_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1113_: u8 = 0;
    v___x_1113_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg(v_m_1111_, v_a_1112_);
    return v___x_1113_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___boxed(
    mut v_00_u03b2_1114_: *mut crate::leanh::LeanObject,
    mut v_m_1115_: *mut crate::leanh::LeanObject,
    mut v_a_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1117_: u8 = 0;
    let mut v_r_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1117_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0(v_00_u03b2_1114_, v_m_1115_, v_a_1116_);
    crate::leanh::lean_dec_ref(v_a_1116_);
    crate::leanh::lean_dec_ref(v_m_1115_);
    v_r_1118_ = crate::leanh::lean_box((v_res_1117_) as usize);
    return v_r_1118_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1(
    mut v_00_u03b2_1119_: *mut crate::leanh::LeanObject,
    mut v_m_1120_: *mut crate::leanh::LeanObject,
    mut v_a_1121_: *mut crate::leanh::LeanObject,
    mut v_b_1122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_m_1120_, v_a_1121_, v_b_1122_);
    return v___x_1123_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(
    mut v_as_1124_: *mut crate::leanh::LeanObject,
    mut v_sz_1125_: usize,
    mut v_i_1126_: usize,
    mut v_b_1127_: *mut crate::leanh::LeanObject,
    mut v___y_1128_: *mut crate::leanh::LeanObject,
    mut v___y_1129_: *mut crate::leanh::LeanObject,
    mut v___y_1130_: *mut crate::leanh::LeanObject,
    mut v___y_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v_as_1124_, v_sz_1125_, v_i_1126_, v_b_1127_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
    return v___x_1135_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___boxed(
    mut v_as_1136_: *mut crate::leanh::LeanObject,
    mut v_sz_1137_: *mut crate::leanh::LeanObject,
    mut v_i_1138_: *mut crate::leanh::LeanObject,
    mut v_b_1139_: *mut crate::leanh::LeanObject,
    mut v___y_1140_: *mut crate::leanh::LeanObject,
    mut v___y_1141_: *mut crate::leanh::LeanObject,
    mut v___y_1142_: *mut crate::leanh::LeanObject,
    mut v___y_1143_: *mut crate::leanh::LeanObject,
    mut v___y_1144_: *mut crate::leanh::LeanObject,
    mut v___y_1145_: *mut crate::leanh::LeanObject,
    mut v___y_1146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1147_: usize = 0;
    let mut v_i_boxed_1148_: usize = 0;
    let mut v_res_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1147_ = crate::leanh::lean_unbox_usize(v_sz_1137_);
    crate::leanh::lean_dec(v_sz_1137_);
    v_i_boxed_1148_ = crate::leanh::lean_unbox_usize(v_i_1138_);
    crate::leanh::lean_dec(v_i_1138_);
    v_res_1149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(v_as_1136_, v_sz_boxed_1147_, v_i_boxed_1148_, v_b_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
    crate::leanh::lean_dec(v___y_1145_);
    crate::leanh::lean_dec_ref(v___y_1144_);
    crate::leanh::lean_dec(v___y_1143_);
    crate::leanh::lean_dec_ref(v___y_1142_);
    crate::leanh::lean_dec(v___y_1141_);
    crate::leanh::lean_dec_ref(v___y_1140_);
    crate::leanh::lean_dec_ref(v_as_1136_);
    return v_res_1149_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0(
    mut v_00_u03b2_1150_: *mut crate::leanh::LeanObject,
    mut v_a_1151_: *mut crate::leanh::LeanObject,
    mut v_x_1152_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1153_: u8 = 0;
    v___x_1153_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg(v_a_1151_, v_x_1152_);
    return v___x_1153_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0___boxed(
    mut v_00_u03b2_1154_: *mut crate::leanh::LeanObject,
    mut v_a_1155_: *mut crate::leanh::LeanObject,
    mut v_x_1156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1157_: u8 = 0;
    let mut v_r_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_spec__0(v_00_u03b2_1154_, v_a_1155_, v_x_1156_);
    crate::leanh::lean_dec(v_x_1156_);
    crate::leanh::lean_dec_ref(v_a_1155_);
    v_r_1158_ = crate::leanh::lean_box((v_res_1157_) as usize);
    return v_r_1158_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2(
    mut v_00_u03b2_1159_: *mut crate::leanh::LeanObject,
    mut v_data_1160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2___redArg(v_data_1160_);
    return v___x_1161_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4(
    mut v_00_u03b2_1162_: *mut crate::leanh::LeanObject,
    mut v_i_1163_: *mut crate::leanh::LeanObject,
    mut v_source_1164_: *mut crate::leanh::LeanObject,
    mut v_target_1165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1166_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4___redArg(v_i_1163_, v_source_1164_, v_target_1165_);
    return v___x_1166_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b2_1167_: *mut crate::leanh::LeanObject,
    mut v_x_1168_: *mut crate::leanh::LeanObject,
    mut v_x_1169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1170_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4_spec__6___redArg(v_x_1168_, v_x_1169_);
    return v___x_1170_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
}
