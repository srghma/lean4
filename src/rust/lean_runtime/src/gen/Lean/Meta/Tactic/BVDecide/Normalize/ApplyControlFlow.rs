// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow
// Imports: Lean.Meta.Tactic.Simp Init.ByCases Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
    l_Lean_Expr_sort___override, l_Lean_mkAppN,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkAppOptM;
use crate::r#gen::Lean::Meta::Tactic::Simp::{
    initialize_Lean_Meta_Tactic_Simp, runtime_initialize_Lean_Meta_Tactic_Simp,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_pop, lean_mk_array};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_sub,
};
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 116, 101, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,18356704233129443855 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__4_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 112, 112, 108, 121, 95, 105, 116, 101, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,5460808614864354788 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 100, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,105488867511536770 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__4_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 112, 112, 108, 121, 95, 99, 111, 110, 100, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,2575197195497737166 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_400_ = crate::leanh::lean_box(0);
    v___x_401_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_402_ = lean_mk_empty_array_with_capacity(v___x_401_);
    v___x_403_ = lean_array_push(v___x_402_, v___x_400_);
    return v___x_403_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(
    mut v_x_407_: *mut crate::leanh::LeanObject,
    mut v_x_408_: *mut crate::leanh::LeanObject,
    mut v_x_409_: *mut crate::leanh::LeanObject,
    mut v___y_410_: *mut crate::leanh::LeanObject,
    mut v___y_411_: *mut crate::leanh::LeanObject,
    mut v___y_412_: *mut crate::leanh::LeanObject,
    mut v___y_413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: u8 = 0;
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: u8 = 0;
    let mut v_arg_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: u8 = 0;
    let mut v_arg_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: u8 = 0;
    let mut v_arg_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: u8 = 0;
    let mut v_arg_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: u8 = 0;
    let mut v_arg_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: u8 = 0;
    let mut v_params_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fnApp_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newT_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newE_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_482_: u8 = 0;
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_489_: u8 = 0;
    let mut v_a_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_493_: u8 = 0;
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_497_: u8 = 0;
    let mut v_a_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_501_: u8 = 0;
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_505_: u8 = 0;
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_407_) == 5 {
                    v_fn_418_ = crate::leanh::lean_ctor_get(v_x_407_, 0);
                    crate::leanh::lean_inc_ref(v_fn_418_);
                    v_arg_419_ = crate::leanh::lean_ctor_get(v_x_407_, 1);
                    crate::leanh::lean_inc_ref(v_arg_419_);
                    crate::leanh::lean_dec_ref_known(v_x_407_, 2);
                    v___x_420_ = lean_array_set(v_x_408_, v_x_409_, v_arg_419_);
                    v___x_421_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_422_ = lean_nat_sub(v_x_409_, v___x_421_);
                    crate::leanh::lean_dec(v_x_409_);
                    v_x_407_ = v_fn_418_;
                    v_x_408_ = v___x_420_;
                    v_x_409_ = v___x_422_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_409_);
                    v___x_424_ = lean_array_get_size(v_x_408_);
                    v___x_425_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_426_ = lean_nat_dec_eq(v___x_424_, v___x_425_);
                    if v___x_426_ == 0 {
                        v___x_427_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_428_ = lean_nat_sub(v___x_424_, v___x_427_);
                        v___x_429_ = lean_array_fget_borrowed(v_x_408_, v___x_428_);
                        crate::leanh::lean_dec(v___x_428_);
                        crate::leanh::lean_inc(v___x_429_);
                        v___x_430_ = l_Lean_Expr_cleanupAnnotations(v___x_429_);
                        v___x_431_ = l_Lean_Expr_isApp(v___x_430_);
                        if v___x_431_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_430_);
                            crate::leanh::lean_dec_ref(v_x_408_);
                            crate::leanh::lean_dec_ref(v_x_407_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_432_ = crate::leanh::lean_ctor_get(v___x_430_, 1);
                            crate::leanh::lean_inc_ref(v_arg_432_);
                            v___x_433_ = l_Lean_Expr_appFnCleanup___redArg(v___x_430_);
                            v___x_434_ = l_Lean_Expr_isApp(v___x_433_);
                            if v___x_434_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_433_);
                                crate::leanh::lean_dec_ref(v_arg_432_);
                                crate::leanh::lean_dec_ref(v_x_408_);
                                crate::leanh::lean_dec_ref(v_x_407_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_435_ = crate::leanh::lean_ctor_get(v___x_433_, 1);
                                crate::leanh::lean_inc_ref(v_arg_435_);
                                v___x_436_ = l_Lean_Expr_appFnCleanup___redArg(v___x_433_);
                                v___x_437_ = l_Lean_Expr_isApp(v___x_436_);
                                if v___x_437_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_436_);
                                    crate::leanh::lean_dec_ref(v_arg_435_);
                                    crate::leanh::lean_dec_ref(v_arg_432_);
                                    crate::leanh::lean_dec_ref(v_x_408_);
                                    crate::leanh::lean_dec_ref(v_x_407_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_438_ = crate::leanh::lean_ctor_get(v___x_436_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_438_);
                                    v___x_439_ = l_Lean_Expr_appFnCleanup___redArg(v___x_436_);
                                    v___x_440_ = l_Lean_Expr_isApp(v___x_439_);
                                    if v___x_440_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_439_);
                                        crate::leanh::lean_dec_ref(v_arg_438_);
                                        crate::leanh::lean_dec_ref(v_arg_435_);
                                        crate::leanh::lean_dec_ref(v_arg_432_);
                                        crate::leanh::lean_dec_ref(v_x_408_);
                                        crate::leanh::lean_dec_ref(v_x_407_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_441_ = crate::leanh::lean_ctor_get(v___x_439_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_441_);
                                        v___x_442_ = l_Lean_Expr_appFnCleanup___redArg(v___x_439_);
                                        v___x_443_ = l_Lean_Expr_isApp(v___x_442_);
                                        if v___x_443_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_442_);
                                            crate::leanh::lean_dec_ref(v_arg_441_);
                                            crate::leanh::lean_dec_ref(v_arg_438_);
                                            crate::leanh::lean_dec_ref(v_arg_435_);
                                            crate::leanh::lean_dec_ref(v_arg_432_);
                                            crate::leanh::lean_dec_ref(v_x_408_);
                                            crate::leanh::lean_dec_ref(v_x_407_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v_arg_444_ = crate::leanh::lean_ctor_get(v___x_442_, 1);
                                            crate::leanh::lean_inc_ref(v_arg_444_);
                                            v___x_445_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_442_);
                                            v___x_446_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__2;
                                            v___x_447_ =
                                                l_Lean_Expr_isConstOf(v___x_445_, v___x_446_);
                                            crate::leanh::lean_dec_ref(v___x_445_);
                                            if v___x_447_ == 0 {
                                                crate::leanh::lean_dec_ref(v_arg_444_);
                                                crate::leanh::lean_dec_ref(v_arg_441_);
                                                crate::leanh::lean_dec_ref(v_arg_438_);
                                                crate::leanh::lean_dec_ref(v_arg_435_);
                                                crate::leanh::lean_dec_ref(v_arg_432_);
                                                crate::leanh::lean_dec_ref(v_x_408_);
                                                crate::leanh::lean_dec_ref(v_x_407_);
                                                state = 1;
                                                continue;
                                            } else {
                                                v_params_448_ = lean_array_pop(v_x_408_);
                                                v_fnApp_449_ =
                                                    l_Lean_mkAppN(v_x_407_, v_params_448_);
                                                crate::leanh::lean_dec_ref(v_params_448_);
                                                crate::leanh::lean_inc_ref(v_arg_435_);
                                                crate::leanh::lean_inc_ref_n(v_fnApp_449_, 2);
                                                v_newT_450_ = l_Lean_Expr_app___override(
                                                    v_fnApp_449_,
                                                    v_arg_435_,
                                                );
                                                crate::leanh::lean_inc_ref(v_arg_432_);
                                                v_newE_451_ = l_Lean_Expr_app___override(
                                                    v_fnApp_449_,
                                                    v_arg_432_,
                                                );
                                                v___x_452_ = crate::leanh::lean_box(0);
                                                v___x_453_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_453_, 0, v_arg_441_,
                                                );
                                                v___x_454_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_454_, 0, v_arg_438_,
                                                );
                                                v___x_455_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_455_,
                                                    0,
                                                    v_newT_450_,
                                                );
                                                v___x_456_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_456_,
                                                    0,
                                                    v_newE_451_,
                                                );
                                                v___x_457_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__3_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__3);
                                                crate::leanh::lean_inc_ref(v___x_453_);
                                                v___x_458_ =
                                                    lean_array_push(v___x_457_, v___x_453_);
                                                crate::leanh::lean_inc_ref(v___x_454_);
                                                v___x_459_ =
                                                    lean_array_push(v___x_458_, v___x_454_);
                                                v___x_460_ =
                                                    lean_array_push(v___x_459_, v___x_455_);
                                                v___x_461_ =
                                                    lean_array_push(v___x_460_, v___x_456_);
                                                v___x_462_ = l_Lean_Meta_mkAppOptM(
                                                    v___x_446_, v___x_461_, v___y_410_, v___y_411_,
                                                    v___y_412_, v___y_413_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_462_) == 0 {
                                                    v_a_463_ =
                                                        crate::leanh::lean_ctor_get(v___x_462_, 0);
                                                    crate::leanh::lean_inc(v_a_463_);
                                                    crate::leanh::lean_dec_ref_known(v___x_462_, 1);
                                                    v___x_464_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__5;
                                                    v___x_465_ = crate::leanh::lean_alloc_ctor(
                                                        1,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_465_, 0, v_arg_444_,
                                                    );
                                                    v___x_466_ = crate::leanh::lean_alloc_ctor(
                                                        1,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_466_,
                                                        0,
                                                        v_fnApp_449_,
                                                    );
                                                    v___x_467_ = crate::leanh::lean_alloc_ctor(
                                                        1,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_467_, 0, v_arg_435_,
                                                    );
                                                    v___x_468_ = crate::leanh::lean_alloc_ctor(
                                                        1,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_468_, 0, v_arg_432_,
                                                    );
                                                    v___x_469_ =
                                                        crate::leanh::lean_unsigned_to_nat(7);
                                                    v___x_470_ = lean_mk_empty_array_with_capacity(
                                                        v___x_469_,
                                                    );
                                                    v___x_471_ =
                                                        lean_array_push(v___x_470_, v___x_465_);
                                                    v___x_472_ =
                                                        lean_array_push(v___x_471_, v___x_452_);
                                                    v___x_473_ =
                                                        lean_array_push(v___x_472_, v___x_466_);
                                                    v___x_474_ =
                                                        lean_array_push(v___x_473_, v___x_453_);
                                                    v___x_475_ =
                                                        lean_array_push(v___x_474_, v___x_454_);
                                                    v___x_476_ =
                                                        lean_array_push(v___x_475_, v___x_467_);
                                                    v___x_477_ =
                                                        lean_array_push(v___x_476_, v___x_468_);
                                                    v___x_478_ = l_Lean_Meta_mkAppOptM(
                                                        v___x_464_, v___x_477_, v___y_410_,
                                                        v___y_411_, v___y_412_, v___y_413_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_478_) == 0 {
                                                        v_a_479_ = crate::leanh::lean_ctor_get(
                                                            v___x_478_, 0,
                                                        );
                                                        v_isSharedCheck_489_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_478_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_489_ == 0 {
                                                            v___x_481_ = v___x_478_;
                                                            v_isShared_482_ = v_isSharedCheck_489_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_479_);
                                                            crate::leanh::lean_dec(v___x_478_);
                                                            v___x_481_ = crate::leanh::lean_box(0);
                                                            v_isShared_482_ = v_isSharedCheck_489_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_463_);
                                                        v_a_490_ = crate::leanh::lean_ctor_get(
                                                            v___x_478_, 0,
                                                        );
                                                        v_isSharedCheck_497_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_478_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_497_ == 0 {
                                                            v___x_492_ = v___x_478_;
                                                            v_isShared_493_ = v_isSharedCheck_497_;
                                                            state = 4;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_490_);
                                                            crate::leanh::lean_dec(v___x_478_);
                                                            v___x_492_ = crate::leanh::lean_box(0);
                                                            v_isShared_493_ = v_isSharedCheck_497_;
                                                            state = 4;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref_known(v___x_454_, 1);
                                                    crate::leanh::lean_dec_ref_known(v___x_453_, 1);
                                                    crate::leanh::lean_dec_ref(v_fnApp_449_);
                                                    crate::leanh::lean_dec_ref(v_arg_444_);
                                                    crate::leanh::lean_dec_ref(v_arg_435_);
                                                    crate::leanh::lean_dec_ref(v_arg_432_);
                                                    v_a_498_ =
                                                        crate::leanh::lean_ctor_get(v___x_462_, 0);
                                                    v_isSharedCheck_505_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_462_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_505_ == 0 {
                                                        v___x_500_ = v___x_462_;
                                                        v_isShared_501_ = v_isSharedCheck_505_;
                                                        state = 6;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_498_);
                                                        crate::leanh::lean_dec(v___x_462_);
                                                        v___x_500_ = crate::leanh::lean_box(0);
                                                        v_isShared_501_ = v_isSharedCheck_505_;
                                                        state = 6;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_408_);
                        crate::leanh::lean_dec_ref(v_x_407_);
                        v___x_506_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__0;
                        v___x_507_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_507_, 0, v___x_506_);
                        return v___x_507_;
                    }
                }
            }
            1 => {
                v___x_416_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__0;
                v___x_417_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_417_, 0, v___x_416_);
                return v___x_417_;
            }
            2 => {
                v___x_483_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_483_, 0, v_a_479_);
                v___x_484_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_484_, 0, v_a_463_);
                crate::leanh::lean_ctor_set(v___x_484_, 1, v___x_483_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_484_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_447_,
                );
                v___x_485_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_485_, 0, v___x_484_);
                if v_isShared_482_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_481_, 0, v___x_485_);
                    v___x_487_ = v___x_481_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_488_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
                    v___x_487_ = v_reuseFailAlloc_488_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_487_;
            }
            4 => {
                if v_isShared_493_ == 0 {
                    v___x_495_ = v___x_492_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_496_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
                    v___x_495_ = v_reuseFailAlloc_496_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_495_;
            }
            6 => {
                if v_isShared_501_ == 0 {
                    v___x_503_ = v___x_500_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_504_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
                    v___x_503_ = v_reuseFailAlloc_504_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___boxed(
    mut v_x_508_: *mut crate::leanh::LeanObject,
    mut v_x_509_: *mut crate::leanh::LeanObject,
    mut v_x_510_: *mut crate::leanh::LeanObject,
    mut v___y_511_: *mut crate::leanh::LeanObject,
    mut v___y_512_: *mut crate::leanh::LeanObject,
    mut v___y_513_: *mut crate::leanh::LeanObject,
    mut v___y_514_: *mut crate::leanh::LeanObject,
    mut v___y_515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_516_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_x_508_, v_x_509_, v_x_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
    crate::leanh::lean_dec(v___y_514_);
    crate::leanh::lean_dec_ref(v___y_513_);
    crate::leanh::lean_dec(v___y_512_);
    crate::leanh::lean_dec_ref(v___y_511_);
    return v_res_516_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_517_ = crate::leanh::lean_box(0);
    v_dummy_518_ = l_Lean_Expr_sort___override(v___x_517_);
    return v_dummy_518_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc(
    mut v_e_519_: *mut crate::leanh::LeanObject,
    mut v_a_520_: *mut crate::leanh::LeanObject,
    mut v_a_521_: *mut crate::leanh::LeanObject,
    mut v_a_522_: *mut crate::leanh::LeanObject,
    mut v_a_523_: *mut crate::leanh::LeanObject,
    mut v_a_524_: *mut crate::leanh::LeanObject,
    mut v_a_525_: *mut crate::leanh::LeanObject,
    mut v_a_526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dummy_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dummy_528_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0,
    );
    v_nargs_529_ = l_Lean_Expr_getAppNumArgs(v_e_519_);
    crate::leanh::lean_inc(v_nargs_529_);
    v___x_530_ = lean_mk_array(v_nargs_529_, v_dummy_528_);
    v___x_531_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_532_ = lean_nat_sub(v_nargs_529_, v___x_531_);
    crate::leanh::lean_dec(v_nargs_529_);
    v___x_533_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_e_519_, v___x_530_, v___x_532_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
    return v___x_533_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___boxed(
    mut v_e_534_: *mut crate::leanh::LeanObject,
    mut v_a_535_: *mut crate::leanh::LeanObject,
    mut v_a_536_: *mut crate::leanh::LeanObject,
    mut v_a_537_: *mut crate::leanh::LeanObject,
    mut v_a_538_: *mut crate::leanh::LeanObject,
    mut v_a_539_: *mut crate::leanh::LeanObject,
    mut v_a_540_: *mut crate::leanh::LeanObject,
    mut v_a_541_: *mut crate::leanh::LeanObject,
    mut v_a_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_543_ = l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc(
        v_e_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_,
    );
    crate::leanh::lean_dec(v_a_541_);
    crate::leanh::lean_dec_ref(v_a_540_);
    crate::leanh::lean_dec(v_a_539_);
    crate::leanh::lean_dec_ref(v_a_538_);
    crate::leanh::lean_dec(v_a_537_);
    crate::leanh::lean_dec_ref(v_a_536_);
    crate::leanh::lean_dec(v_a_535_);
    return v_res_543_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0(
    mut v_x_544_: *mut crate::leanh::LeanObject,
    mut v_x_545_: *mut crate::leanh::LeanObject,
    mut v_x_546_: *mut crate::leanh::LeanObject,
    mut v___y_547_: *mut crate::leanh::LeanObject,
    mut v___y_548_: *mut crate::leanh::LeanObject,
    mut v___y_549_: *mut crate::leanh::LeanObject,
    mut v___y_550_: *mut crate::leanh::LeanObject,
    mut v___y_551_: *mut crate::leanh::LeanObject,
    mut v___y_552_: *mut crate::leanh::LeanObject,
    mut v___y_553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_555_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg(v_x_544_, v_x_545_, v_x_546_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
    return v___x_555_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___boxed(
    mut v_x_556_: *mut crate::leanh::LeanObject,
    mut v_x_557_: *mut crate::leanh::LeanObject,
    mut v_x_558_: *mut crate::leanh::LeanObject,
    mut v___y_559_: *mut crate::leanh::LeanObject,
    mut v___y_560_: *mut crate::leanh::LeanObject,
    mut v___y_561_: *mut crate::leanh::LeanObject,
    mut v___y_562_: *mut crate::leanh::LeanObject,
    mut v___y_563_: *mut crate::leanh::LeanObject,
    mut v___y_564_: *mut crate::leanh::LeanObject,
    mut v___y_565_: *mut crate::leanh::LeanObject,
    mut v___y_566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_567_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0(
            v_x_556_, v_x_557_, v_x_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_,
            v___y_563_, v___y_564_, v___y_565_,
        );
    crate::leanh::lean_dec(v___y_565_);
    crate::leanh::lean_dec_ref(v___y_564_);
    crate::leanh::lean_dec(v___y_563_);
    crate::leanh::lean_dec_ref(v___y_562_);
    crate::leanh::lean_dec(v___y_561_);
    crate::leanh::lean_dec_ref(v___y_560_);
    crate::leanh::lean_dec(v___y_559_);
    return v_res_567_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_571_ = crate::leanh::lean_box(0);
    v___x_572_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_573_ = lean_mk_empty_array_with_capacity(v___x_572_);
    v___x_574_ = lean_array_push(v___x_573_, v___x_571_);
    return v___x_574_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(
    mut v_x_580_: *mut crate::leanh::LeanObject,
    mut v_x_581_: *mut crate::leanh::LeanObject,
    mut v_x_582_: *mut crate::leanh::LeanObject,
    mut v___y_583_: *mut crate::leanh::LeanObject,
    mut v___y_584_: *mut crate::leanh::LeanObject,
    mut v___y_585_: *mut crate::leanh::LeanObject,
    mut v___y_586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: u8 = 0;
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    let mut v_arg_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: u8 = 0;
    let mut v_arg_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: u8 = 0;
    let mut v_arg_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: u8 = 0;
    let mut v_arg_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: u8 = 0;
    let mut v_params_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fnApp_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newT_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newE_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_649_: u8 = 0;
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut v_a_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_660_: u8 = 0;
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_664_: u8 = 0;
    let mut v_a_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_668_: u8 = 0;
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_672_: u8 = 0;
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_580_) == 5 {
                    v_fn_591_ = crate::leanh::lean_ctor_get(v_x_580_, 0);
                    crate::leanh::lean_inc_ref(v_fn_591_);
                    v_arg_592_ = crate::leanh::lean_ctor_get(v_x_580_, 1);
                    crate::leanh::lean_inc_ref(v_arg_592_);
                    crate::leanh::lean_dec_ref_known(v_x_580_, 2);
                    v___x_593_ = lean_array_set(v_x_581_, v_x_582_, v_arg_592_);
                    v___x_594_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_595_ = lean_nat_sub(v_x_582_, v___x_594_);
                    crate::leanh::lean_dec(v_x_582_);
                    v_x_580_ = v_fn_591_;
                    v_x_581_ = v___x_593_;
                    v_x_582_ = v___x_595_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_582_);
                    v___x_597_ = lean_array_get_size(v_x_581_);
                    v___x_598_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_599_ = lean_nat_dec_eq(v___x_597_, v___x_598_);
                    if v___x_599_ == 0 {
                        v___x_600_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_601_ = lean_nat_sub(v___x_597_, v___x_600_);
                        v___x_602_ = lean_array_fget_borrowed(v_x_581_, v___x_601_);
                        crate::leanh::lean_dec(v___x_601_);
                        crate::leanh::lean_inc(v___x_602_);
                        v___x_603_ = l_Lean_Expr_cleanupAnnotations(v___x_602_);
                        v___x_604_ = l_Lean_Expr_isApp(v___x_603_);
                        if v___x_604_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_603_);
                            crate::leanh::lean_dec_ref(v_x_581_);
                            crate::leanh::lean_dec_ref(v_x_580_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_605_ = crate::leanh::lean_ctor_get(v___x_603_, 1);
                            crate::leanh::lean_inc_ref(v_arg_605_);
                            v___x_606_ = l_Lean_Expr_appFnCleanup___redArg(v___x_603_);
                            v___x_607_ = l_Lean_Expr_isApp(v___x_606_);
                            if v___x_607_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_606_);
                                crate::leanh::lean_dec_ref(v_arg_605_);
                                crate::leanh::lean_dec_ref(v_x_581_);
                                crate::leanh::lean_dec_ref(v_x_580_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_608_ = crate::leanh::lean_ctor_get(v___x_606_, 1);
                                crate::leanh::lean_inc_ref(v_arg_608_);
                                v___x_609_ = l_Lean_Expr_appFnCleanup___redArg(v___x_606_);
                                v___x_610_ = l_Lean_Expr_isApp(v___x_609_);
                                if v___x_610_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_609_);
                                    crate::leanh::lean_dec_ref(v_arg_608_);
                                    crate::leanh::lean_dec_ref(v_arg_605_);
                                    crate::leanh::lean_dec_ref(v_x_581_);
                                    crate::leanh::lean_dec_ref(v_x_580_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_611_ = crate::leanh::lean_ctor_get(v___x_609_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_611_);
                                    v___x_612_ = l_Lean_Expr_appFnCleanup___redArg(v___x_609_);
                                    v___x_613_ = l_Lean_Expr_isApp(v___x_612_);
                                    if v___x_613_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_612_);
                                        crate::leanh::lean_dec_ref(v_arg_611_);
                                        crate::leanh::lean_dec_ref(v_arg_608_);
                                        crate::leanh::lean_dec_ref(v_arg_605_);
                                        crate::leanh::lean_dec_ref(v_x_581_);
                                        crate::leanh::lean_dec_ref(v_x_580_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_614_ = crate::leanh::lean_ctor_get(v___x_612_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_614_);
                                        v___x_615_ = l_Lean_Expr_appFnCleanup___redArg(v___x_612_);
                                        v___x_616_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__1;
                                        v___x_617_ = l_Lean_Expr_isConstOf(v___x_615_, v___x_616_);
                                        crate::leanh::lean_dec_ref(v___x_615_);
                                        if v___x_617_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_614_);
                                            crate::leanh::lean_dec_ref(v_arg_611_);
                                            crate::leanh::lean_dec_ref(v_arg_608_);
                                            crate::leanh::lean_dec_ref(v_arg_605_);
                                            crate::leanh::lean_dec_ref(v_x_581_);
                                            crate::leanh::lean_dec_ref(v_x_580_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v_params_618_ = lean_array_pop(v_x_581_);
                                            v_fnApp_619_ = l_Lean_mkAppN(v_x_580_, v_params_618_);
                                            crate::leanh::lean_dec_ref(v_params_618_);
                                            crate::leanh::lean_inc_ref(v_arg_608_);
                                            crate::leanh::lean_inc_ref_n(v_fnApp_619_, 2);
                                            v_newT_620_ = l_Lean_Expr_app___override(
                                                v_fnApp_619_,
                                                v_arg_608_,
                                            );
                                            crate::leanh::lean_inc_ref(v_arg_605_);
                                            v_newE_621_ = l_Lean_Expr_app___override(
                                                v_fnApp_619_,
                                                v_arg_605_,
                                            );
                                            v___x_622_ = crate::leanh::lean_box(0);
                                            v___x_623_ =
                                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_623_, 0, v_arg_611_);
                                            v___x_624_ =
                                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_624_, 0, v_newT_620_);
                                            v___x_625_ =
                                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_625_, 0, v_newE_621_);
                                            v___x_626_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__2);
                                            crate::leanh::lean_inc_ref(v___x_623_);
                                            v___x_627_ = lean_array_push(v___x_626_, v___x_623_);
                                            v___x_628_ = lean_array_push(v___x_627_, v___x_624_);
                                            v___x_629_ = lean_array_push(v___x_628_, v___x_625_);
                                            v___x_630_ = l_Lean_Meta_mkAppOptM(
                                                v___x_616_, v___x_629_, v___y_583_, v___y_584_,
                                                v___y_585_, v___y_586_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_630_) == 0 {
                                                v_a_631_ =
                                                    crate::leanh::lean_ctor_get(v___x_630_, 0);
                                                crate::leanh::lean_inc(v_a_631_);
                                                crate::leanh::lean_dec_ref_known(v___x_630_, 1);
                                                v___x_632_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___closed__5;
                                                v___x_633_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_633_, 0, v_arg_614_,
                                                );
                                                v___x_634_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_634_,
                                                    0,
                                                    v_fnApp_619_,
                                                );
                                                v___x_635_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_635_, 0, v_arg_608_,
                                                );
                                                v___x_636_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_636_, 0, v_arg_605_,
                                                );
                                                v___x_637_ = crate::leanh::lean_unsigned_to_nat(6);
                                                v___x_638_ =
                                                    lean_mk_empty_array_with_capacity(v___x_637_);
                                                v___x_639_ =
                                                    lean_array_push(v___x_638_, v___x_633_);
                                                v___x_640_ =
                                                    lean_array_push(v___x_639_, v___x_622_);
                                                v___x_641_ =
                                                    lean_array_push(v___x_640_, v___x_634_);
                                                v___x_642_ =
                                                    lean_array_push(v___x_641_, v___x_623_);
                                                v___x_643_ =
                                                    lean_array_push(v___x_642_, v___x_635_);
                                                v___x_644_ =
                                                    lean_array_push(v___x_643_, v___x_636_);
                                                v___x_645_ = l_Lean_Meta_mkAppOptM(
                                                    v___x_632_, v___x_644_, v___y_583_, v___y_584_,
                                                    v___y_585_, v___y_586_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_645_) == 0 {
                                                    v_a_646_ =
                                                        crate::leanh::lean_ctor_get(v___x_645_, 0);
                                                    v_isSharedCheck_656_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_645_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_656_ == 0 {
                                                        v___x_648_ = v___x_645_;
                                                        v_isShared_649_ = v_isSharedCheck_656_;
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_646_);
                                                        crate::leanh::lean_dec(v___x_645_);
                                                        v___x_648_ = crate::leanh::lean_box(0);
                                                        v_isShared_649_ = v_isSharedCheck_656_;
                                                        state = 2;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_631_);
                                                    v_a_657_ =
                                                        crate::leanh::lean_ctor_get(v___x_645_, 0);
                                                    v_isSharedCheck_664_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_645_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_664_ == 0 {
                                                        v___x_659_ = v___x_645_;
                                                        v_isShared_660_ = v_isSharedCheck_664_;
                                                        state = 4;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_657_);
                                                        crate::leanh::lean_dec(v___x_645_);
                                                        v___x_659_ = crate::leanh::lean_box(0);
                                                        v_isShared_660_ = v_isSharedCheck_664_;
                                                        state = 4;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref_known(v___x_623_, 1);
                                                crate::leanh::lean_dec_ref(v_fnApp_619_);
                                                crate::leanh::lean_dec_ref(v_arg_614_);
                                                crate::leanh::lean_dec_ref(v_arg_608_);
                                                crate::leanh::lean_dec_ref(v_arg_605_);
                                                v_a_665_ =
                                                    crate::leanh::lean_ctor_get(v___x_630_, 0);
                                                v_isSharedCheck_672_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_630_))
                                                        as u8;
                                                if v_isSharedCheck_672_ == 0 {
                                                    v___x_667_ = v___x_630_;
                                                    v_isShared_668_ = v_isSharedCheck_672_;
                                                    state = 6;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_665_);
                                                    crate::leanh::lean_dec(v___x_630_);
                                                    v___x_667_ = crate::leanh::lean_box(0);
                                                    v_isShared_668_ = v_isSharedCheck_672_;
                                                    state = 6;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_581_);
                        crate::leanh::lean_dec_ref(v_x_580_);
                        v___x_673_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__0;
                        v___x_674_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_674_, 0, v___x_673_);
                        return v___x_674_;
                    }
                }
            }
            1 => {
                v___x_589_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc_spec__0___redArg___closed__0;
                v___x_590_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_590_, 0, v___x_589_);
                return v___x_590_;
            }
            2 => {
                v___x_650_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_650_, 0, v_a_646_);
                v___x_651_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_651_, 0, v_a_631_);
                crate::leanh::lean_ctor_set(v___x_651_, 1, v___x_650_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_651_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_617_,
                );
                v___x_652_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_652_, 0, v___x_651_);
                if v_isShared_649_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_648_, 0, v___x_652_);
                    v___x_654_ = v___x_648_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_655_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
                    v___x_654_ = v_reuseFailAlloc_655_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_654_;
            }
            4 => {
                if v_isShared_660_ == 0 {
                    v___x_662_ = v___x_659_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_663_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
                    v___x_662_ = v_reuseFailAlloc_663_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_662_;
            }
            6 => {
                if v_isShared_668_ == 0 {
                    v___x_670_ = v___x_667_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_671_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
                    v___x_670_ = v_reuseFailAlloc_671_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg___boxed(
    mut v_x_675_: *mut crate::leanh::LeanObject,
    mut v_x_676_: *mut crate::leanh::LeanObject,
    mut v_x_677_: *mut crate::leanh::LeanObject,
    mut v___y_678_: *mut crate::leanh::LeanObject,
    mut v___y_679_: *mut crate::leanh::LeanObject,
    mut v___y_680_: *mut crate::leanh::LeanObject,
    mut v___y_681_: *mut crate::leanh::LeanObject,
    mut v___y_682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_683_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(v_x_675_, v_x_676_, v_x_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
    crate::leanh::lean_dec(v___y_681_);
    crate::leanh::lean_dec_ref(v___y_680_);
    crate::leanh::lean_dec(v___y_679_);
    crate::leanh::lean_dec_ref(v___y_678_);
    return v_res_683_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc(
    mut v_e_684_: *mut crate::leanh::LeanObject,
    mut v_a_685_: *mut crate::leanh::LeanObject,
    mut v_a_686_: *mut crate::leanh::LeanObject,
    mut v_a_687_: *mut crate::leanh::LeanObject,
    mut v_a_688_: *mut crate::leanh::LeanObject,
    mut v_a_689_: *mut crate::leanh::LeanObject,
    mut v_a_690_: *mut crate::leanh::LeanObject,
    mut v_a_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dummy_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dummy_693_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___closed__0,
    );
    v_nargs_694_ = l_Lean_Expr_getAppNumArgs(v_e_684_);
    crate::leanh::lean_inc(v_nargs_694_);
    v___x_695_ = lean_mk_array(v_nargs_694_, v_dummy_693_);
    v___x_696_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_697_ = lean_nat_sub(v_nargs_694_, v___x_696_);
    crate::leanh::lean_dec(v_nargs_694_);
    v___x_698_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(v_e_684_, v___x_695_, v___x_697_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
    return v___x_698_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc___boxed(
    mut v_e_699_: *mut crate::leanh::LeanObject,
    mut v_a_700_: *mut crate::leanh::LeanObject,
    mut v_a_701_: *mut crate::leanh::LeanObject,
    mut v_a_702_: *mut crate::leanh::LeanObject,
    mut v_a_703_: *mut crate::leanh::LeanObject,
    mut v_a_704_: *mut crate::leanh::LeanObject,
    mut v_a_705_: *mut crate::leanh::LeanObject,
    mut v_a_706_: *mut crate::leanh::LeanObject,
    mut v_a_707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_708_ = l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc(
        v_e_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_,
    );
    crate::leanh::lean_dec(v_a_706_);
    crate::leanh::lean_dec_ref(v_a_705_);
    crate::leanh::lean_dec(v_a_704_);
    crate::leanh::lean_dec_ref(v_a_703_);
    crate::leanh::lean_dec(v_a_702_);
    crate::leanh::lean_dec_ref(v_a_701_);
    crate::leanh::lean_dec(v_a_700_);
    return v_res_708_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0(
    mut v_x_709_: *mut crate::leanh::LeanObject,
    mut v_x_710_: *mut crate::leanh::LeanObject,
    mut v_x_711_: *mut crate::leanh::LeanObject,
    mut v___y_712_: *mut crate::leanh::LeanObject,
    mut v___y_713_: *mut crate::leanh::LeanObject,
    mut v___y_714_: *mut crate::leanh::LeanObject,
    mut v___y_715_: *mut crate::leanh::LeanObject,
    mut v___y_716_: *mut crate::leanh::LeanObject,
    mut v___y_717_: *mut crate::leanh::LeanObject,
    mut v___y_718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_720_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___redArg(v_x_709_, v_x_710_, v_x_711_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
    return v___x_720_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0___boxed(
    mut v_x_721_: *mut crate::leanh::LeanObject,
    mut v_x_722_: *mut crate::leanh::LeanObject,
    mut v_x_723_: *mut crate::leanh::LeanObject,
    mut v___y_724_: *mut crate::leanh::LeanObject,
    mut v___y_725_: *mut crate::leanh::LeanObject,
    mut v___y_726_: *mut crate::leanh::LeanObject,
    mut v___y_727_: *mut crate::leanh::LeanObject,
    mut v___y_728_: *mut crate::leanh::LeanObject,
    mut v___y_729_: *mut crate::leanh::LeanObject,
    mut v___y_730_: *mut crate::leanh::LeanObject,
    mut v___y_731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_732_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc_spec__0(v_x_721_, v_x_722_, v_x_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
    crate::leanh::lean_dec(v___y_730_);
    crate::leanh::lean_dec_ref(v___y_729_);
    crate::leanh::lean_dec(v___y_728_);
    crate::leanh::lean_dec_ref(v___y_727_);
    crate::leanh::lean_dec(v___y_726_);
    crate::leanh::lean_dec_ref(v___y_725_);
    crate::leanh::lean_dec(v___y_724_);
    return v_res_732_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath_spec__0___redArg(
    mut v_j_733_: *mut crate::leanh::LeanObject,
    mut v_a_734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_736_: u8 = 0;
    let mut v_one_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_735_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_736_ = lean_nat_dec_eq(v_j_733_, v_zero_735_);
                if v_isZero_736_ == 1 {
                    crate::leanh::lean_dec(v_j_733_);
                    return v_a_734_;
                } else {
                    v_one_737_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_738_ = lean_nat_sub(v_j_733_, v_one_737_);
                    crate::leanh::lean_dec(v_j_733_);
                    v___x_739_ = crate::leanh::lean_box(0);
                    v___x_740_ = lean_array_push(v_a_734_, v___x_739_);
                    v_j_733_ = v_n_738_;
                    v_a_734_ = v___x_740_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath(
    mut v_struct_742_: *mut crate::leanh::LeanObject,
    mut v_structParams_743_: *mut crate::leanh::LeanObject,
    mut v_projIdx_744_: *mut crate::leanh::LeanObject,
    mut v_controlFlow_745_: *mut crate::leanh::LeanObject,
    mut v_controlFlowParams_746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stars_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_747_ = lean_nat_add(v_structParams_743_, v_controlFlowParams_746_);
    v___x_748_ = crate::leanh::lean_unsigned_to_nat(1);
    v_stars_749_ = lean_nat_sub(v___x_747_, v___x_748_);
    crate::leanh::lean_dec(v___x_747_);
    v___x_750_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_751_ = lean_nat_add(v___x_750_, v_stars_749_);
    v_path_752_ = lean_mk_empty_array_with_capacity(v___x_751_);
    crate::leanh::lean_dec(v___x_751_);
    v___x_753_ = crate::leanh::lean_unsigned_to_nat(0);
    crate::leanh::lean_inc(v_struct_742_);
    v___x_754_ = crate::leanh::lean_alloc_ctor(6, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_754_, 0, v_struct_742_);
    crate::leanh::lean_ctor_set(v___x_754_, 1, v_projIdx_744_);
    crate::leanh::lean_ctor_set(v___x_754_, 2, v___x_753_);
    v_path_755_ = lean_array_push(v_path_752_, v___x_754_);
    v___x_756_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_756_, 0, v_controlFlow_745_);
    crate::leanh::lean_ctor_set(v___x_756_, 1, v_controlFlowParams_746_);
    v_path_757_ = lean_array_push(v_path_755_, v___x_756_);
    v___x_758_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_758_, 0, v_struct_742_);
    crate::leanh::lean_ctor_set(v___x_758_, 1, v_structParams_743_);
    v_path_759_ = lean_array_push(v_path_757_, v___x_758_);
    v___x_760_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath_spec__0___redArg(v_stars_749_, v_path_759_);
    return v___x_760_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath_spec__0(
    mut v_n_761_: *mut crate::leanh::LeanObject,
    mut v_j_762_: *mut crate::leanh::LeanObject,
    mut v_a_763_: *mut crate::leanh::LeanObject,
    mut v_a_764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath_spec__0___redArg(v_j_762_, v_a_764_);
    return v___x_765_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath_spec__0___boxed(
    mut v_n_766_: *mut crate::leanh::LeanObject,
    mut v_j_767_: *mut crate::leanh::LeanObject,
    mut v_a_768_: *mut crate::leanh::LeanObject,
    mut v_a_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_770_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath_spec__0(v_n_766_, v_j_767_, v_a_768_, v_a_769_);
    crate::leanh::lean_dec(v_n_766_);
    return v_res_770_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_mkApplyUnaryControlDiscrPath(
    mut v_type_771_: *mut crate::leanh::LeanObject,
    mut v_typeParams_772_: *mut crate::leanh::LeanObject,
    mut v_constName_773_: *mut crate::leanh::LeanObject,
    mut v_controlFlow_774_: *mut crate::leanh::LeanObject,
    mut v_controlFlowParams_775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stars_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_776_ = lean_nat_add(v_typeParams_772_, v_controlFlowParams_775_);
    v___x_777_ = crate::leanh::lean_unsigned_to_nat(1);
    v_stars_778_ = lean_nat_sub(v___x_776_, v___x_777_);
    crate::leanh::lean_dec(v___x_776_);
    v___x_779_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_780_ = lean_nat_add(v___x_779_, v_stars_778_);
    v_path_781_ = lean_mk_empty_array_with_capacity(v___x_780_);
    crate::leanh::lean_dec(v___x_780_);
    v___x_782_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_782_, 0, v_constName_773_);
    crate::leanh::lean_ctor_set(v___x_782_, 1, v___x_777_);
    v_path_783_ = lean_array_push(v_path_781_, v___x_782_);
    v___x_784_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_784_, 0, v_controlFlow_774_);
    crate::leanh::lean_ctor_set(v___x_784_, 1, v_controlFlowParams_775_);
    v_path_785_ = lean_array_push(v_path_783_, v___x_784_);
    v___x_786_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_786_, 0, v_type_771_);
    crate::leanh::lean_ctor_set(v___x_786_, 1, v_typeParams_772_);
    v_path_787_ = lean_array_push(v_path_785_, v___x_786_);
    v_path_788_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath_spec__0___redArg(v_stars_778_, v_path_787_);
    return v_path_788_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
}
