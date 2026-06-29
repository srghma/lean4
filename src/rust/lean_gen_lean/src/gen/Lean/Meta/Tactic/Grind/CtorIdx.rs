// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CtorIdx
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Constructions.CtorIdx Lean.Meta.CtorIdxHInj
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Environment::l_Lean_Environment_containsOnBranch;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_appFn_x21, l_Lean_Expr_constLevels_x21, l_Lean_Expr_constName_x3f,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isAppOfArity,
    l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr, l_Lean_mkAppN, l_Lean_mkConst,
    l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkCongrArg, l_Lean_Meta_mkEq, l_Lean_Meta_mkExpectedPropHint,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_whnfD;
use crate::r#gen::Lean::Meta::Constructions::CtorIdx::{
    initialize_Lean_Meta_Constructions_CtorIdx, l_isCtorIdx_x3f___redArg,
    runtime_initialize_Lean_Meta_Constructions_CtorIdx,
};
use crate::r#gen::Lean::Meta::CtorIdxHInj::{
    initialize_Lean_Meta_CtorIdxHInj, l_Lean_Meta_mkCtorIdxHInjTheoremNameFor,
    runtime_initialize_Lean_Meta_CtorIdxHInj,
};
use crate::r#gen::Lean::Meta::CtorRecognizer::l_Lean_Meta_isConstructorApp_x3f;
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_addNewRawFact,
    l_Lean_Meta_Grind_getGeneration___redArg, l_Lean_Meta_Grind_getRootENode___redArg,
    l_Lean_Meta_Grind_hasSameType, l_Lean_Meta_Grind_instInhabitedGoalM,
    l_Lean_Meta_Grind_pushEqCore___redArg, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::ReservedNameAction::l_Lean_executeReservedNameAction;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_sub, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::{
    lean_grind_internalize, lean_grind_mk_eq_proof,
};
static mut l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1_value: crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 67, 116, 111, 114, 73, 100, 120, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 112, 114, 111, 112, 97, 103, 97, 116, 101, 67, 116, 111, 114, 73, 100, 120, 85, 112, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3_value: crate::leanh::LeanStringObject<162> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 162, m_capacity: 162, m_length: 161, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 97, 84, 121, 112, 101, 46, 105, 115, 65, 112, 112, 79, 102, 65, 114, 105, 116, 121, 32, 105, 110, 100, 73, 110, 102, 111, 46, 110, 97, 109, 101, 32, 40, 105, 110, 100, 73, 110, 102, 111, 46, 110, 117, 109, 80, 97, 114, 97, 109, 115, 32, 43, 32, 105, 110, 100, 73, 110, 102, 111, 46, 110, 117, 109, 73, 110, 100, 105, 99, 101, 115, 41, 10, 32, 32, 32, 32, 32, 32, 45, 45, 32, 98, 111, 116, 104, 32, 116, 121, 112, 101, 115, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 104, 101, 97, 100, 101, 100, 32, 98, 121, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 116, 121, 112, 101, 32, 102, 111, 114, 109, 101, 114, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_406_ = l_Lean_Meta_Grind_instInhabitedGoalM(crate::leanh::lean_box(0));
    return v___x_406_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(
    mut v_msg_407_: *mut crate::leanh::LeanObject,
    mut v___y_408_: *mut crate::leanh::LeanObject,
    mut v___y_409_: *mut crate::leanh::LeanObject,
    mut v___y_410_: *mut crate::leanh::LeanObject,
    mut v___y_411_: *mut crate::leanh::LeanObject,
    mut v___y_412_: *mut crate::leanh::LeanObject,
    mut v___y_413_: *mut crate::leanh::LeanObject,
    mut v___y_414_: *mut crate::leanh::LeanObject,
    mut v___y_415_: *mut crate::leanh::LeanObject,
    mut v___y_416_: *mut crate::leanh::LeanObject,
    mut v___y_417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_63942__overap_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_419_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0,
    );
    v___x_63942__overap_420_ = lean_panic_fn_borrowed(v___x_419_, v_msg_407_);
    crate::leanh::lean_inc(v___y_417_);
    crate::leanh::lean_inc_ref(v___y_416_);
    crate::leanh::lean_inc(v___y_415_);
    crate::leanh::lean_inc_ref(v___y_414_);
    crate::leanh::lean_inc(v___y_413_);
    crate::leanh::lean_inc_ref(v___y_412_);
    crate::leanh::lean_inc(v___y_411_);
    crate::leanh::lean_inc_ref(v___y_410_);
    crate::leanh::lean_inc(v___y_409_);
    crate::leanh::lean_inc(v___y_408_);
    v___x_421_ = crate::leanh::lean_apply_11(
        v___x_63942__overap_420_,
        v___y_408_,
        v___y_409_,
        v___y_410_,
        v___y_411_,
        v___y_412_,
        v___y_413_,
        v___y_414_,
        v___y_415_,
        v___y_416_,
        v___y_417_,
        crate::leanh::lean_box(0),
    );
    return v___x_421_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___boxed(
    mut v_msg_422_: *mut crate::leanh::LeanObject,
    mut v___y_423_: *mut crate::leanh::LeanObject,
    mut v___y_424_: *mut crate::leanh::LeanObject,
    mut v___y_425_: *mut crate::leanh::LeanObject,
    mut v___y_426_: *mut crate::leanh::LeanObject,
    mut v___y_427_: *mut crate::leanh::LeanObject,
    mut v___y_428_: *mut crate::leanh::LeanObject,
    mut v___y_429_: *mut crate::leanh::LeanObject,
    mut v___y_430_: *mut crate::leanh::LeanObject,
    mut v___y_431_: *mut crate::leanh::LeanObject,
    mut v___y_432_: *mut crate::leanh::LeanObject,
    mut v___y_433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_434_ = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(
        v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_,
        v___y_429_, v___y_430_, v___y_431_, v___y_432_,
    );
    crate::leanh::lean_dec(v___y_432_);
    crate::leanh::lean_dec_ref(v___y_431_);
    crate::leanh::lean_dec(v___y_430_);
    crate::leanh::lean_dec_ref(v___y_429_);
    crate::leanh::lean_dec(v___y_428_);
    crate::leanh::lean_dec_ref(v___y_427_);
    crate::leanh::lean_dec(v___y_426_);
    crate::leanh::lean_dec_ref(v___y_425_);
    crate::leanh::lean_dec(v___y_424_);
    crate::leanh::lean_dec(v___y_423_);
    return v_res_434_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_435_ = crate::leanh::lean_box(0);
    v_dummy_436_ = l_Lean_Expr_sort___override(v___x_435_);
    return v_dummy_436_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_440_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3;
    v___x_441_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_442_ = crate::leanh::lean_unsigned_to_nat(37);
    v___x_443_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2;
    v___x_444_ =
        l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1;
    v___x_445_ =
        l_mkPanicMessageWithDecl(v___x_444_, v___x_443_, v___x_442_, v___x_441_, v___x_440_);
    return v___x_445_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(
    mut v_e_446_: *mut crate::leanh::LeanObject,
    mut v_x_447_: *mut crate::leanh::LeanObject,
    mut v_x_448_: *mut crate::leanh::LeanObject,
    mut v_x_449_: *mut crate::leanh::LeanObject,
    mut v___y_450_: *mut crate::leanh::LeanObject,
    mut v___y_451_: *mut crate::leanh::LeanObject,
    mut v___y_452_: *mut crate::leanh::LeanObject,
    mut v___y_453_: *mut crate::leanh::LeanObject,
    mut v___y_454_: *mut crate::leanh::LeanObject,
    mut v___y_455_: *mut crate::leanh::LeanObject,
    mut v___y_456_: *mut crate::leanh::LeanObject,
    mut v___y_457_: *mut crate::leanh::LeanObject,
    mut v___y_458_: *mut crate::leanh::LeanObject,
    mut v___y_459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_471_: u8 = 0;
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_476_: u8 = 0;
    let mut v_val_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_480_: u8 = 0;
    let mut v_toConstantVal_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: u8 = 0;
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v_self_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctor_502_: u8 = 0;
    let mut v_heqProofs_503_: u8 = 0;
    let mut v___y_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_544_: u8 = 0;
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_549_: u8 = 0;
    let mut v_unused_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_556_: u8 = 0;
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_560_: u8 = 0;
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_569_: u8 = 0;
    let mut v_val_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: u8 = 0;
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_602_: u8 = 0;
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_606_: u8 = 0;
    let mut v_a_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_610_: u8 = 0;
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_614_: u8 = 0;
    let mut v_a_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_618_: u8 = 0;
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_622_: u8 = 0;
    let mut v_a_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_626_: u8 = 0;
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_630_: u8 = 0;
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: u8 = 0;
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_650_: u8 = 0;
    let mut v_name_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: u8 = 0;
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: u8 = 0;
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: u8 = 0;
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_667_: u8 = 0;
    let mut v_a_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_671_: u8 = 0;
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_675_: u8 = 0;
    let mut v_a_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_679_: u8 = 0;
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_683_: u8 = 0;
    let mut v_a_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_687_: u8 = 0;
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_691_: u8 = 0;
    let mut v_a_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_695_: u8 = 0;
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_699_: u8 = 0;
    let mut v___x_700_: u8 = 0;
    let mut v_a_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_704_: u8 = 0;
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_708_: u8 = 0;
    let mut v_a_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_712_: u8 = 0;
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_716_: u8 = 0;
    let mut v_a_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_720_: u8 = 0;
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_724_: u8 = 0;
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_729_: u8 = 0;
    let mut v_a_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_733_: u8 = 0;
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_737_: u8 = 0;
    let mut v_isSharedCheck_738_: u8 = 0;
    let mut v_a_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_742_: u8 = 0;
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_746_: u8 = 0;
    let mut v_isSharedCheck_747_: u8 = 0;
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_752_: u8 = 0;
    let mut v_a_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_756_: u8 = 0;
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_760_: u8 = 0;
    let mut v_isSharedCheck_761_: u8 = 0;
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_447_) == 5 {
                    v_fn_461_ = crate::leanh::lean_ctor_get(v_x_447_, 0);
                    crate::leanh::lean_inc_ref(v_fn_461_);
                    v_arg_462_ = crate::leanh::lean_ctor_get(v_x_447_, 1);
                    crate::leanh::lean_inc_ref(v_arg_462_);
                    crate::leanh::lean_dec_ref_known(v_x_447_, 2);
                    v___x_463_ = lean_array_set(v_x_448_, v_x_449_, v_arg_462_);
                    v___x_464_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_465_ = lean_nat_sub(v_x_449_, v___x_464_);
                    crate::leanh::lean_dec(v_x_449_);
                    v_x_447_ = v_fn_461_;
                    v_x_448_ = v___x_463_;
                    v_x_449_ = v___x_465_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_449_);
                    v___x_467_ = l_Lean_Expr_constName_x3f(v_x_447_);
                    crate::leanh::lean_dec_ref(v_x_447_);
                    if crate::leanh::lean_obj_tag(v___x_467_) == 1 {
                        v_val_468_ = crate::leanh::lean_ctor_get(v___x_467_, 0);
                        v_isSharedCheck_761_ = (!crate::leanh::lean_is_exclusive(v___x_467_)) as u8;
                        if v_isSharedCheck_761_ == 0 {
                            v___x_470_ = v___x_467_;
                            v_isShared_471_ = v_isSharedCheck_761_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_468_);
                            crate::leanh::lean_dec(v___x_467_);
                            v___x_470_ = crate::leanh::lean_box(0);
                            v_isShared_471_ = v_isSharedCheck_761_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_467_);
                        crate::leanh::lean_dec_ref(v_x_448_);
                        crate::leanh::lean_dec_ref(v_e_446_);
                        v___x_762_ = crate::leanh::lean_box(0);
                        v___x_763_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_763_, 0, v___x_762_);
                        return v___x_763_;
                    }
                }
            }
            1 => {
                v___x_472_ = l_isCtorIdx_x3f___redArg(v_val_468_, v___y_459_);
                if crate::leanh::lean_obj_tag(v___x_472_) == 0 {
                    v_a_473_ = crate::leanh::lean_ctor_get(v___x_472_, 0);
                    v_isSharedCheck_752_ = (!crate::leanh::lean_is_exclusive(v___x_472_)) as u8;
                    if v_isSharedCheck_752_ == 0 {
                        v___x_475_ = v___x_472_;
                        v_isShared_476_ = v_isSharedCheck_752_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_473_);
                        crate::leanh::lean_dec(v___x_472_);
                        v___x_475_ = crate::leanh::lean_box(0);
                        v_isShared_476_ = v_isSharedCheck_752_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_470_);
                    crate::leanh::lean_dec_ref(v_x_448_);
                    crate::leanh::lean_dec_ref(v_e_446_);
                    v_a_753_ = crate::leanh::lean_ctor_get(v___x_472_, 0);
                    v_isSharedCheck_760_ = (!crate::leanh::lean_is_exclusive(v___x_472_)) as u8;
                    if v_isSharedCheck_760_ == 0 {
                        v___x_755_ = v___x_472_;
                        v_isShared_756_ = v_isSharedCheck_760_;
                        state = 47;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_753_);
                        crate::leanh::lean_dec(v___x_472_);
                        v___x_755_ = crate::leanh::lean_box(0);
                        v_isShared_756_ = v_isSharedCheck_760_;
                        state = 47;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_473_) == 1 {
                    v_val_477_ = crate::leanh::lean_ctor_get(v_a_473_, 0);
                    v_isSharedCheck_747_ = (!crate::leanh::lean_is_exclusive(v_a_473_)) as u8;
                    if v_isSharedCheck_747_ == 0 {
                        v___x_479_ = v_a_473_;
                        v_isShared_480_ = v_isSharedCheck_747_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_477_);
                        crate::leanh::lean_dec(v_a_473_);
                        v___x_479_ = crate::leanh::lean_box(0);
                        v_isShared_480_ = v_isSharedCheck_747_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_473_);
                    crate::leanh::lean_del_object(v___x_470_);
                    crate::leanh::lean_dec_ref(v_x_448_);
                    crate::leanh::lean_dec_ref(v_e_446_);
                    v___x_748_ = crate::leanh::lean_box(0);
                    if v_isShared_476_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_475_, 0, v___x_748_);
                        v___x_750_ = v___x_475_;
                        state = 46;
                        continue;
                    } else {
                        v_reuseFailAlloc_751_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
                        v___x_750_ = v_reuseFailAlloc_751_;
                        state = 46;
                        continue;
                    }
                }
            }
            3 => {
                v_toConstantVal_481_ = crate::leanh::lean_ctor_get(v_val_477_, 0);
                crate::leanh::lean_inc_ref(v_toConstantVal_481_);
                v_numParams_482_ = crate::leanh::lean_ctor_get(v_val_477_, 1);
                crate::leanh::lean_inc(v_numParams_482_);
                v_numIndices_483_ = crate::leanh::lean_ctor_get(v_val_477_, 2);
                crate::leanh::lean_inc(v_numIndices_483_);
                crate::leanh::lean_dec(v_val_477_);
                v___x_484_ = lean_array_get_size(v_x_448_);
                v___x_485_ = lean_nat_add(v_numParams_482_, v_numIndices_483_);
                crate::leanh::lean_dec(v_numIndices_483_);
                crate::leanh::lean_dec(v_numParams_482_);
                v___x_486_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_487_ = lean_nat_add(v___x_485_, v___x_486_);
                v___x_488_ = lean_nat_dec_eq(v___x_484_, v___x_487_);
                crate::leanh::lean_dec(v___x_487_);
                if v___x_488_ == 0 {
                    crate::leanh::lean_dec(v___x_485_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                    crate::leanh::lean_del_object(v___x_479_);
                    crate::leanh::lean_del_object(v___x_470_);
                    crate::leanh::lean_dec_ref(v_x_448_);
                    crate::leanh::lean_dec_ref(v_e_446_);
                    v___x_489_ = crate::leanh::lean_box(0);
                    if v_isShared_476_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_475_, 0, v___x_489_);
                        v___x_491_ = v___x_475_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_492_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
                        v___x_491_ = v_reuseFailAlloc_492_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_475_);
                    v___x_493_ = l_Lean_instInhabitedExpr;
                    v___x_494_ = lean_nat_sub(v___x_484_, v___x_486_);
                    v___x_495_ = lean_array_get(v___x_493_, v_x_448_, v___x_494_);
                    crate::leanh::lean_dec(v___x_494_);
                    crate::leanh::lean_dec_ref(v_x_448_);
                    crate::leanh::lean_inc(v___x_495_);
                    v___x_496_ = l_Lean_Meta_Grind_getRootENode___redArg(
                        v___x_495_, v___y_450_, v___y_456_, v___y_457_, v___y_458_, v___y_459_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_496_) == 0 {
                        v_a_497_ = crate::leanh::lean_ctor_get(v___x_496_, 0);
                        v_isSharedCheck_738_ = (!crate::leanh::lean_is_exclusive(v___x_496_)) as u8;
                        if v_isSharedCheck_738_ == 0 {
                            v___x_499_ = v___x_496_;
                            v_isShared_500_ = v_isSharedCheck_738_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_497_);
                            crate::leanh::lean_dec(v___x_496_);
                            v___x_499_ = crate::leanh::lean_box(0);
                            v_isShared_500_ = v_isSharedCheck_738_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_495_);
                        crate::leanh::lean_dec(v___x_485_);
                        crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                        crate::leanh::lean_del_object(v___x_479_);
                        crate::leanh::lean_del_object(v___x_470_);
                        crate::leanh::lean_dec_ref(v_e_446_);
                        v_a_739_ = crate::leanh::lean_ctor_get(v___x_496_, 0);
                        v_isSharedCheck_746_ = (!crate::leanh::lean_is_exclusive(v___x_496_)) as u8;
                        if v_isSharedCheck_746_ == 0 {
                            v___x_741_ = v___x_496_;
                            v_isShared_742_ = v_isSharedCheck_746_;
                            state = 44;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_739_);
                            crate::leanh::lean_dec(v___x_496_);
                            v___x_741_ = crate::leanh::lean_box(0);
                            v_isShared_742_ = v_isSharedCheck_746_;
                            state = 44;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_491_;
            }
            5 => {
                v_self_501_ = crate::leanh::lean_ctor_get(v_a_497_, 0);
                crate::leanh::lean_inc_ref(v_self_501_);
                v_ctor_502_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_497_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 12 + 2) as u32,
                );
                v_heqProofs_503_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_497_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 12 + 4) as u32,
                );
                crate::leanh::lean_dec(v_a_497_);
                if v_ctor_502_ == 0 {
                    crate::leanh::lean_dec_ref(v_self_501_);
                    crate::leanh::lean_dec(v___x_495_);
                    crate::leanh::lean_dec(v___x_485_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                    crate::leanh::lean_del_object(v___x_479_);
                    crate::leanh::lean_del_object(v___x_470_);
                    crate::leanh::lean_dec_ref(v_e_446_);
                    v___x_561_ = crate::leanh::lean_box(0);
                    if v_isShared_500_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_499_, 0, v___x_561_);
                        v___x_563_ = v___x_499_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
                        v___x_563_ = v_reuseFailAlloc_564_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_499_);
                    crate::leanh::lean_inc_ref(v_self_501_);
                    v___x_565_ = l_Lean_Meta_isConstructorApp_x3f(
                        v_self_501_,
                        v___y_456_,
                        v___y_457_,
                        v___y_458_,
                        v___y_459_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_565_) == 0 {
                        v_a_566_ = crate::leanh::lean_ctor_get(v___x_565_, 0);
                        v_isSharedCheck_729_ = (!crate::leanh::lean_is_exclusive(v___x_565_)) as u8;
                        if v_isSharedCheck_729_ == 0 {
                            v___x_568_ = v___x_565_;
                            v_isShared_569_ = v_isSharedCheck_729_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_566_);
                            crate::leanh::lean_dec(v___x_565_);
                            v___x_568_ = crate::leanh::lean_box(0);
                            v_isShared_569_ = v_isSharedCheck_729_;
                            state = 14;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_self_501_);
                        crate::leanh::lean_dec(v___x_495_);
                        crate::leanh::lean_dec(v___x_485_);
                        crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                        crate::leanh::lean_del_object(v___x_479_);
                        crate::leanh::lean_del_object(v___x_470_);
                        crate::leanh::lean_dec_ref(v_e_446_);
                        v_a_730_ = crate::leanh::lean_ctor_get(v___x_565_, 0);
                        v_isSharedCheck_737_ = (!crate::leanh::lean_is_exclusive(v___x_565_)) as u8;
                        if v_isSharedCheck_737_ == 0 {
                            v___x_732_ = v___x_565_;
                            v_isShared_733_ = v_isSharedCheck_737_;
                            state = 42;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_730_);
                            crate::leanh::lean_dec(v___x_565_);
                            v___x_732_ = crate::leanh::lean_box(0);
                            v_isShared_733_ = v_isSharedCheck_737_;
                            state = 42;
                            continue;
                        }
                    }
                }
            }
            6 => {
                crate::leanh::lean_inc(v___y_506_);
                v___x_520_ = l_Lean_mkConst(v___y_506_, v___y_509_);
                v_dummy_521_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
                v_nargs_522_ = l_Lean_Expr_getAppNumArgs(v___y_508_);
                crate::leanh::lean_inc(v_nargs_522_);
                v___x_523_ = lean_mk_array(v_nargs_522_, v_dummy_521_);
                v___x_524_ = lean_nat_sub(v_nargs_522_, v___x_486_);
                crate::leanh::lean_dec(v_nargs_522_);
                v___x_525_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v___y_508_, v___x_523_, v___x_524_,
                );
                v___x_526_ = l_Lean_mkAppN(v___x_520_, v___x_525_);
                crate::leanh::lean_dec_ref(v___x_525_);
                v___x_527_ = l_Lean_Expr_app___override(v___x_526_, v___x_495_);
                v_nargs_528_ = l_Lean_Expr_getAppNumArgs(v___y_507_);
                crate::leanh::lean_inc(v_nargs_528_);
                v___x_529_ = lean_mk_array(v_nargs_528_, v_dummy_521_);
                v___x_530_ = lean_nat_sub(v_nargs_528_, v___x_486_);
                crate::leanh::lean_dec(v_nargs_528_);
                v___x_531_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v___y_507_, v___x_529_, v___x_530_,
                );
                v___x_532_ = l_Lean_mkAppN(v___x_527_, v___x_531_);
                crate::leanh::lean_dec_ref(v___x_531_);
                v___x_533_ = l_Lean_Expr_app___override(v___x_532_, v_self_501_);
                crate::leanh::lean_inc(v___y_519_);
                crate::leanh::lean_inc_ref(v___y_518_);
                crate::leanh::lean_inc(v___y_517_);
                crate::leanh::lean_inc_ref(v___y_516_);
                crate::leanh::lean_inc_ref(v___x_533_);
                v___x_534_ =
                    lean_infer_type(v___x_533_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
                if crate::leanh::lean_obj_tag(v___x_534_) == 0 {
                    v_a_535_ = crate::leanh::lean_ctor_get(v___x_534_, 0);
                    crate::leanh::lean_inc(v_a_535_);
                    crate::leanh::lean_dec_ref_known(v___x_534_, 1);
                    if v_isShared_480_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_479_, 0);
                        crate::leanh::lean_ctor_set(v___x_479_, 0, v___y_506_);
                        v___x_537_ = v___x_479_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_552_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_552_, 0, v___y_506_);
                        v___x_537_ = v_reuseFailAlloc_552_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_533_);
                    crate::leanh::lean_dec(v___y_506_);
                    crate::leanh::lean_dec(v___y_505_);
                    crate::leanh::lean_del_object(v___x_479_);
                    crate::leanh::lean_del_object(v___x_470_);
                    v_a_553_ = crate::leanh::lean_ctor_get(v___x_534_, 0);
                    v_isSharedCheck_560_ = (!crate::leanh::lean_is_exclusive(v___x_534_)) as u8;
                    if v_isSharedCheck_560_ == 0 {
                        v___x_555_ = v___x_534_;
                        v_isShared_556_ = v_isSharedCheck_560_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_553_);
                        crate::leanh::lean_dec(v___x_534_);
                        v___x_555_ = crate::leanh::lean_box(0);
                        v_isShared_556_ = v_isSharedCheck_560_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_471_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_470_, 7);
                    crate::leanh::lean_ctor_set(v___x_470_, 0, v___x_537_);
                    v___x_539_ = v___x_470_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_551_ = crate::leanh::lean_alloc_ctor(7, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_537_);
                    v___x_539_ = v_reuseFailAlloc_551_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_540_ = crate::leanh::lean_box(1);
                v___x_541_ = l_Lean_Meta_Grind_addNewRawFact(
                    v___x_533_, v_a_535_, v___y_505_, v___x_539_, v___x_540_, v___y_510_,
                    v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_,
                    v___y_517_, v___y_518_, v___y_519_,
                );
                if crate::leanh::lean_obj_tag(v___x_541_) == 0 {
                    v_isSharedCheck_549_ = (!crate::leanh::lean_is_exclusive(v___x_541_)) as u8;
                    if v_isSharedCheck_549_ == 0 {
                        v_unused_550_ = crate::leanh::lean_ctor_get(v___x_541_, 0);
                        crate::leanh::lean_dec(v_unused_550_);
                        v___x_543_ = v___x_541_;
                        v_isShared_544_ = v_isSharedCheck_549_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_541_);
                        v___x_543_ = crate::leanh::lean_box(0);
                        v_isShared_544_ = v_isSharedCheck_549_;
                        state = 9;
                        continue;
                    }
                } else {
                    return v___x_541_;
                }
            }
            9 => {
                v___x_545_ = crate::leanh::lean_box(0);
                if v_isShared_544_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_543_, 0, v___x_545_);
                    v___x_547_ = v___x_543_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_548_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
                    v___x_547_ = v_reuseFailAlloc_548_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_547_;
            }
            11 => {
                if v_isShared_556_ == 0 {
                    v___x_558_ = v___x_555_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_559_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
                    v___x_558_ = v_reuseFailAlloc_559_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_558_;
            }
            13 => {
                return v___x_563_;
            }
            14 => {
                if crate::leanh::lean_obj_tag(v_a_566_) == 1 {
                    crate::leanh::lean_del_object(v___x_568_);
                    v_val_570_ = crate::leanh::lean_ctor_get(v_a_566_, 0);
                    crate::leanh::lean_inc(v_val_570_);
                    crate::leanh::lean_dec_ref_known(v_a_566_, 1);
                    if v_heqProofs_503_ == 0 {
                        crate::leanh::lean_dec(v___x_485_);
                        crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                        crate::leanh::lean_del_object(v___x_479_);
                        crate::leanh::lean_del_object(v___x_470_);
                        v___y_572_ = v___y_450_;
                        v___y_573_ = v___y_451_;
                        v___y_574_ = v___y_452_;
                        v___y_575_ = v___y_453_;
                        v___y_576_ = v___y_454_;
                        v___y_577_ = v___y_455_;
                        v___y_578_ = v___y_456_;
                        v___y_579_ = v___y_457_;
                        v___y_580_ = v___y_458_;
                        v___y_581_ = v___y_459_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_self_501_);
                        crate::leanh::lean_inc(v___x_495_);
                        v___x_631_ = l_Lean_Meta_Grind_hasSameType(
                            v___x_495_,
                            v_self_501_,
                            v___y_456_,
                            v___y_457_,
                            v___y_458_,
                            v___y_459_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_631_) == 0 {
                            v_a_632_ = crate::leanh::lean_ctor_get(v___x_631_, 0);
                            crate::leanh::lean_inc(v_a_632_);
                            crate::leanh::lean_dec_ref_known(v___x_631_, 1);
                            v___x_633_ = (crate::leanh::lean_unbox(v_a_632_) as u8);
                            crate::leanh::lean_dec(v_a_632_);
                            if v___x_633_ == 0 {
                                crate::leanh::lean_dec(v_val_570_);
                                crate::leanh::lean_dec_ref(v_e_446_);
                                v___x_634_ = l_Lean_Meta_Grind_getGeneration___redArg(
                                    v___x_495_, v___y_450_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_634_) == 0 {
                                    v_a_635_ = crate::leanh::lean_ctor_get(v___x_634_, 0);
                                    crate::leanh::lean_inc(v_a_635_);
                                    crate::leanh::lean_dec_ref_known(v___x_634_, 1);
                                    v___x_636_ = l_Lean_Meta_Grind_getGeneration___redArg(
                                        v_self_501_,
                                        v___y_450_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_636_) == 0 {
                                        v_a_637_ = crate::leanh::lean_ctor_get(v___x_636_, 0);
                                        crate::leanh::lean_inc(v_a_637_);
                                        crate::leanh::lean_dec_ref_known(v___x_636_, 1);
                                        v___x_700_ = lean_nat_dec_le(v_a_635_, v_a_637_);
                                        if v___x_700_ == 0 {
                                            crate::leanh::lean_dec(v_a_637_);
                                            v___y_639_ = v_a_635_;
                                            state = 24;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_a_635_);
                                            v___y_639_ = v_a_637_;
                                            state = 24;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_635_);
                                        crate::leanh::lean_dec_ref(v_self_501_);
                                        crate::leanh::lean_dec(v___x_495_);
                                        crate::leanh::lean_dec(v___x_485_);
                                        crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                                        crate::leanh::lean_del_object(v___x_479_);
                                        crate::leanh::lean_del_object(v___x_470_);
                                        v_a_701_ = crate::leanh::lean_ctor_get(v___x_636_, 0);
                                        v_isSharedCheck_708_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_636_)) as u8;
                                        if v_isSharedCheck_708_ == 0 {
                                            v___x_703_ = v___x_636_;
                                            v_isShared_704_ = v_isSharedCheck_708_;
                                            state = 35;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_701_);
                                            crate::leanh::lean_dec(v___x_636_);
                                            v___x_703_ = crate::leanh::lean_box(0);
                                            v_isShared_704_ = v_isSharedCheck_708_;
                                            state = 35;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_self_501_);
                                    crate::leanh::lean_dec(v___x_495_);
                                    crate::leanh::lean_dec(v___x_485_);
                                    crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                                    crate::leanh::lean_del_object(v___x_479_);
                                    crate::leanh::lean_del_object(v___x_470_);
                                    v_a_709_ = crate::leanh::lean_ctor_get(v___x_634_, 0);
                                    v_isSharedCheck_716_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_634_)) as u8;
                                    if v_isSharedCheck_716_ == 0 {
                                        v___x_711_ = v___x_634_;
                                        v_isShared_712_ = v_isSharedCheck_716_;
                                        state = 37;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_709_);
                                        crate::leanh::lean_dec(v___x_634_);
                                        v___x_711_ = crate::leanh::lean_box(0);
                                        v_isShared_712_ = v_isSharedCheck_716_;
                                        state = 37;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_485_);
                                crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                                crate::leanh::lean_del_object(v___x_479_);
                                crate::leanh::lean_del_object(v___x_470_);
                                v___y_572_ = v___y_450_;
                                v___y_573_ = v___y_451_;
                                v___y_574_ = v___y_452_;
                                v___y_575_ = v___y_453_;
                                v___y_576_ = v___y_454_;
                                v___y_577_ = v___y_455_;
                                v___y_578_ = v___y_456_;
                                v___y_579_ = v___y_457_;
                                v___y_580_ = v___y_458_;
                                v___y_581_ = v___y_459_;
                                state = 15;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_570_);
                            crate::leanh::lean_dec_ref(v_self_501_);
                            crate::leanh::lean_dec(v___x_495_);
                            crate::leanh::lean_dec(v___x_485_);
                            crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                            crate::leanh::lean_del_object(v___x_479_);
                            crate::leanh::lean_del_object(v___x_470_);
                            crate::leanh::lean_dec_ref(v_e_446_);
                            v_a_717_ = crate::leanh::lean_ctor_get(v___x_631_, 0);
                            v_isSharedCheck_724_ =
                                (!crate::leanh::lean_is_exclusive(v___x_631_)) as u8;
                            if v_isSharedCheck_724_ == 0 {
                                v___x_719_ = v___x_631_;
                                v_isShared_720_ = v_isSharedCheck_724_;
                                state = 39;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_717_);
                                crate::leanh::lean_dec(v___x_631_);
                                v___x_719_ = crate::leanh::lean_box(0);
                                v_isShared_720_ = v_isSharedCheck_724_;
                                state = 39;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_566_);
                    crate::leanh::lean_dec_ref(v_self_501_);
                    crate::leanh::lean_dec(v___x_495_);
                    crate::leanh::lean_dec(v___x_485_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                    crate::leanh::lean_del_object(v___x_479_);
                    crate::leanh::lean_del_object(v___x_470_);
                    crate::leanh::lean_dec_ref(v_e_446_);
                    v___x_725_ = crate::leanh::lean_box(0);
                    if v_isShared_569_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_568_, 0, v___x_725_);
                        v___x_727_ = v___x_568_;
                        state = 41;
                        continue;
                    } else {
                        v_reuseFailAlloc_728_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
                        v___x_727_ = v_reuseFailAlloc_728_;
                        state = 41;
                        continue;
                    }
                }
            }
            15 => {
                v_cidx_582_ = crate::leanh::lean_ctor_get(v_val_570_, 2);
                crate::leanh::lean_inc(v_cidx_582_);
                crate::leanh::lean_dec(v_val_570_);
                v___x_583_ = l_Lean_mkNatLit(v_cidx_582_);
                v___x_584_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_583_, v___y_577_);
                if crate::leanh::lean_obj_tag(v___x_584_) == 0 {
                    v_a_585_ = crate::leanh::lean_ctor_get(v___x_584_, 0);
                    crate::leanh::lean_inc_n(v_a_585_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_584_, 1);
                    v___x_586_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_587_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___y_581_);
                    crate::leanh::lean_inc_ref(v___y_580_);
                    crate::leanh::lean_inc(v___y_579_);
                    crate::leanh::lean_inc_ref(v___y_578_);
                    crate::leanh::lean_inc(v___y_577_);
                    crate::leanh::lean_inc_ref(v___y_576_);
                    crate::leanh::lean_inc(v___y_575_);
                    crate::leanh::lean_inc_ref(v___y_574_);
                    crate::leanh::lean_inc(v___y_573_);
                    crate::leanh::lean_inc(v___y_572_);
                    v___x_588_ = lean_grind_internalize(
                        v_a_585_, v___x_586_, v___x_587_, v___y_572_, v___y_573_, v___y_574_,
                        v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_,
                        v___y_581_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_588_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_588_, 1);
                        crate::leanh::lean_inc(v___y_581_);
                        crate::leanh::lean_inc_ref(v___y_580_);
                        crate::leanh::lean_inc(v___y_579_);
                        crate::leanh::lean_inc_ref(v___y_578_);
                        crate::leanh::lean_inc(v___y_577_);
                        crate::leanh::lean_inc_ref(v___y_576_);
                        crate::leanh::lean_inc(v___y_575_);
                        crate::leanh::lean_inc_ref(v___y_574_);
                        crate::leanh::lean_inc(v___y_573_);
                        crate::leanh::lean_inc(v___y_572_);
                        v___x_589_ = lean_grind_mk_eq_proof(
                            v___x_495_,
                            v_self_501_,
                            v___y_572_,
                            v___y_573_,
                            v___y_574_,
                            v___y_575_,
                            v___y_576_,
                            v___y_577_,
                            v___y_578_,
                            v___y_579_,
                            v___y_580_,
                            v___y_581_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_589_) == 0 {
                            v_a_590_ = crate::leanh::lean_ctor_get(v___x_589_, 0);
                            crate::leanh::lean_inc(v_a_590_);
                            crate::leanh::lean_dec_ref_known(v___x_589_, 1);
                            v___x_591_ = l_Lean_Expr_appFn_x21(v_e_446_);
                            v___x_592_ = l_Lean_Meta_mkCongrArg(
                                v___x_591_, v_a_590_, v___y_578_, v___y_579_, v___y_580_,
                                v___y_581_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_592_) == 0 {
                                v_a_593_ = crate::leanh::lean_ctor_get(v___x_592_, 0);
                                crate::leanh::lean_inc(v_a_593_);
                                crate::leanh::lean_dec_ref_known(v___x_592_, 1);
                                crate::leanh::lean_inc(v_a_585_);
                                crate::leanh::lean_inc_ref(v_e_446_);
                                v___x_594_ = l_Lean_Meta_mkEq(
                                    v_e_446_, v_a_585_, v___y_578_, v___y_579_, v___y_580_,
                                    v___y_581_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_594_) == 0 {
                                    v_a_595_ = crate::leanh::lean_ctor_get(v___x_594_, 0);
                                    crate::leanh::lean_inc(v_a_595_);
                                    crate::leanh::lean_dec_ref_known(v___x_594_, 1);
                                    v___x_596_ = l_Lean_Meta_mkExpectedPropHint(v_a_593_, v_a_595_);
                                    v___x_597_ = 0;
                                    v___x_598_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                                        v_e_446_, v_a_585_, v___x_596_, v___x_597_, v___y_572_,
                                        v___y_574_, v___y_578_, v___y_579_, v___y_580_, v___y_581_,
                                    );
                                    return v___x_598_;
                                } else {
                                    crate::leanh::lean_dec(v_a_593_);
                                    crate::leanh::lean_dec(v_a_585_);
                                    crate::leanh::lean_dec_ref(v_e_446_);
                                    v_a_599_ = crate::leanh::lean_ctor_get(v___x_594_, 0);
                                    v_isSharedCheck_606_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_594_)) as u8;
                                    if v_isSharedCheck_606_ == 0 {
                                        v___x_601_ = v___x_594_;
                                        v_isShared_602_ = v_isSharedCheck_606_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_599_);
                                        crate::leanh::lean_dec(v___x_594_);
                                        v___x_601_ = crate::leanh::lean_box(0);
                                        v_isShared_602_ = v_isSharedCheck_606_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_585_);
                                crate::leanh::lean_dec_ref(v_e_446_);
                                v_a_607_ = crate::leanh::lean_ctor_get(v___x_592_, 0);
                                v_isSharedCheck_614_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_592_)) as u8;
                                if v_isSharedCheck_614_ == 0 {
                                    v___x_609_ = v___x_592_;
                                    v_isShared_610_ = v_isSharedCheck_614_;
                                    state = 18;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_607_);
                                    crate::leanh::lean_dec(v___x_592_);
                                    v___x_609_ = crate::leanh::lean_box(0);
                                    v_isShared_610_ = v_isSharedCheck_614_;
                                    state = 18;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_585_);
                            crate::leanh::lean_dec_ref(v_e_446_);
                            v_a_615_ = crate::leanh::lean_ctor_get(v___x_589_, 0);
                            v_isSharedCheck_622_ =
                                (!crate::leanh::lean_is_exclusive(v___x_589_)) as u8;
                            if v_isSharedCheck_622_ == 0 {
                                v___x_617_ = v___x_589_;
                                v_isShared_618_ = v_isSharedCheck_622_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_615_);
                                crate::leanh::lean_dec(v___x_589_);
                                v___x_617_ = crate::leanh::lean_box(0);
                                v_isShared_618_ = v_isSharedCheck_622_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_585_);
                        crate::leanh::lean_dec_ref(v_self_501_);
                        crate::leanh::lean_dec(v___x_495_);
                        crate::leanh::lean_dec_ref(v_e_446_);
                        return v___x_588_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_self_501_);
                    crate::leanh::lean_dec(v___x_495_);
                    crate::leanh::lean_dec_ref(v_e_446_);
                    v_a_623_ = crate::leanh::lean_ctor_get(v___x_584_, 0);
                    v_isSharedCheck_630_ = (!crate::leanh::lean_is_exclusive(v___x_584_)) as u8;
                    if v_isSharedCheck_630_ == 0 {
                        v___x_625_ = v___x_584_;
                        v_isShared_626_ = v_isSharedCheck_630_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_623_);
                        crate::leanh::lean_dec(v___x_584_);
                        v___x_625_ = crate::leanh::lean_box(0);
                        v_isShared_626_ = v_isSharedCheck_630_;
                        state = 22;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_602_ == 0 {
                    v___x_604_ = v___x_601_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_605_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
                    v___x_604_ = v_reuseFailAlloc_605_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_604_;
            }
            18 => {
                if v_isShared_610_ == 0 {
                    v___x_612_ = v___x_609_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
                    v___x_612_ = v_reuseFailAlloc_613_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_612_;
            }
            20 => {
                if v_isShared_618_ == 0 {
                    v___x_620_ = v___x_617_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_621_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
                    v___x_620_ = v_reuseFailAlloc_621_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_620_;
            }
            22 => {
                if v_isShared_626_ == 0 {
                    v___x_628_ = v___x_625_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_629_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
                    v___x_628_ = v_reuseFailAlloc_629_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_628_;
            }
            24 => {
                crate::leanh::lean_inc(v___y_459_);
                crate::leanh::lean_inc_ref(v___y_458_);
                crate::leanh::lean_inc(v___y_457_);
                crate::leanh::lean_inc_ref(v___y_456_);
                crate::leanh::lean_inc(v___x_495_);
                v___x_640_ =
                    lean_infer_type(v___x_495_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
                if crate::leanh::lean_obj_tag(v___x_640_) == 0 {
                    v_a_641_ = crate::leanh::lean_ctor_get(v___x_640_, 0);
                    crate::leanh::lean_inc(v_a_641_);
                    crate::leanh::lean_dec_ref_known(v___x_640_, 1);
                    v___x_642_ =
                        l_Lean_Meta_whnfD(v_a_641_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
                    if crate::leanh::lean_obj_tag(v___x_642_) == 0 {
                        v_a_643_ = crate::leanh::lean_ctor_get(v___x_642_, 0);
                        crate::leanh::lean_inc(v_a_643_);
                        crate::leanh::lean_dec_ref_known(v___x_642_, 1);
                        crate::leanh::lean_inc(v___y_459_);
                        crate::leanh::lean_inc_ref(v___y_458_);
                        crate::leanh::lean_inc(v___y_457_);
                        crate::leanh::lean_inc_ref(v___y_456_);
                        crate::leanh::lean_inc_ref(v_self_501_);
                        v___x_644_ = lean_infer_type(
                            v_self_501_,
                            v___y_456_,
                            v___y_457_,
                            v___y_458_,
                            v___y_459_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_644_) == 0 {
                            v_a_645_ = crate::leanh::lean_ctor_get(v___x_644_, 0);
                            crate::leanh::lean_inc(v_a_645_);
                            crate::leanh::lean_dec_ref_known(v___x_644_, 1);
                            v___x_646_ = l_Lean_Meta_whnfD(
                                v_a_645_, v___y_456_, v___y_457_, v___y_458_, v___y_459_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_646_) == 0 {
                                v_a_647_ = crate::leanh::lean_ctor_get(v___x_646_, 0);
                                v_isSharedCheck_667_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_646_)) as u8;
                                if v_isSharedCheck_667_ == 0 {
                                    v___x_649_ = v___x_646_;
                                    v_isShared_650_ = v_isSharedCheck_667_;
                                    state = 25;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_647_);
                                    crate::leanh::lean_dec(v___x_646_);
                                    v___x_649_ = crate::leanh::lean_box(0);
                                    v_isShared_650_ = v_isSharedCheck_667_;
                                    state = 25;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_643_);
                                crate::leanh::lean_dec(v___y_639_);
                                crate::leanh::lean_dec_ref(v_self_501_);
                                crate::leanh::lean_dec(v___x_495_);
                                crate::leanh::lean_dec(v___x_485_);
                                crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                                crate::leanh::lean_del_object(v___x_479_);
                                crate::leanh::lean_del_object(v___x_470_);
                                v_a_668_ = crate::leanh::lean_ctor_get(v___x_646_, 0);
                                v_isSharedCheck_675_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_646_)) as u8;
                                if v_isSharedCheck_675_ == 0 {
                                    v___x_670_ = v___x_646_;
                                    v_isShared_671_ = v_isSharedCheck_675_;
                                    state = 27;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_668_);
                                    crate::leanh::lean_dec(v___x_646_);
                                    v___x_670_ = crate::leanh::lean_box(0);
                                    v_isShared_671_ = v_isSharedCheck_675_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_643_);
                            crate::leanh::lean_dec(v___y_639_);
                            crate::leanh::lean_dec_ref(v_self_501_);
                            crate::leanh::lean_dec(v___x_495_);
                            crate::leanh::lean_dec(v___x_485_);
                            crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                            crate::leanh::lean_del_object(v___x_479_);
                            crate::leanh::lean_del_object(v___x_470_);
                            v_a_676_ = crate::leanh::lean_ctor_get(v___x_644_, 0);
                            v_isSharedCheck_683_ =
                                (!crate::leanh::lean_is_exclusive(v___x_644_)) as u8;
                            if v_isSharedCheck_683_ == 0 {
                                v___x_678_ = v___x_644_;
                                v_isShared_679_ = v_isSharedCheck_683_;
                                state = 29;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_676_);
                                crate::leanh::lean_dec(v___x_644_);
                                v___x_678_ = crate::leanh::lean_box(0);
                                v_isShared_679_ = v_isSharedCheck_683_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_639_);
                        crate::leanh::lean_dec_ref(v_self_501_);
                        crate::leanh::lean_dec(v___x_495_);
                        crate::leanh::lean_dec(v___x_485_);
                        crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                        crate::leanh::lean_del_object(v___x_479_);
                        crate::leanh::lean_del_object(v___x_470_);
                        v_a_684_ = crate::leanh::lean_ctor_get(v___x_642_, 0);
                        v_isSharedCheck_691_ = (!crate::leanh::lean_is_exclusive(v___x_642_)) as u8;
                        if v_isSharedCheck_691_ == 0 {
                            v___x_686_ = v___x_642_;
                            v_isShared_687_ = v_isSharedCheck_691_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_684_);
                            crate::leanh::lean_dec(v___x_642_);
                            v___x_686_ = crate::leanh::lean_box(0);
                            v_isShared_687_ = v_isSharedCheck_691_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_639_);
                    crate::leanh::lean_dec_ref(v_self_501_);
                    crate::leanh::lean_dec(v___x_495_);
                    crate::leanh::lean_dec(v___x_485_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                    crate::leanh::lean_del_object(v___x_479_);
                    crate::leanh::lean_del_object(v___x_470_);
                    v_a_692_ = crate::leanh::lean_ctor_get(v___x_640_, 0);
                    v_isSharedCheck_699_ = (!crate::leanh::lean_is_exclusive(v___x_640_)) as u8;
                    if v_isSharedCheck_699_ == 0 {
                        v___x_694_ = v___x_640_;
                        v_isShared_695_ = v_isSharedCheck_699_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_692_);
                        crate::leanh::lean_dec(v___x_640_);
                        v___x_694_ = crate::leanh::lean_box(0);
                        v_isShared_695_ = v_isSharedCheck_699_;
                        state = 33;
                        continue;
                    }
                }
            }
            25 => {
                v_name_651_ = crate::leanh::lean_ctor_get(v_toConstantVal_481_, 0);
                crate::leanh::lean_inc(v_name_651_);
                crate::leanh::lean_dec_ref(v_toConstantVal_481_);
                crate::leanh::lean_inc(v___x_485_);
                v___x_652_ = l_Lean_Expr_isAppOfArity(v_a_643_, v_name_651_, v___x_485_);
                if v___x_652_ == 0 {
                    crate::leanh::lean_dec(v_name_651_);
                    crate::leanh::lean_del_object(v___x_649_);
                    crate::leanh::lean_dec(v_a_647_);
                    crate::leanh::lean_dec(v_a_643_);
                    crate::leanh::lean_dec(v___y_639_);
                    crate::leanh::lean_dec_ref(v_self_501_);
                    crate::leanh::lean_dec(v___x_495_);
                    crate::leanh::lean_dec(v___x_485_);
                    crate::leanh::lean_del_object(v___x_479_);
                    crate::leanh::lean_del_object(v___x_470_);
                    v___x_653_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
                    v___x_654_ = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(
                        v___x_653_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_,
                        v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_,
                    );
                    return v___x_654_;
                } else {
                    v___x_655_ = l_Lean_Expr_isAppOfArity(v_a_647_, v_name_651_, v___x_485_);
                    if v___x_655_ == 0 {
                        crate::leanh::lean_dec(v_name_651_);
                        crate::leanh::lean_dec(v_a_647_);
                        crate::leanh::lean_dec(v_a_643_);
                        crate::leanh::lean_dec(v___y_639_);
                        crate::leanh::lean_dec_ref(v_self_501_);
                        crate::leanh::lean_dec(v___x_495_);
                        crate::leanh::lean_del_object(v___x_479_);
                        crate::leanh::lean_del_object(v___x_470_);
                        v___x_656_ = crate::leanh::lean_box(0);
                        if v_isShared_650_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_649_, 0, v___x_656_);
                            v___x_658_ = v___x_649_;
                            state = 26;
                            continue;
                        } else {
                            v_reuseFailAlloc_659_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
                            v___x_658_ = v_reuseFailAlloc_659_;
                            state = 26;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_649_);
                        v___x_660_ = lean_st_ref_get(v___y_459_);
                        v_env_661_ = crate::leanh::lean_ctor_get(v___x_660_, 0);
                        crate::leanh::lean_inc_ref(v_env_661_);
                        crate::leanh::lean_dec(v___x_660_);
                        v___x_662_ = l_Lean_Expr_getAppFn(v_a_643_);
                        v___x_663_ = l_Lean_Expr_constLevels_x21(v___x_662_);
                        crate::leanh::lean_dec_ref(v___x_662_);
                        v___x_664_ = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(v_name_651_);
                        v___x_665_ = l_Lean_Environment_containsOnBranch(v_env_661_, v___x_664_);
                        crate::leanh::lean_dec_ref(v_env_661_);
                        if v___x_665_ == 0 {
                            crate::leanh::lean_inc(v___x_664_);
                            v___x_666_ = l_Lean_executeReservedNameAction(
                                v___x_664_, v___y_458_, v___y_459_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_666_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_666_, 1);
                                v___y_505_ = v___y_639_;
                                v___y_506_ = v___x_664_;
                                v___y_507_ = v_a_647_;
                                v___y_508_ = v_a_643_;
                                v___y_509_ = v___x_663_;
                                v___y_510_ = v___y_450_;
                                v___y_511_ = v___y_451_;
                                v___y_512_ = v___y_452_;
                                v___y_513_ = v___y_453_;
                                v___y_514_ = v___y_454_;
                                v___y_515_ = v___y_455_;
                                v___y_516_ = v___y_456_;
                                v___y_517_ = v___y_457_;
                                v___y_518_ = v___y_458_;
                                v___y_519_ = v___y_459_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_664_);
                                crate::leanh::lean_dec(v___x_663_);
                                crate::leanh::lean_dec(v_a_647_);
                                crate::leanh::lean_dec(v_a_643_);
                                crate::leanh::lean_dec(v___y_639_);
                                crate::leanh::lean_dec_ref(v_self_501_);
                                crate::leanh::lean_dec(v___x_495_);
                                crate::leanh::lean_del_object(v___x_479_);
                                crate::leanh::lean_del_object(v___x_470_);
                                return v___x_666_;
                            }
                        } else {
                            v___y_505_ = v___y_639_;
                            v___y_506_ = v___x_664_;
                            v___y_507_ = v_a_647_;
                            v___y_508_ = v_a_643_;
                            v___y_509_ = v___x_663_;
                            v___y_510_ = v___y_450_;
                            v___y_511_ = v___y_451_;
                            v___y_512_ = v___y_452_;
                            v___y_513_ = v___y_453_;
                            v___y_514_ = v___y_454_;
                            v___y_515_ = v___y_455_;
                            v___y_516_ = v___y_456_;
                            v___y_517_ = v___y_457_;
                            v___y_518_ = v___y_458_;
                            v___y_519_ = v___y_459_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            26 => {
                return v___x_658_;
            }
            27 => {
                if v_isShared_671_ == 0 {
                    v___x_673_ = v___x_670_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_674_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
                    v___x_673_ = v_reuseFailAlloc_674_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_673_;
            }
            29 => {
                if v_isShared_679_ == 0 {
                    v___x_681_ = v___x_678_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_682_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
                    v___x_681_ = v_reuseFailAlloc_682_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_681_;
            }
            31 => {
                if v_isShared_687_ == 0 {
                    v___x_689_ = v___x_686_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_690_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
                    v___x_689_ = v_reuseFailAlloc_690_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_689_;
            }
            33 => {
                if v_isShared_695_ == 0 {
                    v___x_697_ = v___x_694_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_698_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
                    v___x_697_ = v_reuseFailAlloc_698_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_697_;
            }
            35 => {
                if v_isShared_704_ == 0 {
                    v___x_706_ = v___x_703_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_707_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
                    v___x_706_ = v_reuseFailAlloc_707_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_706_;
            }
            37 => {
                if v_isShared_712_ == 0 {
                    v___x_714_ = v___x_711_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_715_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
                    v___x_714_ = v_reuseFailAlloc_715_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_714_;
            }
            39 => {
                if v_isShared_720_ == 0 {
                    v___x_722_ = v___x_719_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_723_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
                    v___x_722_ = v_reuseFailAlloc_723_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_722_;
            }
            41 => {
                return v___x_727_;
            }
            42 => {
                if v_isShared_733_ == 0 {
                    v___x_735_ = v___x_732_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_736_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
                    v___x_735_ = v_reuseFailAlloc_736_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_735_;
            }
            44 => {
                if v_isShared_742_ == 0 {
                    v___x_744_ = v___x_741_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_745_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
                    v___x_744_ = v_reuseFailAlloc_745_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_744_;
            }
            46 => {
                return v___x_750_;
            }
            47 => {
                if v_isShared_756_ == 0 {
                    v___x_758_ = v___x_755_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_759_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
                    v___x_758_ = v_reuseFailAlloc_759_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___boxed(
    mut v_e_764_: *mut crate::leanh::LeanObject,
    mut v_x_765_: *mut crate::leanh::LeanObject,
    mut v_x_766_: *mut crate::leanh::LeanObject,
    mut v_x_767_: *mut crate::leanh::LeanObject,
    mut v___y_768_: *mut crate::leanh::LeanObject,
    mut v___y_769_: *mut crate::leanh::LeanObject,
    mut v___y_770_: *mut crate::leanh::LeanObject,
    mut v___y_771_: *mut crate::leanh::LeanObject,
    mut v___y_772_: *mut crate::leanh::LeanObject,
    mut v___y_773_: *mut crate::leanh::LeanObject,
    mut v___y_774_: *mut crate::leanh::LeanObject,
    mut v___y_775_: *mut crate::leanh::LeanObject,
    mut v___y_776_: *mut crate::leanh::LeanObject,
    mut v___y_777_: *mut crate::leanh::LeanObject,
    mut v___y_778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_779_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(
        v_e_764_, v_x_765_, v_x_766_, v_x_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_,
        v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_,
    );
    crate::leanh::lean_dec(v___y_777_);
    crate::leanh::lean_dec_ref(v___y_776_);
    crate::leanh::lean_dec(v___y_775_);
    crate::leanh::lean_dec_ref(v___y_774_);
    crate::leanh::lean_dec(v___y_773_);
    crate::leanh::lean_dec_ref(v___y_772_);
    crate::leanh::lean_dec(v___y_771_);
    crate::leanh::lean_dec_ref(v___y_770_);
    crate::leanh::lean_dec(v___y_769_);
    crate::leanh::lean_dec(v___y_768_);
    return v_res_779_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateCtorIdxUp(
    mut v_e_780_: *mut crate::leanh::LeanObject,
    mut v_a_781_: *mut crate::leanh::LeanObject,
    mut v_a_782_: *mut crate::leanh::LeanObject,
    mut v_a_783_: *mut crate::leanh::LeanObject,
    mut v_a_784_: *mut crate::leanh::LeanObject,
    mut v_a_785_: *mut crate::leanh::LeanObject,
    mut v_a_786_: *mut crate::leanh::LeanObject,
    mut v_a_787_: *mut crate::leanh::LeanObject,
    mut v_a_788_: *mut crate::leanh::LeanObject,
    mut v_a_789_: *mut crate::leanh::LeanObject,
    mut v_a_790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dummy_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dummy_792_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
    v_nargs_793_ = l_Lean_Expr_getAppNumArgs(v_e_780_);
    crate::leanh::lean_inc(v_nargs_793_);
    v___x_794_ = lean_mk_array(v_nargs_793_, v_dummy_792_);
    v___x_795_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_796_ = lean_nat_sub(v_nargs_793_, v___x_795_);
    crate::leanh::lean_dec(v_nargs_793_);
    crate::leanh::lean_inc_ref(v_e_780_);
    v___x_797_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(
        v_e_780_, v_e_780_, v___x_794_, v___x_796_, v_a_781_, v_a_782_, v_a_783_, v_a_784_,
        v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_,
    );
    return v___x_797_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(
    mut v_e_798_: *mut crate::leanh::LeanObject,
    mut v_a_799_: *mut crate::leanh::LeanObject,
    mut v_a_800_: *mut crate::leanh::LeanObject,
    mut v_a_801_: *mut crate::leanh::LeanObject,
    mut v_a_802_: *mut crate::leanh::LeanObject,
    mut v_a_803_: *mut crate::leanh::LeanObject,
    mut v_a_804_: *mut crate::leanh::LeanObject,
    mut v_a_805_: *mut crate::leanh::LeanObject,
    mut v_a_806_: *mut crate::leanh::LeanObject,
    mut v_a_807_: *mut crate::leanh::LeanObject,
    mut v_a_808_: *mut crate::leanh::LeanObject,
    mut v_a_809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_810_ = l_Lean_Meta_Grind_propagateCtorIdxUp(
        v_e_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_,
        v_a_807_, v_a_808_,
    );
    crate::leanh::lean_dec(v_a_808_);
    crate::leanh::lean_dec_ref(v_a_807_);
    crate::leanh::lean_dec(v_a_806_);
    crate::leanh::lean_dec_ref(v_a_805_);
    crate::leanh::lean_dec(v_a_804_);
    crate::leanh::lean_dec_ref(v_a_803_);
    crate::leanh::lean_dec(v_a_802_);
    crate::leanh::lean_dec_ref(v_a_801_);
    crate::leanh::lean_dec(v_a_800_);
    crate::leanh::lean_dec(v_a_799_);
    return v_res_810_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_CtorIdx(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CtorIdxHInj(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_CtorIdx(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_CtorIdx(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_CtorIdxHInj(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_CtorIdx(builtin);
}
