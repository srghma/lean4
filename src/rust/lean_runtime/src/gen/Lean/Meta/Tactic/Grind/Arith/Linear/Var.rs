// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Var
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.LinearM Lean.Meta.Tactic.Grind.Arith.Linear.Util
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::LinearM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
    l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Types::l_Lean_Meta_Grind_Arith_Linear_linearExt;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util,
    l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_SolverExtension_markTerm___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
    lean_usize_once,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_499_: *mut LeanObject,
    mut v_x_500_: *mut LeanObject,
    mut v_x_501_: *mut LeanObject,
    mut v_x_502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_507_: u8 = 0;
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: u8 = 0;
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u8 = 0;
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_503_ = lean_ctor_get(v_x_499_, 0);
                v_vs_504_ = lean_ctor_get(v_x_499_, 1);
                v_isSharedCheck_528_ = (!lean_is_exclusive(v_x_499_)) as u8;
                if v_isSharedCheck_528_ == 0 {
                    v___x_506_ = v_x_499_;
                    v_isShared_507_ = v_isSharedCheck_528_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_504_);
                    lean_inc(v_ks_503_);
                    lean_dec(v_x_499_);
                    v___x_506_ = lean_box(0);
                    v_isShared_507_ = v_isSharedCheck_528_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_508_ = lean_array_get_size(v_ks_503_);
                v___x_509_ = lean_nat_dec_lt(v_x_500_, v___x_508_);
                if v___x_509_ == 0 {
                    lean_dec(v_x_500_);
                    v___x_510_ = lean_array_push(v_ks_503_, v_x_501_);
                    v___x_511_ = lean_array_push(v_vs_504_, v_x_502_);
                    if v_isShared_507_ == 0 {
                        lean_ctor_set(v___x_506_, 1, v___x_511_);
                        lean_ctor_set(v___x_506_, 0, v___x_510_);
                        v___x_513_ = v___x_506_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_510_);
                        lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_511_);
                        v___x_513_ = v_reuseFailAlloc_514_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_515_ = lean_array_fget_borrowed(v_ks_503_, v_x_500_);
                    v___x_516_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_501_,
                            v_k_x27_515_,
                        );
                    if v___x_516_ == 0 {
                        if v_isShared_507_ == 0 {
                            v___x_518_ = v___x_506_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_522_, 0, v_ks_503_);
                            lean_ctor_set(v_reuseFailAlloc_522_, 1, v_vs_504_);
                            v___x_518_ = v_reuseFailAlloc_522_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_523_ = lean_array_fset(v_ks_503_, v_x_500_, v_x_501_);
                        v___x_524_ = lean_array_fset(v_vs_504_, v_x_500_, v_x_502_);
                        lean_dec(v_x_500_);
                        if v_isShared_507_ == 0 {
                            lean_ctor_set(v___x_506_, 1, v___x_524_);
                            lean_ctor_set(v___x_506_, 0, v___x_523_);
                            v___x_526_ = v___x_506_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_523_);
                            lean_ctor_set(v_reuseFailAlloc_527_, 1, v___x_524_);
                            v___x_526_ = v_reuseFailAlloc_527_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_513_;
            }
            3 => {
                v___x_519_ = lean_unsigned_to_nat(1);
                v___x_520_ = lean_nat_add(v_x_500_, v___x_519_);
                lean_dec(v_x_500_);
                v_x_499_ = v___x_518_;
                v_x_500_ = v___x_520_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4___redArg(
    mut v_n_529_: *mut LeanObject,
    mut v_k_530_: *mut LeanObject,
    mut v_v_531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    v___x_532_ = lean_unsigned_to_nat(0);
    v___x_533_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5___redArg(v_n_529_, v___x_532_, v_k_530_, v_v_531_);
    return v___x_533_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_534_: usize = 0;
    let mut v___x_535_: usize = 0;
    let mut v___x_536_: usize = 0;
    v___x_534_ = 5usize;
    v___x_535_ = 1usize;
    v___x_536_ = lean_usize_shift_left(v___x_535_, v___x_534_);
    return v___x_536_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_537_: usize = 0;
    let mut v___x_538_: usize = 0;
    let mut v___x_539_: usize = 0;
    v___x_537_ = 1usize;
    v___x_538_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__0);
    v___x_539_ = lean_usize_sub(v___x_538_, v___x_537_);
    return v___x_539_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    v___x_540_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_540_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(
    mut v_x_541_: *mut LeanObject,
    mut v_x_542_: usize,
    mut v_x_543_: usize,
    mut v_x_544_: *mut LeanObject,
    mut v_x_545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: usize = 0;
    let mut v___x_548_: usize = 0;
    let mut v___x_549_: usize = 0;
    let mut v___x_550_: usize = 0;
    let mut v_j_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: u8 = 0;
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_556_: u8 = 0;
    let mut v_v_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_570_: u8 = 0;
    let mut v___x_571_: u8 = 0;
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_577_: u8 = 0;
    let mut v_node_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_581_: u8 = 0;
    let mut v___x_582_: usize = 0;
    let mut v___x_583_: usize = 0;
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_588_: u8 = 0;
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_590_: u8 = 0;
    let mut v_unused_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_596_: u8 = 0;
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_601_: u8 = 0;
    let mut v_ks_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: usize = 0;
    let mut v___x_608_: u8 = 0;
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: u8 = 0;
    let mut v_reuseFailAlloc_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_541_) == 0 {
                    v_es_546_ = lean_ctor_get(v_x_541_, 0);
                    v___x_547_ = 5usize;
                    v___x_548_ = 1usize;
                    v___x_549_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1);
                    v___x_550_ = lean_usize_land(v_x_542_, v___x_549_);
                    v_j_551_ = lean_usize_to_nat(v___x_550_);
                    v___x_552_ = lean_array_get_size(v_es_546_);
                    v___x_553_ = lean_nat_dec_lt(v_j_551_, v___x_552_);
                    if v___x_553_ == 0 {
                        lean_dec(v_j_551_);
                        lean_dec(v_x_545_);
                        lean_dec_ref(v_x_544_);
                        return v_x_541_;
                    } else {
                        lean_inc_ref(v_es_546_);
                        v_isSharedCheck_590_ = (!lean_is_exclusive(v_x_541_)) as u8;
                        if v_isSharedCheck_590_ == 0 {
                            v_unused_591_ = lean_ctor_get(v_x_541_, 0);
                            lean_dec(v_unused_591_);
                            v___x_555_ = v_x_541_;
                            v_isShared_556_ = v_isSharedCheck_590_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_541_);
                            v___x_555_ = lean_box(0);
                            v_isShared_556_ = v_isSharedCheck_590_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_592_ = lean_ctor_get(v_x_541_, 0);
                    v_vs_593_ = lean_ctor_get(v_x_541_, 1);
                    v_isSharedCheck_613_ = (!lean_is_exclusive(v_x_541_)) as u8;
                    if v_isSharedCheck_613_ == 0 {
                        v___x_595_ = v_x_541_;
                        v_isShared_596_ = v_isSharedCheck_613_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_593_);
                        lean_inc(v_ks_592_);
                        lean_dec(v_x_541_);
                        v___x_595_ = lean_box(0);
                        v_isShared_596_ = v_isSharedCheck_613_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_557_ = lean_array_fget(v_es_546_, v_j_551_);
                v___x_558_ = lean_box(0);
                v_xs_x27_559_ = lean_array_fset(v_es_546_, v_j_551_, v___x_558_);
                match lean_obj_tag(v_v_557_) {
                    0 => {
                        v_key_566_ = lean_ctor_get(v_v_557_, 0);
                        v_val_567_ = lean_ctor_get(v_v_557_, 1);
                        v_isSharedCheck_577_ = (!lean_is_exclusive(v_v_557_)) as u8;
                        if v_isSharedCheck_577_ == 0 {
                            v___x_569_ = v_v_557_;
                            v_isShared_570_ = v_isSharedCheck_577_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_567_);
                            lean_inc(v_key_566_);
                            lean_dec(v_v_557_);
                            v___x_569_ = lean_box(0);
                            v_isShared_570_ = v_isSharedCheck_577_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_578_ = lean_ctor_get(v_v_557_, 0);
                        v_isSharedCheck_588_ = (!lean_is_exclusive(v_v_557_)) as u8;
                        if v_isSharedCheck_588_ == 0 {
                            v___x_580_ = v_v_557_;
                            v_isShared_581_ = v_isSharedCheck_588_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_578_);
                            lean_dec(v_v_557_);
                            v___x_580_ = lean_box(0);
                            v_isShared_581_ = v_isSharedCheck_588_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_589_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_589_, 0, v_x_544_);
                        lean_ctor_set(v___x_589_, 1, v_x_545_);
                        v___y_561_ = v___x_589_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_562_ = lean_array_fset(v_xs_x27_559_, v_j_551_, v___y_561_);
                lean_dec(v_j_551_);
                if v_isShared_556_ == 0 {
                    lean_ctor_set(v___x_555_, 0, v___x_562_);
                    v___x_564_ = v___x_555_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
                    v___x_564_ = v_reuseFailAlloc_565_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_564_;
            }
            4 => {
                v___x_571_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_544_, v_key_566_,
                    );
                if v___x_571_ == 0 {
                    lean_del_object(v___x_569_);
                    v___x_572_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_566_, v_val_567_, v_x_544_, v_x_545_,
                    );
                    v___x_573_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_573_, 0, v___x_572_);
                    v___y_561_ = v___x_573_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_567_);
                    lean_dec(v_key_566_);
                    if v_isShared_570_ == 0 {
                        lean_ctor_set(v___x_569_, 1, v_x_545_);
                        lean_ctor_set(v___x_569_, 0, v_x_544_);
                        v___x_575_ = v___x_569_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_576_, 0, v_x_544_);
                        lean_ctor_set(v_reuseFailAlloc_576_, 1, v_x_545_);
                        v___x_575_ = v_reuseFailAlloc_576_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_561_ = v___x_575_;
                state = 2;
                continue;
            }
            6 => {
                v___x_582_ = lean_usize_shift_right(v_x_542_, v___x_547_);
                v___x_583_ = lean_usize_add(v_x_543_, v___x_548_);
                v___x_584_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_node_578_, v___x_582_, v___x_583_, v_x_544_, v_x_545_);
                if v_isShared_581_ == 0 {
                    lean_ctor_set(v___x_580_, 0, v___x_584_);
                    v___x_586_ = v___x_580_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
                    v___x_586_ = v_reuseFailAlloc_587_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_561_ = v___x_586_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_596_ == 0 {
                    v___x_598_ = v___x_595_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_612_, 0, v_ks_592_);
                    lean_ctor_set(v_reuseFailAlloc_612_, 1, v_vs_593_);
                    v___x_598_ = v_reuseFailAlloc_612_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_599_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4___redArg(v___x_598_, v_x_544_, v_x_545_);
                v___x_607_ = 7usize;
                v___x_608_ = lean_usize_dec_le(v___x_607_, v_x_543_);
                if v___x_608_ == 0 {
                    v___x_609_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_599_);
                    v___x_610_ = lean_unsigned_to_nat(4);
                    v___x_611_ = lean_nat_dec_lt(v___x_609_, v___x_610_);
                    lean_dec(v___x_609_);
                    v___y_601_ = v___x_611_;
                    state = 10;
                    continue;
                } else {
                    v___y_601_ = v___x_608_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_601_ == 0 {
                    v_ks_602_ = lean_ctor_get(v_newNode_599_, 0);
                    lean_inc_ref(v_ks_602_);
                    v_vs_603_ = lean_ctor_get(v_newNode_599_, 1);
                    lean_inc_ref(v_vs_603_);
                    lean_dec_ref(v_newNode_599_);
                    v___x_604_ = lean_unsigned_to_nat(0);
                    v___x_605_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__2);
                    v___x_606_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_x_543_, v_ks_602_, v_vs_603_, v___x_604_, v___x_605_);
                    lean_dec_ref(v_vs_603_);
                    lean_dec_ref(v_ks_602_);
                    return v___x_606_;
                } else {
                    return v_newNode_599_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(
    mut v_depth_614_: usize,
    mut v_keys_615_: *mut LeanObject,
    mut v_vals_616_: *mut LeanObject,
    mut v_i_617_: *mut LeanObject,
    mut v_entries_618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: u8 = 0;
    let mut v_k_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: u64 = 0;
    let mut v_h_624_: usize = 0;
    let mut v___x_625_: usize = 0;
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: usize = 0;
    let mut v___x_628_: usize = 0;
    let mut v___x_629_: usize = 0;
    let mut v_h_630_: usize = 0;
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_619_ = lean_array_get_size(v_keys_615_);
                v___x_620_ = lean_nat_dec_lt(v_i_617_, v___x_619_);
                if v___x_620_ == 0 {
                    lean_dec(v_i_617_);
                    return v_entries_618_;
                } else {
                    v_k_621_ = lean_array_fget_borrowed(v_keys_615_, v_i_617_);
                    v_v_622_ = lean_array_fget_borrowed(v_vals_616_, v_i_617_);
                    v___x_623_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_621_);
                    v_h_624_ = lean_uint64_to_usize(v___x_623_);
                    v___x_625_ = 5usize;
                    v___x_626_ = lean_unsigned_to_nat(1);
                    v___x_627_ = 1usize;
                    v___x_628_ = lean_usize_sub(v_depth_614_, v___x_627_);
                    v___x_629_ = lean_usize_mul(v___x_625_, v___x_628_);
                    v_h_630_ = lean_usize_shift_right(v_h_624_, v___x_629_);
                    v___x_631_ = lean_nat_add(v_i_617_, v___x_626_);
                    lean_dec(v_i_617_);
                    lean_inc(v_v_622_);
                    lean_inc(v_k_621_);
                    v___x_632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_entries_618_, v_h_630_, v_depth_614_, v_k_621_, v_v_622_);
                    v_i_617_ = v___x_631_;
                    v_entries_618_ = v___x_632_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_634_: *mut LeanObject,
    mut v_keys_635_: *mut LeanObject,
    mut v_vals_636_: *mut LeanObject,
    mut v_i_637_: *mut LeanObject,
    mut v_entries_638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_639_: usize = 0;
    let mut v_res_640_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_639_ = lean_unbox_usize(v_depth_634_);
    lean_dec(v_depth_634_);
    v_res_640_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_depth_boxed_639_, v_keys_635_, v_vals_636_, v_i_637_, v_entries_638_);
    lean_dec_ref(v_vals_636_);
    lean_dec_ref(v_keys_635_);
    return v_res_640_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___boxed(
    mut v_x_641_: *mut LeanObject,
    mut v_x_642_: *mut LeanObject,
    mut v_x_643_: *mut LeanObject,
    mut v_x_644_: *mut LeanObject,
    mut v_x_645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7910__boxed_646_: usize = 0;
    let mut v_x_7911__boxed_647_: usize = 0;
    let mut v_res_648_: *mut LeanObject = core::ptr::null_mut();
    v_x_7910__boxed_646_ = lean_unbox_usize(v_x_642_);
    lean_dec(v_x_642_);
    v_x_7911__boxed_647_ = lean_unbox_usize(v_x_643_);
    lean_dec(v_x_643_);
    v_res_648_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_641_, v_x_7910__boxed_646_, v_x_7911__boxed_647_, v_x_644_, v_x_645_);
    return v_res_648_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(
    mut v_x_649_: *mut LeanObject,
    mut v_x_650_: *mut LeanObject,
    mut v_x_651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_652_: u64 = 0;
    let mut v___x_653_: usize = 0;
    let mut v___x_654_: usize = 0;
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    v___x_652_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_650_);
    v___x_653_ = lean_uint64_to_usize(v___x_652_);
    v___x_654_ = 1usize;
    v___x_655_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_649_, v___x_653_, v___x_654_, v_x_650_, v_x_651_);
    return v___x_655_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    v___x_656_ = lean_unsigned_to_nat(32);
    v___x_657_ = lean_mk_empty_array_with_capacity(v___x_656_);
    v___x_658_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_658_, 0, v___x_657_);
    return v___x_658_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_659_: usize = 0;
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    v___x_659_ = 5usize;
    v___x_660_ = lean_unsigned_to_nat(0);
    v___x_661_ = lean_unsigned_to_nat(32);
    v___x_662_ = lean_mk_empty_array_with_capacity(v___x_661_);
    v___x_663_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0_once),
        _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__0,
    );
    v___x_664_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_664_, 0, v___x_663_);
    lean_ctor_set(v___x_664_, 1, v___x_662_);
    lean_ctor_set(v___x_664_, 2, v___x_660_);
    lean_ctor_set(v___x_664_, 3, v___x_660_);
    lean_ctor_set_usize(v___x_664_, 4, v___x_659_);
    return v___x_664_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0(
    mut v_a_665_: *mut LeanObject,
    mut v_e_666_: *mut LeanObject,
    mut v_size_667_: *mut LeanObject,
    mut v_s_668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natStructs_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: u8 = 0;
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_681_: u8 = 0;
    let mut v_v_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intModuleInst_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leInst_x3f_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_x3f_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedAddInst_x3f_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isLinearInst_x3f_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noNatDivInst_x3f_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_x3f_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedRingInst_x3f_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofNatZero_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leFn_x3f_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltFn_x3f_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsmulFn_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_x3f_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsmulFn_x3f_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_homomulFn_x3f_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_719_: u8 = 0;
    let mut v_conflict_x3f_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_occurs_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ignored_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_728_: u8 = 0;
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_748_: u8 = 0;
    let mut v_isSharedCheck_749_: u8 = 0;
    let mut v_unused_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_757_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_669_ = lean_ctor_get(v_s_668_, 0);
                v_typeIdOf_670_ = lean_ctor_get(v_s_668_, 1);
                v_exprToStructId_671_ = lean_ctor_get(v_s_668_, 2);
                v_exprToStructIdEntries_672_ = lean_ctor_get(v_s_668_, 3);
                v_forbiddenNatModules_673_ = lean_ctor_get(v_s_668_, 4);
                v_natStructs_674_ = lean_ctor_get(v_s_668_, 5);
                v_natTypeIdOf_675_ = lean_ctor_get(v_s_668_, 6);
                v_exprToNatStructId_676_ = lean_ctor_get(v_s_668_, 7);
                v___x_677_ = lean_array_get_size(v_structs_669_);
                v___x_678_ = lean_nat_dec_lt(v_a_665_, v___x_677_);
                if v___x_678_ == 0 {
                    lean_dec(v_size_667_);
                    lean_dec_ref(v_e_666_);
                    return v_s_668_;
                } else {
                    lean_inc_ref(v_exprToNatStructId_676_);
                    lean_inc_ref(v_natTypeIdOf_675_);
                    lean_inc_ref(v_natStructs_674_);
                    lean_inc_ref(v_forbiddenNatModules_673_);
                    lean_inc_ref(v_exprToStructIdEntries_672_);
                    lean_inc_ref(v_exprToStructId_671_);
                    lean_inc_ref(v_typeIdOf_670_);
                    lean_inc_ref(v_structs_669_);
                    v_isSharedCheck_749_ = (!lean_is_exclusive(v_s_668_)) as u8;
                    if v_isSharedCheck_749_ == 0 {
                        v_unused_750_ = lean_ctor_get(v_s_668_, 7);
                        lean_dec(v_unused_750_);
                        v_unused_751_ = lean_ctor_get(v_s_668_, 6);
                        lean_dec(v_unused_751_);
                        v_unused_752_ = lean_ctor_get(v_s_668_, 5);
                        lean_dec(v_unused_752_);
                        v_unused_753_ = lean_ctor_get(v_s_668_, 4);
                        lean_dec(v_unused_753_);
                        v_unused_754_ = lean_ctor_get(v_s_668_, 3);
                        lean_dec(v_unused_754_);
                        v_unused_755_ = lean_ctor_get(v_s_668_, 2);
                        lean_dec(v_unused_755_);
                        v_unused_756_ = lean_ctor_get(v_s_668_, 1);
                        lean_dec(v_unused_756_);
                        v_unused_757_ = lean_ctor_get(v_s_668_, 0);
                        lean_dec(v_unused_757_);
                        v___x_680_ = v_s_668_;
                        v_isShared_681_ = v_isSharedCheck_749_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_668_);
                        v___x_680_ = lean_box(0);
                        v_isShared_681_ = v_isSharedCheck_749_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_682_ = lean_array_fget(v_structs_669_, v_a_665_);
                v_id_683_ = lean_ctor_get(v_v_682_, 0);
                v_ringId_x3f_684_ = lean_ctor_get(v_v_682_, 1);
                v_type_685_ = lean_ctor_get(v_v_682_, 2);
                v_u_686_ = lean_ctor_get(v_v_682_, 3);
                v_intModuleInst_687_ = lean_ctor_get(v_v_682_, 4);
                v_leInst_x3f_688_ = lean_ctor_get(v_v_682_, 5);
                v_ltInst_x3f_689_ = lean_ctor_get(v_v_682_, 6);
                v_lawfulOrderLTInst_x3f_690_ = lean_ctor_get(v_v_682_, 7);
                v_isPreorderInst_x3f_691_ = lean_ctor_get(v_v_682_, 8);
                v_orderedAddInst_x3f_692_ = lean_ctor_get(v_v_682_, 9);
                v_isLinearInst_x3f_693_ = lean_ctor_get(v_v_682_, 10);
                v_noNatDivInst_x3f_694_ = lean_ctor_get(v_v_682_, 11);
                v_ringInst_x3f_695_ = lean_ctor_get(v_v_682_, 12);
                v_commRingInst_x3f_696_ = lean_ctor_get(v_v_682_, 13);
                v_orderedRingInst_x3f_697_ = lean_ctor_get(v_v_682_, 14);
                v_fieldInst_x3f_698_ = lean_ctor_get(v_v_682_, 15);
                v_charInst_x3f_699_ = lean_ctor_get(v_v_682_, 16);
                v_zero_700_ = lean_ctor_get(v_v_682_, 17);
                v_ofNatZero_701_ = lean_ctor_get(v_v_682_, 18);
                v_one_x3f_702_ = lean_ctor_get(v_v_682_, 19);
                v_leFn_x3f_703_ = lean_ctor_get(v_v_682_, 20);
                v_ltFn_x3f_704_ = lean_ctor_get(v_v_682_, 21);
                v_addFn_705_ = lean_ctor_get(v_v_682_, 22);
                v_zsmulFn_706_ = lean_ctor_get(v_v_682_, 23);
                v_nsmulFn_707_ = lean_ctor_get(v_v_682_, 24);
                v_zsmulFn_x3f_708_ = lean_ctor_get(v_v_682_, 25);
                v_nsmulFn_x3f_709_ = lean_ctor_get(v_v_682_, 26);
                v_homomulFn_x3f_710_ = lean_ctor_get(v_v_682_, 27);
                v_subFn_711_ = lean_ctor_get(v_v_682_, 28);
                v_negFn_712_ = lean_ctor_get(v_v_682_, 29);
                v_vars_713_ = lean_ctor_get(v_v_682_, 30);
                v_varMap_714_ = lean_ctor_get(v_v_682_, 31);
                v_lowers_715_ = lean_ctor_get(v_v_682_, 32);
                v_uppers_716_ = lean_ctor_get(v_v_682_, 33);
                v_diseqs_717_ = lean_ctor_get(v_v_682_, 34);
                v_assignment_718_ = lean_ctor_get(v_v_682_, 35);
                v_caseSplits_719_ = lean_ctor_get_uint8(
                    v_v_682_,
                    (core::mem::size_of::<*mut LeanObject>() * 42) as u32,
                );
                v_conflict_x3f_720_ = lean_ctor_get(v_v_682_, 36);
                v_diseqSplits_721_ = lean_ctor_get(v_v_682_, 37);
                v_elimEqs_722_ = lean_ctor_get(v_v_682_, 38);
                v_elimStack_723_ = lean_ctor_get(v_v_682_, 39);
                v_occurs_724_ = lean_ctor_get(v_v_682_, 40);
                v_ignored_725_ = lean_ctor_get(v_v_682_, 41);
                v_isSharedCheck_748_ = (!lean_is_exclusive(v_v_682_)) as u8;
                if v_isSharedCheck_748_ == 0 {
                    v___x_727_ = v_v_682_;
                    v_isShared_728_ = v_isSharedCheck_748_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_ignored_725_);
                    lean_inc(v_occurs_724_);
                    lean_inc(v_elimStack_723_);
                    lean_inc(v_elimEqs_722_);
                    lean_inc(v_diseqSplits_721_);
                    lean_inc(v_conflict_x3f_720_);
                    lean_inc(v_assignment_718_);
                    lean_inc(v_diseqs_717_);
                    lean_inc(v_uppers_716_);
                    lean_inc(v_lowers_715_);
                    lean_inc(v_varMap_714_);
                    lean_inc(v_vars_713_);
                    lean_inc(v_negFn_712_);
                    lean_inc(v_subFn_711_);
                    lean_inc(v_homomulFn_x3f_710_);
                    lean_inc(v_nsmulFn_x3f_709_);
                    lean_inc(v_zsmulFn_x3f_708_);
                    lean_inc(v_nsmulFn_707_);
                    lean_inc(v_zsmulFn_706_);
                    lean_inc(v_addFn_705_);
                    lean_inc(v_ltFn_x3f_704_);
                    lean_inc(v_leFn_x3f_703_);
                    lean_inc(v_one_x3f_702_);
                    lean_inc(v_ofNatZero_701_);
                    lean_inc(v_zero_700_);
                    lean_inc(v_charInst_x3f_699_);
                    lean_inc(v_fieldInst_x3f_698_);
                    lean_inc(v_orderedRingInst_x3f_697_);
                    lean_inc(v_commRingInst_x3f_696_);
                    lean_inc(v_ringInst_x3f_695_);
                    lean_inc(v_noNatDivInst_x3f_694_);
                    lean_inc(v_isLinearInst_x3f_693_);
                    lean_inc(v_orderedAddInst_x3f_692_);
                    lean_inc(v_isPreorderInst_x3f_691_);
                    lean_inc(v_lawfulOrderLTInst_x3f_690_);
                    lean_inc(v_ltInst_x3f_689_);
                    lean_inc(v_leInst_x3f_688_);
                    lean_inc(v_intModuleInst_687_);
                    lean_inc(v_u_686_);
                    lean_inc(v_type_685_);
                    lean_inc(v_ringId_x3f_684_);
                    lean_inc(v_id_683_);
                    lean_dec(v_v_682_);
                    v___x_727_ = lean_box(0);
                    v_isShared_728_ = v_isSharedCheck_748_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_729_ = lean_box(0);
                v_xs_x27_730_ = lean_array_fset(v_structs_669_, v_a_665_, v___x_729_);
                lean_inc_ref(v_e_666_);
                v___x_731_ = l_Lean_PersistentArray_push___redArg(v_vars_713_, v_e_666_);
                v___x_732_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(v_varMap_714_, v_e_666_, v_size_667_);
                v___x_733_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___closed__1,
                );
                v___x_734_ = l_Lean_PersistentArray_push___redArg(v_lowers_715_, v___x_733_);
                v___x_735_ = l_Lean_PersistentArray_push___redArg(v_uppers_716_, v___x_733_);
                v___x_736_ = l_Lean_PersistentArray_push___redArg(v_diseqs_717_, v___x_733_);
                v___x_737_ = lean_box(0);
                v___x_738_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_722_, v___x_737_);
                v___x_739_ = lean_box(1);
                v___x_740_ = l_Lean_PersistentArray_push___redArg(v_occurs_724_, v___x_739_);
                if v_isShared_728_ == 0 {
                    lean_ctor_set(v___x_727_, 40, v___x_740_);
                    lean_ctor_set(v___x_727_, 38, v___x_738_);
                    lean_ctor_set(v___x_727_, 34, v___x_736_);
                    lean_ctor_set(v___x_727_, 33, v___x_735_);
                    lean_ctor_set(v___x_727_, 32, v___x_734_);
                    lean_ctor_set(v___x_727_, 31, v___x_732_);
                    lean_ctor_set(v___x_727_, 30, v___x_731_);
                    v___x_742_ = v___x_727_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 42, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_747_, 0, v_id_683_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 1, v_ringId_x3f_684_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 2, v_type_685_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 3, v_u_686_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 4, v_intModuleInst_687_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 5, v_leInst_x3f_688_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 6, v_ltInst_x3f_689_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 7, v_lawfulOrderLTInst_x3f_690_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 8, v_isPreorderInst_x3f_691_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 9, v_orderedAddInst_x3f_692_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 10, v_isLinearInst_x3f_693_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 11, v_noNatDivInst_x3f_694_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 12, v_ringInst_x3f_695_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 13, v_commRingInst_x3f_696_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 14, v_orderedRingInst_x3f_697_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 15, v_fieldInst_x3f_698_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 16, v_charInst_x3f_699_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 17, v_zero_700_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 18, v_ofNatZero_701_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 19, v_one_x3f_702_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 20, v_leFn_x3f_703_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 21, v_ltFn_x3f_704_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 22, v_addFn_705_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 23, v_zsmulFn_706_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 24, v_nsmulFn_707_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 25, v_zsmulFn_x3f_708_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 26, v_nsmulFn_x3f_709_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 27, v_homomulFn_x3f_710_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 28, v_subFn_711_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 29, v_negFn_712_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 30, v___x_731_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 31, v___x_732_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 32, v___x_734_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 33, v___x_735_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 34, v___x_736_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 35, v_assignment_718_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 36, v_conflict_x3f_720_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 37, v_diseqSplits_721_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 38, v___x_738_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 39, v_elimStack_723_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 40, v___x_740_);
                    lean_ctor_set(v_reuseFailAlloc_747_, 41, v_ignored_725_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_747_,
                        (core::mem::size_of::<*mut LeanObject>() * 42) as u32,
                        v_caseSplits_719_,
                    );
                    v___x_742_ = v_reuseFailAlloc_747_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_743_ = lean_array_fset(v_xs_x27_730_, v_a_665_, v___x_742_);
                if v_isShared_681_ == 0 {
                    lean_ctor_set(v___x_680_, 0, v___x_743_);
                    v___x_745_ = v___x_680_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
                    lean_ctor_set(v_reuseFailAlloc_746_, 1, v_typeIdOf_670_);
                    lean_ctor_set(v_reuseFailAlloc_746_, 2, v_exprToStructId_671_);
                    lean_ctor_set(v_reuseFailAlloc_746_, 3, v_exprToStructIdEntries_672_);
                    lean_ctor_set(v_reuseFailAlloc_746_, 4, v_forbiddenNatModules_673_);
                    lean_ctor_set(v_reuseFailAlloc_746_, 5, v_natStructs_674_);
                    lean_ctor_set(v_reuseFailAlloc_746_, 6, v_natTypeIdOf_675_);
                    lean_ctor_set(v_reuseFailAlloc_746_, 7, v_exprToNatStructId_676_);
                    v___x_745_ = v_reuseFailAlloc_746_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___boxed(
    mut v_a_758_: *mut LeanObject,
    mut v_e_759_: *mut LeanObject,
    mut v_size_760_: *mut LeanObject,
    mut v_s_761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_762_: *mut LeanObject = core::ptr::null_mut();
    v_res_762_ =
        l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0(v_a_758_, v_e_759_, v_size_760_, v_s_761_);
    lean_dec(v_a_758_);
    return v_res_762_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(
    mut v_keys_763_: *mut LeanObject,
    mut v_vals_764_: *mut LeanObject,
    mut v_i_765_: *mut LeanObject,
    mut v_k_766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: u8 = 0;
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: u8 = 0;
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_767_ = lean_array_get_size(v_keys_763_);
                v___x_768_ = lean_nat_dec_lt(v_i_765_, v___x_767_);
                if v___x_768_ == 0 {
                    lean_dec(v_i_765_);
                    v___x_769_ = lean_box(0);
                    return v___x_769_;
                } else {
                    v_k_x27_770_ = lean_array_fget_borrowed(v_keys_763_, v_i_765_);
                    v___x_771_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_766_,
                            v_k_x27_770_,
                        );
                    if v___x_771_ == 0 {
                        v___x_772_ = lean_unsigned_to_nat(1);
                        v___x_773_ = lean_nat_add(v_i_765_, v___x_772_);
                        lean_dec(v_i_765_);
                        v_i_765_ = v___x_773_;
                        state = 0;
                        continue;
                    } else {
                        v___x_775_ = lean_array_fget_borrowed(v_vals_764_, v_i_765_);
                        lean_dec(v_i_765_);
                        lean_inc(v___x_775_);
                        v___x_776_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_776_, 0, v___x_775_);
                        return v___x_776_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_777_: *mut LeanObject,
    mut v_vals_778_: *mut LeanObject,
    mut v_i_779_: *mut LeanObject,
    mut v_k_780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_781_: *mut LeanObject = core::ptr::null_mut();
    v_res_781_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_keys_777_, v_vals_778_, v_i_779_, v_k_780_);
    lean_dec_ref(v_k_780_);
    lean_dec_ref(v_vals_778_);
    lean_dec_ref(v_keys_777_);
    return v_res_781_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(
    mut v_x_782_: *mut LeanObject,
    mut v_x_783_: usize,
    mut v_x_784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: usize = 0;
    let mut v___x_788_: usize = 0;
    let mut v___x_789_: usize = 0;
    let mut v_j_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: u8 = 0;
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: usize = 0;
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_782_) == 0 {
                    v_es_785_ = lean_ctor_get(v_x_782_, 0);
                    v___x_786_ = lean_box(2);
                    v___x_787_ = 5usize;
                    v___x_788_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg___closed__1);
                    v___x_789_ = lean_usize_land(v_x_783_, v___x_788_);
                    v_j_790_ = lean_usize_to_nat(v___x_789_);
                    v___x_791_ = lean_array_get_borrowed(v___x_786_, v_es_785_, v_j_790_);
                    lean_dec(v_j_790_);
                    match lean_obj_tag(v___x_791_) {
                        0 => {
                            v_key_792_ = lean_ctor_get(v___x_791_, 0);
                            v_val_793_ = lean_ctor_get(v___x_791_, 1);
                            v___x_794_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_784_, v_key_792_);
                            if v___x_794_ == 0 {
                                v___x_795_ = lean_box(0);
                                return v___x_795_;
                            } else {
                                lean_inc(v_val_793_);
                                v___x_796_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_796_, 0, v_val_793_);
                                return v___x_796_;
                            }
                        }
                        1 => {
                            v_node_797_ = lean_ctor_get(v___x_791_, 0);
                            v___x_798_ = lean_usize_shift_right(v_x_783_, v___x_787_);
                            v_x_782_ = v_node_797_;
                            v_x_783_ = v___x_798_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_800_ = lean_box(0);
                            return v___x_800_;
                        }
                    }
                } else {
                    v_ks_801_ = lean_ctor_get(v_x_782_, 0);
                    v_vs_802_ = lean_ctor_get(v_x_782_, 1);
                    v___x_803_ = lean_unsigned_to_nat(0);
                    v___x_804_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_ks_801_, v_vs_802_, v___x_803_, v_x_784_);
                    return v___x_804_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg___boxed(
    mut v_x_805_: *mut LeanObject,
    mut v_x_806_: *mut LeanObject,
    mut v_x_807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_8211__boxed_808_: usize = 0;
    let mut v_res_809_: *mut LeanObject = core::ptr::null_mut();
    v_x_8211__boxed_808_ = lean_unbox_usize(v_x_806_);
    lean_dec(v_x_806_);
    v_res_809_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_805_, v_x_8211__boxed_808_, v_x_807_);
    lean_dec_ref(v_x_807_);
    lean_dec_ref(v_x_805_);
    return v_res_809_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(
    mut v_x_810_: *mut LeanObject,
    mut v_x_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_812_: u64 = 0;
    let mut v___x_813_: usize = 0;
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    v___x_812_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_811_);
    v___x_813_ = lean_uint64_to_usize(v___x_812_);
    v___x_814_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_810_, v___x_813_, v_x_811_);
    return v___x_814_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg___boxed(
    mut v_x_815_: *mut LeanObject,
    mut v_x_816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_817_: *mut LeanObject = core::ptr::null_mut();
    v_res_817_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_x_815_, v_x_816_);
    lean_dec_ref(v_x_816_);
    lean_dec_ref(v_x_815_);
    return v_res_817_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_mkVar(
    mut v_e_818_: *mut LeanObject,
    mut v_mark_819_: u8,
    mut v_a_820_: *mut LeanObject,
    mut v_a_821_: *mut LeanObject,
    mut v_a_822_: *mut LeanObject,
    mut v_a_823_: *mut LeanObject,
    mut v_a_824_: *mut LeanObject,
    mut v_a_825_: *mut LeanObject,
    mut v_a_826_: *mut LeanObject,
    mut v_a_827_: *mut LeanObject,
    mut v_a_828_: *mut LeanObject,
    mut v_a_829_: *mut LeanObject,
    mut v_a_830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_836_: u8 = 0;
    let mut v_vars_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_851_: u8 = 0;
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_858_: u8 = 0;
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_862_: u8 = 0;
    let mut v_unused_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_867_: u8 = 0;
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_871_: u8 = 0;
    let mut v_isSharedCheck_872_: u8 = 0;
    let mut v_unused_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_877_: u8 = 0;
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_881_: u8 = 0;
    let mut v_a_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_885_: u8 = 0;
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_889_: u8 = 0;
    let mut v_isSharedCheck_890_: u8 = 0;
    let mut v_a_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_894_: u8 = 0;
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_832_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_,
                    v_a_828_, v_a_829_, v_a_830_,
                );
                if lean_obj_tag(v___x_832_) == 0 {
                    v_a_833_ = lean_ctor_get(v___x_832_, 0);
                    v_isSharedCheck_890_ = (!lean_is_exclusive(v___x_832_)) as u8;
                    if v_isSharedCheck_890_ == 0 {
                        v___x_835_ = v___x_832_;
                        v_isShared_836_ = v_isSharedCheck_890_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_833_);
                        lean_dec(v___x_832_);
                        v___x_835_ = lean_box(0);
                        v_isShared_836_ = v_isSharedCheck_890_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_818_);
                    v_a_891_ = lean_ctor_get(v___x_832_, 0);
                    v_isSharedCheck_898_ = (!lean_is_exclusive(v___x_832_)) as u8;
                    if v_isSharedCheck_898_ == 0 {
                        v___x_893_ = v___x_832_;
                        v_isShared_894_ = v_isSharedCheck_898_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_891_);
                        lean_dec(v___x_832_);
                        v___x_893_ = lean_box(0);
                        v_isShared_894_ = v_isSharedCheck_898_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_vars_837_ = lean_ctor_get(v_a_833_, 30);
                lean_inc_ref(v_vars_837_);
                v_varMap_838_ = lean_ctor_get(v_a_833_, 31);
                lean_inc_ref(v_varMap_838_);
                lean_dec(v_a_833_);
                v___x_839_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_varMap_838_, v_e_818_);
                lean_dec_ref(v_varMap_838_);
                if lean_obj_tag(v___x_839_) == 1 {
                    lean_dec_ref(v_vars_837_);
                    lean_dec_ref(v_e_818_);
                    v_val_840_ = lean_ctor_get(v___x_839_, 0);
                    lean_inc(v_val_840_);
                    lean_dec_ref_known(v___x_839_, 1);
                    if v_isShared_836_ == 0 {
                        lean_ctor_set(v___x_835_, 0, v_val_840_);
                        v___x_842_ = v___x_835_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_843_, 0, v_val_840_);
                        v___x_842_ = v_reuseFailAlloc_843_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_839_);
                    lean_del_object(v___x_835_);
                    v_size_844_ = lean_ctor_get(v_vars_837_, 2);
                    lean_inc_n(v_size_844_, 2);
                    lean_dec_ref(v_vars_837_);
                    lean_inc_ref(v_e_818_);
                    lean_inc(v_a_820_);
                    v___f_845_ = lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_Linear_mkVar___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_845_, 0, v_a_820_);
                    lean_closure_set(v___f_845_, 1, v_e_818_);
                    lean_closure_set(v___f_845_, 2, v_size_844_);
                    v___x_846_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                    v___x_847_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_846_, v___f_845_, v_a_821_);
                    if lean_obj_tag(v___x_847_) == 0 {
                        lean_dec_ref_known(v___x_847_, 1);
                        lean_inc_ref(v_e_818_);
                        v___x_848_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(
                            v_e_818_, v_a_820_, v_a_821_, v_a_825_, v_a_826_, v_a_827_, v_a_828_,
                            v_a_829_, v_a_830_,
                        );
                        if lean_obj_tag(v___x_848_) == 0 {
                            v_isSharedCheck_872_ = (!lean_is_exclusive(v___x_848_)) as u8;
                            if v_isSharedCheck_872_ == 0 {
                                v_unused_873_ = lean_ctor_get(v___x_848_, 0);
                                lean_dec(v_unused_873_);
                                v___x_850_ = v___x_848_;
                                v_isShared_851_ = v_isSharedCheck_872_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_848_);
                                v___x_850_ = lean_box(0);
                                v_isShared_851_ = v_isSharedCheck_872_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_size_844_);
                            lean_dec_ref(v_e_818_);
                            v_a_874_ = lean_ctor_get(v___x_848_, 0);
                            v_isSharedCheck_881_ = (!lean_is_exclusive(v___x_848_)) as u8;
                            if v_isSharedCheck_881_ == 0 {
                                v___x_876_ = v___x_848_;
                                v_isShared_877_ = v_isSharedCheck_881_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_874_);
                                lean_dec(v___x_848_);
                                v___x_876_ = lean_box(0);
                                v_isShared_877_ = v_isSharedCheck_881_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_size_844_);
                        lean_dec_ref(v_e_818_);
                        v_a_882_ = lean_ctor_get(v___x_847_, 0);
                        v_isSharedCheck_889_ = (!lean_is_exclusive(v___x_847_)) as u8;
                        if v_isSharedCheck_889_ == 0 {
                            v___x_884_ = v___x_847_;
                            v_isShared_885_ = v_isSharedCheck_889_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_882_);
                            lean_dec(v___x_847_);
                            v___x_884_ = lean_box(0);
                            v_isShared_885_ = v_isSharedCheck_889_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_842_;
            }
            3 => {
                if v_mark_819_ == 0 {
                    lean_dec_ref(v_e_818_);
                    if v_isShared_851_ == 0 {
                        lean_ctor_set(v___x_850_, 0, v_size_844_);
                        v___x_853_ = v___x_850_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_854_, 0, v_size_844_);
                        v___x_853_ = v_reuseFailAlloc_854_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_850_);
                    v___x_855_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(
                        v___x_846_, v_e_818_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_,
                        v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_,
                    );
                    if lean_obj_tag(v___x_855_) == 0 {
                        v_isSharedCheck_862_ = (!lean_is_exclusive(v___x_855_)) as u8;
                        if v_isSharedCheck_862_ == 0 {
                            v_unused_863_ = lean_ctor_get(v___x_855_, 0);
                            lean_dec(v_unused_863_);
                            v___x_857_ = v___x_855_;
                            v_isShared_858_ = v_isSharedCheck_862_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v___x_855_);
                            v___x_857_ = lean_box(0);
                            v_isShared_858_ = v_isSharedCheck_862_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_size_844_);
                        v_a_864_ = lean_ctor_get(v___x_855_, 0);
                        v_isSharedCheck_871_ = (!lean_is_exclusive(v___x_855_)) as u8;
                        if v_isSharedCheck_871_ == 0 {
                            v___x_866_ = v___x_855_;
                            v_isShared_867_ = v_isSharedCheck_871_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_864_);
                            lean_dec(v___x_855_);
                            v___x_866_ = lean_box(0);
                            v_isShared_867_ = v_isSharedCheck_871_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_853_;
            }
            5 => {
                if v_isShared_858_ == 0 {
                    lean_ctor_set(v___x_857_, 0, v_size_844_);
                    v___x_860_ = v___x_857_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_861_, 0, v_size_844_);
                    v___x_860_ = v_reuseFailAlloc_861_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_860_;
            }
            7 => {
                if v_isShared_867_ == 0 {
                    v___x_869_ = v___x_866_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
                    v___x_869_ = v_reuseFailAlloc_870_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_869_;
            }
            9 => {
                if v_isShared_877_ == 0 {
                    v___x_879_ = v___x_876_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
                    v___x_879_ = v_reuseFailAlloc_880_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_879_;
            }
            11 => {
                if v_isShared_885_ == 0 {
                    v___x_887_ = v___x_884_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
                    v___x_887_ = v_reuseFailAlloc_888_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_887_;
            }
            13 => {
                if v_isShared_894_ == 0 {
                    v___x_896_ = v___x_893_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
                    v___x_896_ = v_reuseFailAlloc_897_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_mkVar___boxed(
    mut v_e_899_: *mut LeanObject,
    mut v_mark_900_: *mut LeanObject,
    mut v_a_901_: *mut LeanObject,
    mut v_a_902_: *mut LeanObject,
    mut v_a_903_: *mut LeanObject,
    mut v_a_904_: *mut LeanObject,
    mut v_a_905_: *mut LeanObject,
    mut v_a_906_: *mut LeanObject,
    mut v_a_907_: *mut LeanObject,
    mut v_a_908_: *mut LeanObject,
    mut v_a_909_: *mut LeanObject,
    mut v_a_910_: *mut LeanObject,
    mut v_a_911_: *mut LeanObject,
    mut v_a_912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mark_boxed_913_: u8 = 0;
    let mut v_res_914_: *mut LeanObject = core::ptr::null_mut();
    v_mark_boxed_913_ = (lean_unbox(v_mark_900_) as u8);
    v_res_914_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(
        v_e_899_,
        v_mark_boxed_913_,
        v_a_901_,
        v_a_902_,
        v_a_903_,
        v_a_904_,
        v_a_905_,
        v_a_906_,
        v_a_907_,
        v_a_908_,
        v_a_909_,
        v_a_910_,
        v_a_911_,
    );
    lean_dec(v_a_911_);
    lean_dec_ref(v_a_910_);
    lean_dec(v_a_909_);
    lean_dec_ref(v_a_908_);
    lean_dec(v_a_907_);
    lean_dec_ref(v_a_906_);
    lean_dec(v_a_905_);
    lean_dec_ref(v_a_904_);
    lean_dec(v_a_903_);
    lean_dec(v_a_902_);
    lean_dec(v_a_901_);
    return v_res_914_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0(
    mut v_00_u03b2_915_: *mut LeanObject,
    mut v_x_916_: *mut LeanObject,
    mut v_x_917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    v___x_918_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___redArg(v_x_916_, v_x_917_);
    return v___x_918_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0___boxed(
    mut v_00_u03b2_919_: *mut LeanObject,
    mut v_x_920_: *mut LeanObject,
    mut v_x_921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_922_: *mut LeanObject = core::ptr::null_mut();
    v_res_922_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0(
            v_00_u03b2_919_,
            v_x_920_,
            v_x_921_,
        );
    lean_dec_ref(v_x_921_);
    lean_dec_ref(v_x_920_);
    return v_res_922_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1(
    mut v_00_u03b2_923_: *mut LeanObject,
    mut v_x_924_: *mut LeanObject,
    mut v_x_925_: *mut LeanObject,
    mut v_x_926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    v___x_927_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1___redArg(v_x_924_, v_x_925_, v_x_926_);
    return v___x_927_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0(
    mut v_00_u03b2_928_: *mut LeanObject,
    mut v_x_929_: *mut LeanObject,
    mut v_x_930_: usize,
    mut v_x_931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    v___x_932_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___redArg(v_x_929_, v_x_930_, v_x_931_);
    return v___x_932_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0___boxed(
    mut v_00_u03b2_933_: *mut LeanObject,
    mut v_x_934_: *mut LeanObject,
    mut v_x_935_: *mut LeanObject,
    mut v_x_936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_8421__boxed_937_: usize = 0;
    let mut v_res_938_: *mut LeanObject = core::ptr::null_mut();
    v_x_8421__boxed_937_ = lean_unbox_usize(v_x_935_);
    lean_dec(v_x_935_);
    v_res_938_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0(v_00_u03b2_933_, v_x_934_, v_x_8421__boxed_937_, v_x_936_);
    lean_dec_ref(v_x_936_);
    lean_dec_ref(v_x_934_);
    return v_res_938_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2(
    mut v_00_u03b2_939_: *mut LeanObject,
    mut v_x_940_: *mut LeanObject,
    mut v_x_941_: usize,
    mut v_x_942_: usize,
    mut v_x_943_: *mut LeanObject,
    mut v_x_944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    v___x_945_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___redArg(v_x_940_, v_x_941_, v_x_942_, v_x_943_, v_x_944_);
    return v___x_945_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2___boxed(
    mut v_00_u03b2_946_: *mut LeanObject,
    mut v_x_947_: *mut LeanObject,
    mut v_x_948_: *mut LeanObject,
    mut v_x_949_: *mut LeanObject,
    mut v_x_950_: *mut LeanObject,
    mut v_x_951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_8432__boxed_952_: usize = 0;
    let mut v_x_8433__boxed_953_: usize = 0;
    let mut v_res_954_: *mut LeanObject = core::ptr::null_mut();
    v_x_8432__boxed_952_ = lean_unbox_usize(v_x_948_);
    lean_dec(v_x_948_);
    v_x_8433__boxed_953_ = lean_unbox_usize(v_x_949_);
    lean_dec(v_x_949_);
    v_res_954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2(v_00_u03b2_946_, v_x_947_, v_x_8432__boxed_952_, v_x_8433__boxed_953_, v_x_950_, v_x_951_);
    return v_res_954_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1(
    mut v_00_u03b2_955_: *mut LeanObject,
    mut v_keys_956_: *mut LeanObject,
    mut v_vals_957_: *mut LeanObject,
    mut v_heq_958_: *mut LeanObject,
    mut v_i_959_: *mut LeanObject,
    mut v_k_960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    v___x_961_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___redArg(v_keys_956_, v_vals_957_, v_i_959_, v_k_960_);
    return v___x_961_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_962_: *mut LeanObject,
    mut v_keys_963_: *mut LeanObject,
    mut v_vals_964_: *mut LeanObject,
    mut v_heq_965_: *mut LeanObject,
    mut v_i_966_: *mut LeanObject,
    mut v_k_967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_968_: *mut LeanObject = core::ptr::null_mut();
    v_res_968_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__0_spec__0_spec__1(v_00_u03b2_962_, v_keys_963_, v_vals_964_, v_heq_965_, v_i_966_, v_k_967_);
    lean_dec_ref(v_k_967_);
    lean_dec_ref(v_vals_964_);
    lean_dec_ref(v_keys_963_);
    return v_res_968_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4(
    mut v_00_u03b2_969_: *mut LeanObject,
    mut v_n_970_: *mut LeanObject,
    mut v_k_971_: *mut LeanObject,
    mut v_v_972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    v___x_973_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4___redArg(v_n_970_, v_k_971_, v_v_972_);
    return v___x_973_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5(
    mut v_00_u03b2_974_: *mut LeanObject,
    mut v_depth_975_: usize,
    mut v_keys_976_: *mut LeanObject,
    mut v_vals_977_: *mut LeanObject,
    mut v_heq_978_: *mut LeanObject,
    mut v_i_979_: *mut LeanObject,
    mut v_entries_980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    v___x_981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___redArg(v_depth_975_, v_keys_976_, v_vals_977_, v_i_979_, v_entries_980_);
    return v___x_981_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_982_: *mut LeanObject,
    mut v_depth_983_: *mut LeanObject,
    mut v_keys_984_: *mut LeanObject,
    mut v_vals_985_: *mut LeanObject,
    mut v_heq_986_: *mut LeanObject,
    mut v_i_987_: *mut LeanObject,
    mut v_entries_988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_989_: usize = 0;
    let mut v_res_990_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_989_ = lean_unbox_usize(v_depth_983_);
    lean_dec(v_depth_983_);
    v_res_990_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__5(v_00_u03b2_982_, v_depth_boxed_989_, v_keys_984_, v_vals_985_, v_heq_986_, v_i_987_, v_entries_988_);
    lean_dec_ref(v_vals_985_);
    lean_dec_ref(v_keys_984_);
    return v_res_990_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_991_: *mut LeanObject,
    mut v_x_992_: *mut LeanObject,
    mut v_x_993_: *mut LeanObject,
    mut v_x_994_: *mut LeanObject,
    mut v_x_995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    v___x_996_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_mkVar_spec__1_spec__2_spec__4_spec__5___redArg(v_x_992_, v_x_993_, v_x_994_, v_x_995_);
    return v___x_996_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
}
