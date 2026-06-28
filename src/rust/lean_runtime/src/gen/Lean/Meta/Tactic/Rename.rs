// Lean compiler output
// Module: Lean.Meta.Tactic.Rename
// Imports: Lean.Meta.Tactic.Util
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
};
use crate::r#gen::Lean::LocalContext::l_Lean_LocalContext_setUserName;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_mkFreshExprMVarAt,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    initialize_Lean_Meta_Tactic_Util, l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag,
    l_Lean_MVarId_getType, runtime_initialize_Lean_Meta_Tactic_Util,
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
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_rename___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [114, 101, 110, 97, 109, 101, 0],
};
static mut l_Lean_MVarId_rename___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rename___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_rename___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_rename___closed__0_value) as *mut LeanObject,
        16251432624378154990 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_rename___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rename___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_rename_spec__1___redArg(
    mut v_mvarId_412_: *mut LeanObject,
    mut v_x_413_: *mut LeanObject,
    mut v___y_414_: *mut LeanObject,
    mut v___y_415_: *mut LeanObject,
    mut v___y_416_: *mut LeanObject,
    mut v___y_417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_423_: u8 = 0;
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_427_: u8 = 0;
    let mut v_a_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_431_: u8 = 0;
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_419_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_412_,
                    v_x_413_,
                    v___y_414_,
                    v___y_415_,
                    v___y_416_,
                    v___y_417_,
                );
                if lean_obj_tag(v___x_419_) == 0 {
                    v_a_420_ = lean_ctor_get(v___x_419_, 0);
                    v_isSharedCheck_427_ = (!lean_is_exclusive(v___x_419_)) as u8;
                    if v_isSharedCheck_427_ == 0 {
                        v___x_422_ = v___x_419_;
                        v_isShared_423_ = v_isSharedCheck_427_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_420_);
                        lean_dec(v___x_419_);
                        v___x_422_ = lean_box(0);
                        v_isShared_423_ = v_isSharedCheck_427_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_428_ = lean_ctor_get(v___x_419_, 0);
                    v_isSharedCheck_435_ = (!lean_is_exclusive(v___x_419_)) as u8;
                    if v_isSharedCheck_435_ == 0 {
                        v___x_430_ = v___x_419_;
                        v_isShared_431_ = v_isSharedCheck_435_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_428_);
                        lean_dec(v___x_419_);
                        v___x_430_ = lean_box(0);
                        v_isShared_431_ = v_isSharedCheck_435_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_423_ == 0 {
                    v___x_425_ = v___x_422_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
                    v___x_425_ = v_reuseFailAlloc_426_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_425_;
            }
            3 => {
                if v_isShared_431_ == 0 {
                    v___x_433_ = v___x_430_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
                    v___x_433_ = v_reuseFailAlloc_434_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_rename_spec__1___redArg___boxed(
    mut v_mvarId_436_: *mut LeanObject,
    mut v_x_437_: *mut LeanObject,
    mut v___y_438_: *mut LeanObject,
    mut v___y_439_: *mut LeanObject,
    mut v___y_440_: *mut LeanObject,
    mut v___y_441_: *mut LeanObject,
    mut v___y_442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_443_: *mut LeanObject = core::ptr::null_mut();
    v_res_443_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rename_spec__1___redArg(
        v_mvarId_436_,
        v_x_437_,
        v___y_438_,
        v___y_439_,
        v___y_440_,
        v___y_441_,
    );
    lean_dec(v___y_441_);
    lean_dec_ref(v___y_440_);
    lean_dec(v___y_439_);
    lean_dec_ref(v___y_438_);
    return v_res_443_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_rename_spec__1(
    mut v_00_u03b1_444_: *mut LeanObject,
    mut v_mvarId_445_: *mut LeanObject,
    mut v_x_446_: *mut LeanObject,
    mut v___y_447_: *mut LeanObject,
    mut v___y_448_: *mut LeanObject,
    mut v___y_449_: *mut LeanObject,
    mut v___y_450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    v___x_452_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rename_spec__1___redArg(
        v_mvarId_445_,
        v_x_446_,
        v___y_447_,
        v___y_448_,
        v___y_449_,
        v___y_450_,
    );
    return v___x_452_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_rename_spec__1___boxed(
    mut v_00_u03b1_453_: *mut LeanObject,
    mut v_mvarId_454_: *mut LeanObject,
    mut v_x_455_: *mut LeanObject,
    mut v___y_456_: *mut LeanObject,
    mut v___y_457_: *mut LeanObject,
    mut v___y_458_: *mut LeanObject,
    mut v___y_459_: *mut LeanObject,
    mut v___y_460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_461_: *mut LeanObject = core::ptr::null_mut();
    v_res_461_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rename_spec__1(
        v_00_u03b1_453_,
        v_mvarId_454_,
        v_x_455_,
        v___y_456_,
        v___y_457_,
        v___y_458_,
        v___y_459_,
    );
    lean_dec(v___y_459_);
    lean_dec_ref(v___y_458_);
    lean_dec(v___y_457_);
    lean_dec_ref(v___y_456_);
    return v_res_461_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(
    mut v_x_462_: *mut LeanObject,
    mut v_x_463_: *mut LeanObject,
    mut v_x_464_: *mut LeanObject,
    mut v_x_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_470_: u8 = 0;
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_472_: u8 = 0;
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: u8 = 0;
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_466_ = lean_ctor_get(v_x_462_, 0);
                v_vs_467_ = lean_ctor_get(v_x_462_, 1);
                v_isSharedCheck_491_ = (!lean_is_exclusive(v_x_462_)) as u8;
                if v_isSharedCheck_491_ == 0 {
                    v___x_469_ = v_x_462_;
                    v_isShared_470_ = v_isSharedCheck_491_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_467_);
                    lean_inc(v_ks_466_);
                    lean_dec(v_x_462_);
                    v___x_469_ = lean_box(0);
                    v_isShared_470_ = v_isSharedCheck_491_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_471_ = lean_array_get_size(v_ks_466_);
                v___x_472_ = lean_nat_dec_lt(v_x_463_, v___x_471_);
                if v___x_472_ == 0 {
                    lean_dec(v_x_463_);
                    v___x_473_ = lean_array_push(v_ks_466_, v_x_464_);
                    v___x_474_ = lean_array_push(v_vs_467_, v_x_465_);
                    if v_isShared_470_ == 0 {
                        lean_ctor_set(v___x_469_, 1, v___x_474_);
                        lean_ctor_set(v___x_469_, 0, v___x_473_);
                        v___x_476_ = v___x_469_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_473_);
                        lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_474_);
                        v___x_476_ = v_reuseFailAlloc_477_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_478_ = lean_array_fget_borrowed(v_ks_466_, v_x_463_);
                    v___x_479_ = l_Lean_instBEqMVarId_beq(v_x_464_, v_k_x27_478_);
                    if v___x_479_ == 0 {
                        if v_isShared_470_ == 0 {
                            v___x_481_ = v___x_469_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_485_, 0, v_ks_466_);
                            lean_ctor_set(v_reuseFailAlloc_485_, 1, v_vs_467_);
                            v___x_481_ = v_reuseFailAlloc_485_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_486_ = lean_array_fset(v_ks_466_, v_x_463_, v_x_464_);
                        v___x_487_ = lean_array_fset(v_vs_467_, v_x_463_, v_x_465_);
                        lean_dec(v_x_463_);
                        if v_isShared_470_ == 0 {
                            lean_ctor_set(v___x_469_, 1, v___x_487_);
                            lean_ctor_set(v___x_469_, 0, v___x_486_);
                            v___x_489_ = v___x_469_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_486_);
                            lean_ctor_set(v_reuseFailAlloc_490_, 1, v___x_487_);
                            v___x_489_ = v_reuseFailAlloc_490_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_476_;
            }
            3 => {
                v___x_482_ = lean_unsigned_to_nat(1);
                v___x_483_ = lean_nat_add(v_x_463_, v___x_482_);
                lean_dec(v_x_463_);
                v_x_462_ = v___x_481_;
                v_x_463_ = v___x_483_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_489_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_n_492_: *mut LeanObject,
    mut v_k_493_: *mut LeanObject,
    mut v_v_494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    v___x_495_ = lean_unsigned_to_nat(0);
    v___x_496_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_492_, v___x_495_, v_k_493_, v_v_494_);
    return v___x_496_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_497_: usize = 0;
    let mut v___x_498_: usize = 0;
    let mut v___x_499_: usize = 0;
    v___x_497_ = 5usize;
    v___x_498_ = 1usize;
    v___x_499_ = lean_usize_shift_left(v___x_498_, v___x_497_);
    return v___x_499_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_500_: usize = 0;
    let mut v___x_501_: usize = 0;
    let mut v___x_502_: usize = 0;
    v___x_500_ = 1usize;
    v___x_501_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_502_ = lean_usize_sub(v___x_501_, v___x_500_);
    return v___x_502_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    v___x_503_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_503_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg(
    mut v_x_504_: *mut LeanObject,
    mut v_x_505_: usize,
    mut v_x_506_: usize,
    mut v_x_507_: *mut LeanObject,
    mut v_x_508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_510_: usize = 0;
    let mut v___x_511_: usize = 0;
    let mut v___x_512_: usize = 0;
    let mut v___x_513_: usize = 0;
    let mut v_j_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u8 = 0;
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_519_: u8 = 0;
    let mut v_v_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_533_: u8 = 0;
    let mut v___x_534_: u8 = 0;
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_540_: u8 = 0;
    let mut v_node_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_544_: u8 = 0;
    let mut v___x_545_: usize = 0;
    let mut v___x_546_: usize = 0;
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_551_: u8 = 0;
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_553_: u8 = 0;
    let mut v_unused_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_559_: u8 = 0;
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_564_: u8 = 0;
    let mut v_ks_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: usize = 0;
    let mut v___x_571_: u8 = 0;
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: u8 = 0;
    let mut v_reuseFailAlloc_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_504_) == 0 {
                    v_es_509_ = lean_ctor_get(v_x_504_, 0);
                    v___x_510_ = 5usize;
                    v___x_511_ = 1usize;
                    v___x_512_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_513_ = lean_usize_land(v_x_505_, v___x_512_);
                    v_j_514_ = lean_usize_to_nat(v___x_513_);
                    v___x_515_ = lean_array_get_size(v_es_509_);
                    v___x_516_ = lean_nat_dec_lt(v_j_514_, v___x_515_);
                    if v___x_516_ == 0 {
                        lean_dec(v_j_514_);
                        lean_dec(v_x_508_);
                        lean_dec(v_x_507_);
                        return v_x_504_;
                    } else {
                        lean_inc_ref(v_es_509_);
                        v_isSharedCheck_553_ = (!lean_is_exclusive(v_x_504_)) as u8;
                        if v_isSharedCheck_553_ == 0 {
                            v_unused_554_ = lean_ctor_get(v_x_504_, 0);
                            lean_dec(v_unused_554_);
                            v___x_518_ = v_x_504_;
                            v_isShared_519_ = v_isSharedCheck_553_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_504_);
                            v___x_518_ = lean_box(0);
                            v_isShared_519_ = v_isSharedCheck_553_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_555_ = lean_ctor_get(v_x_504_, 0);
                    v_vs_556_ = lean_ctor_get(v_x_504_, 1);
                    v_isSharedCheck_576_ = (!lean_is_exclusive(v_x_504_)) as u8;
                    if v_isSharedCheck_576_ == 0 {
                        v___x_558_ = v_x_504_;
                        v_isShared_559_ = v_isSharedCheck_576_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_556_);
                        lean_inc(v_ks_555_);
                        lean_dec(v_x_504_);
                        v___x_558_ = lean_box(0);
                        v_isShared_559_ = v_isSharedCheck_576_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_520_ = lean_array_fget(v_es_509_, v_j_514_);
                v___x_521_ = lean_box(0);
                v_xs_x27_522_ = lean_array_fset(v_es_509_, v_j_514_, v___x_521_);
                match lean_obj_tag(v_v_520_) {
                    0 => {
                        v_key_529_ = lean_ctor_get(v_v_520_, 0);
                        v_val_530_ = lean_ctor_get(v_v_520_, 1);
                        v_isSharedCheck_540_ = (!lean_is_exclusive(v_v_520_)) as u8;
                        if v_isSharedCheck_540_ == 0 {
                            v___x_532_ = v_v_520_;
                            v_isShared_533_ = v_isSharedCheck_540_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_530_);
                            lean_inc(v_key_529_);
                            lean_dec(v_v_520_);
                            v___x_532_ = lean_box(0);
                            v_isShared_533_ = v_isSharedCheck_540_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_541_ = lean_ctor_get(v_v_520_, 0);
                        v_isSharedCheck_551_ = (!lean_is_exclusive(v_v_520_)) as u8;
                        if v_isSharedCheck_551_ == 0 {
                            v___x_543_ = v_v_520_;
                            v_isShared_544_ = v_isSharedCheck_551_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_541_);
                            lean_dec(v_v_520_);
                            v___x_543_ = lean_box(0);
                            v_isShared_544_ = v_isSharedCheck_551_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_552_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_552_, 0, v_x_507_);
                        lean_ctor_set(v___x_552_, 1, v_x_508_);
                        v___y_524_ = v___x_552_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_525_ = lean_array_fset(v_xs_x27_522_, v_j_514_, v___y_524_);
                lean_dec(v_j_514_);
                if v_isShared_519_ == 0 {
                    lean_ctor_set(v___x_518_, 0, v___x_525_);
                    v___x_527_ = v___x_518_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
                    v___x_527_ = v_reuseFailAlloc_528_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_527_;
            }
            4 => {
                v___x_534_ = l_Lean_instBEqMVarId_beq(v_x_507_, v_key_529_);
                if v___x_534_ == 0 {
                    lean_del_object(v___x_532_);
                    v___x_535_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_529_, v_val_530_, v_x_507_, v_x_508_,
                    );
                    v___x_536_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_536_, 0, v___x_535_);
                    v___y_524_ = v___x_536_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_530_);
                    lean_dec(v_key_529_);
                    if v_isShared_533_ == 0 {
                        lean_ctor_set(v___x_532_, 1, v_x_508_);
                        lean_ctor_set(v___x_532_, 0, v_x_507_);
                        v___x_538_ = v___x_532_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_539_, 0, v_x_507_);
                        lean_ctor_set(v_reuseFailAlloc_539_, 1, v_x_508_);
                        v___x_538_ = v_reuseFailAlloc_539_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_524_ = v___x_538_;
                state = 2;
                continue;
            }
            6 => {
                v___x_545_ = lean_usize_shift_right(v_x_505_, v___x_510_);
                v___x_546_ = lean_usize_add(v_x_506_, v___x_511_);
                v___x_547_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg(v_node_541_, v___x_545_, v___x_546_, v_x_507_, v_x_508_);
                if v_isShared_544_ == 0 {
                    lean_ctor_set(v___x_543_, 0, v___x_547_);
                    v___x_549_ = v___x_543_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
                    v___x_549_ = v_reuseFailAlloc_550_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_524_ = v___x_549_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_559_ == 0 {
                    v___x_561_ = v___x_558_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_575_, 0, v_ks_555_);
                    lean_ctor_set(v_reuseFailAlloc_575_, 1, v_vs_556_);
                    v___x_561_ = v_reuseFailAlloc_575_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_562_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__3___redArg(v___x_561_, v_x_507_, v_x_508_);
                v___x_570_ = 7usize;
                v___x_571_ = lean_usize_dec_le(v___x_570_, v_x_506_);
                if v___x_571_ == 0 {
                    v___x_572_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_562_);
                    v___x_573_ = lean_unsigned_to_nat(4);
                    v___x_574_ = lean_nat_dec_lt(v___x_572_, v___x_573_);
                    lean_dec(v___x_572_);
                    v___y_564_ = v___x_574_;
                    state = 10;
                    continue;
                } else {
                    v___y_564_ = v___x_571_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_564_ == 0 {
                    v_ks_565_ = lean_ctor_get(v_newNode_562_, 0);
                    lean_inc_ref(v_ks_565_);
                    v_vs_566_ = lean_ctor_get(v_newNode_562_, 1);
                    lean_inc_ref(v_vs_566_);
                    lean_dec_ref(v_newNode_562_);
                    v___x_567_ = lean_unsigned_to_nat(0);
                    v___x_568_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_569_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__4___redArg(v_x_506_, v_ks_565_, v_vs_566_, v___x_567_, v___x_568_);
                    lean_dec_ref(v_vs_566_);
                    lean_dec_ref(v_ks_565_);
                    return v___x_569_;
                } else {
                    return v_newNode_562_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_depth_577_: usize,
    mut v_keys_578_: *mut LeanObject,
    mut v_vals_579_: *mut LeanObject,
    mut v_i_580_: *mut LeanObject,
    mut v_entries_581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: u8 = 0;
    let mut v_k_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u64 = 0;
    let mut v_h_587_: usize = 0;
    let mut v___x_588_: usize = 0;
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: usize = 0;
    let mut v___x_591_: usize = 0;
    let mut v___x_592_: usize = 0;
    let mut v_h_593_: usize = 0;
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_582_ = lean_array_get_size(v_keys_578_);
                v___x_583_ = lean_nat_dec_lt(v_i_580_, v___x_582_);
                if v___x_583_ == 0 {
                    lean_dec(v_i_580_);
                    return v_entries_581_;
                } else {
                    v_k_584_ = lean_array_fget_borrowed(v_keys_578_, v_i_580_);
                    v_v_585_ = lean_array_fget_borrowed(v_vals_579_, v_i_580_);
                    v___x_586_ = l_Lean_instHashableMVarId_hash(v_k_584_);
                    v_h_587_ = lean_uint64_to_usize(v___x_586_);
                    v___x_588_ = 5usize;
                    v___x_589_ = lean_unsigned_to_nat(1);
                    v___x_590_ = 1usize;
                    v___x_591_ = lean_usize_sub(v_depth_577_, v___x_590_);
                    v___x_592_ = lean_usize_mul(v___x_588_, v___x_591_);
                    v_h_593_ = lean_usize_shift_right(v_h_587_, v___x_592_);
                    v___x_594_ = lean_nat_add(v_i_580_, v___x_589_);
                    lean_dec(v_i_580_);
                    lean_inc(v_v_585_);
                    lean_inc(v_k_584_);
                    v___x_595_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg(v_entries_581_, v_h_593_, v_depth_577_, v_k_584_, v_v_585_);
                    v_i_580_ = v___x_594_;
                    v_entries_581_ = v___x_595_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_depth_597_: *mut LeanObject,
    mut v_keys_598_: *mut LeanObject,
    mut v_vals_599_: *mut LeanObject,
    mut v_i_600_: *mut LeanObject,
    mut v_entries_601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_602_: usize = 0;
    let mut v_res_603_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_602_ = lean_unbox_usize(v_depth_597_);
    lean_dec(v_depth_597_);
    v_res_603_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_602_, v_keys_598_, v_vals_599_, v_i_600_, v_entries_601_);
    lean_dec_ref(v_vals_599_);
    lean_dec_ref(v_keys_598_);
    return v_res_603_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_604_: *mut LeanObject,
    mut v_x_605_: *mut LeanObject,
    mut v_x_606_: *mut LeanObject,
    mut v_x_607_: *mut LeanObject,
    mut v_x_608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1519__boxed_609_: usize = 0;
    let mut v_x_1520__boxed_610_: usize = 0;
    let mut v_res_611_: *mut LeanObject = core::ptr::null_mut();
    v_x_1519__boxed_609_ = lean_unbox_usize(v_x_605_);
    lean_dec(v_x_605_);
    v_x_1520__boxed_610_ = lean_unbox_usize(v_x_606_);
    lean_dec(v_x_606_);
    v_res_611_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg(v_x_604_, v_x_1519__boxed_609_, v_x_1520__boxed_610_, v_x_607_, v_x_608_);
    return v_res_611_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0___redArg(
    mut v_x_612_: *mut LeanObject,
    mut v_x_613_: *mut LeanObject,
    mut v_x_614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_615_: u64 = 0;
    let mut v___x_616_: usize = 0;
    let mut v___x_617_: usize = 0;
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    v___x_615_ = l_Lean_instHashableMVarId_hash(v_x_613_);
    v___x_616_ = lean_uint64_to_usize(v___x_615_);
    v___x_617_ = 1usize;
    v___x_618_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg(v_x_612_, v___x_616_, v___x_617_, v_x_613_, v_x_614_);
    return v___x_618_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0___redArg(
    mut v_mvarId_619_: *mut LeanObject,
    mut v_val_620_: *mut LeanObject,
    mut v___y_621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_631_: u8 = 0;
    let mut v_depth_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_644_: u8 = 0;
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_655_: u8 = 0;
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_623_ = lean_st_ref_take(v___y_621_);
                v_mctx_624_ = lean_ctor_get(v___x_623_, 0);
                v_cache_625_ = lean_ctor_get(v___x_623_, 1);
                v_zetaDeltaFVarIds_626_ = lean_ctor_get(v___x_623_, 2);
                v_postponed_627_ = lean_ctor_get(v___x_623_, 3);
                v_diag_628_ = lean_ctor_get(v___x_623_, 4);
                v_isSharedCheck_656_ = (!lean_is_exclusive(v___x_623_)) as u8;
                if v_isSharedCheck_656_ == 0 {
                    v___x_630_ = v___x_623_;
                    v_isShared_631_ = v_isSharedCheck_656_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_628_);
                    lean_inc(v_postponed_627_);
                    lean_inc(v_zetaDeltaFVarIds_626_);
                    lean_inc(v_cache_625_);
                    lean_inc(v_mctx_624_);
                    lean_dec(v___x_623_);
                    v___x_630_ = lean_box(0);
                    v_isShared_631_ = v_isSharedCheck_656_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_632_ = lean_ctor_get(v_mctx_624_, 0);
                v_levelAssignDepth_633_ = lean_ctor_get(v_mctx_624_, 1);
                v_lmvarCounter_634_ = lean_ctor_get(v_mctx_624_, 2);
                v_mvarCounter_635_ = lean_ctor_get(v_mctx_624_, 3);
                v_lDecls_636_ = lean_ctor_get(v_mctx_624_, 4);
                v_decls_637_ = lean_ctor_get(v_mctx_624_, 5);
                v_userNames_638_ = lean_ctor_get(v_mctx_624_, 6);
                v_lAssignment_639_ = lean_ctor_get(v_mctx_624_, 7);
                v_eAssignment_640_ = lean_ctor_get(v_mctx_624_, 8);
                v_dAssignment_641_ = lean_ctor_get(v_mctx_624_, 9);
                v_isSharedCheck_655_ = (!lean_is_exclusive(v_mctx_624_)) as u8;
                if v_isSharedCheck_655_ == 0 {
                    v___x_643_ = v_mctx_624_;
                    v_isShared_644_ = v_isSharedCheck_655_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_641_);
                    lean_inc(v_eAssignment_640_);
                    lean_inc(v_lAssignment_639_);
                    lean_inc(v_userNames_638_);
                    lean_inc(v_decls_637_);
                    lean_inc(v_lDecls_636_);
                    lean_inc(v_mvarCounter_635_);
                    lean_inc(v_lmvarCounter_634_);
                    lean_inc(v_levelAssignDepth_633_);
                    lean_inc(v_depth_632_);
                    lean_dec(v_mctx_624_);
                    v___x_643_ = lean_box(0);
                    v_isShared_644_ = v_isSharedCheck_655_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_645_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0___redArg(v_eAssignment_640_, v_mvarId_619_, v_val_620_);
                if v_isShared_644_ == 0 {
                    lean_ctor_set(v___x_643_, 8, v___x_645_);
                    v___x_647_ = v___x_643_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_654_, 0, v_depth_632_);
                    lean_ctor_set(v_reuseFailAlloc_654_, 1, v_levelAssignDepth_633_);
                    lean_ctor_set(v_reuseFailAlloc_654_, 2, v_lmvarCounter_634_);
                    lean_ctor_set(v_reuseFailAlloc_654_, 3, v_mvarCounter_635_);
                    lean_ctor_set(v_reuseFailAlloc_654_, 4, v_lDecls_636_);
                    lean_ctor_set(v_reuseFailAlloc_654_, 5, v_decls_637_);
                    lean_ctor_set(v_reuseFailAlloc_654_, 6, v_userNames_638_);
                    lean_ctor_set(v_reuseFailAlloc_654_, 7, v_lAssignment_639_);
                    lean_ctor_set(v_reuseFailAlloc_654_, 8, v___x_645_);
                    lean_ctor_set(v_reuseFailAlloc_654_, 9, v_dAssignment_641_);
                    v___x_647_ = v_reuseFailAlloc_654_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_631_ == 0 {
                    lean_ctor_set(v___x_630_, 0, v___x_647_);
                    v___x_649_ = v___x_630_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_647_);
                    lean_ctor_set(v_reuseFailAlloc_653_, 1, v_cache_625_);
                    lean_ctor_set(v_reuseFailAlloc_653_, 2, v_zetaDeltaFVarIds_626_);
                    lean_ctor_set(v_reuseFailAlloc_653_, 3, v_postponed_627_);
                    lean_ctor_set(v_reuseFailAlloc_653_, 4, v_diag_628_);
                    v___x_649_ = v_reuseFailAlloc_653_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_650_ = lean_st_ref_set(v___y_621_, v___x_649_);
                v___x_651_ = lean_box(0);
                v___x_652_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_652_, 0, v___x_651_);
                return v___x_652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0___redArg___boxed(
    mut v_mvarId_657_: *mut LeanObject,
    mut v_val_658_: *mut LeanObject,
    mut v___y_659_: *mut LeanObject,
    mut v___y_660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_661_: *mut LeanObject = core::ptr::null_mut();
    v_res_661_ = l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0___redArg(
        v_mvarId_657_,
        v_val_658_,
        v___y_659_,
    );
    lean_dec(v___y_659_);
    return v_res_661_;
}
pub unsafe fn l_Lean_MVarId_rename___lam__0(
    mut v_mvarId_662_: *mut LeanObject,
    mut v___x_663_: *mut LeanObject,
    mut v_fvarId_664_: *mut LeanObject,
    mut v_userNameNew_665_: *mut LeanObject,
    mut v___y_666_: *mut LeanObject,
    mut v___y_667_: *mut LeanObject,
    mut v___y_668_: *mut LeanObject,
    mut v___y_669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: u8 = 0;
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_686_: u8 = 0;
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_691_: u8 = 0;
    let mut v_unused_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_696_: u8 = 0;
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_700_: u8 = 0;
    let mut v_a_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_704_: u8 = 0;
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_708_: u8 = 0;
    let mut v_a_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_712_: u8 = 0;
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_716_: u8 = 0;
    let mut v_a_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_720_: u8 = 0;
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_662_);
                v___x_671_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_662_,
                    v___x_663_,
                    v___y_666_,
                    v___y_667_,
                    v___y_668_,
                    v___y_669_,
                );
                if lean_obj_tag(v___x_671_) == 0 {
                    lean_dec_ref_known(v___x_671_, 1);
                    lean_inc(v_mvarId_662_);
                    v___x_672_ = l_Lean_MVarId_getType(
                        v_mvarId_662_,
                        v___y_666_,
                        v___y_667_,
                        v___y_668_,
                        v___y_669_,
                    );
                    if lean_obj_tag(v___x_672_) == 0 {
                        v_a_673_ = lean_ctor_get(v___x_672_, 0);
                        lean_inc(v_a_673_);
                        lean_dec_ref_known(v___x_672_, 1);
                        lean_inc(v_mvarId_662_);
                        v___x_674_ = l_Lean_MVarId_getTag(
                            v_mvarId_662_,
                            v___y_666_,
                            v___y_667_,
                            v___y_668_,
                            v___y_669_,
                        );
                        if lean_obj_tag(v___x_674_) == 0 {
                            v_a_675_ = lean_ctor_get(v___x_674_, 0);
                            lean_inc(v_a_675_);
                            lean_dec_ref_known(v___x_674_, 1);
                            v_lctx_676_ = lean_ctor_get(v___y_666_, 2);
                            v_localInstances_677_ = lean_ctor_get(v___y_666_, 3);
                            lean_inc_ref(v_localInstances_677_);
                            lean_inc_ref(v_lctx_676_);
                            v___x_678_ = l_Lean_LocalContext_setUserName(
                                v_lctx_676_,
                                v_fvarId_664_,
                                v_userNameNew_665_,
                            );
                            v___x_679_ = 2;
                            v___x_680_ = lean_unsigned_to_nat(0);
                            v___x_681_ = l_Lean_Meta_mkFreshExprMVarAt(
                                v___x_678_,
                                v_localInstances_677_,
                                v_a_673_,
                                v___x_679_,
                                v_a_675_,
                                v___x_680_,
                                v___y_666_,
                                v___y_667_,
                                v___y_668_,
                                v___y_669_,
                            );
                            lean_dec_ref(v___y_666_);
                            if lean_obj_tag(v___x_681_) == 0 {
                                v_a_682_ = lean_ctor_get(v___x_681_, 0);
                                lean_inc_n(v_a_682_, 2);
                                lean_dec_ref_known(v___x_681_, 1);
                                v___x_683_ = l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0___redArg(v_mvarId_662_, v_a_682_, v___y_667_);
                                v_isSharedCheck_691_ = (!lean_is_exclusive(v___x_683_)) as u8;
                                if v_isSharedCheck_691_ == 0 {
                                    v_unused_692_ = lean_ctor_get(v___x_683_, 0);
                                    lean_dec(v_unused_692_);
                                    v___x_685_ = v___x_683_;
                                    v_isShared_686_ = v_isSharedCheck_691_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v___x_683_);
                                    v___x_685_ = lean_box(0);
                                    v_isShared_686_ = v_isSharedCheck_691_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_mvarId_662_);
                                v_a_693_ = lean_ctor_get(v___x_681_, 0);
                                v_isSharedCheck_700_ = (!lean_is_exclusive(v___x_681_)) as u8;
                                if v_isSharedCheck_700_ == 0 {
                                    v___x_695_ = v___x_681_;
                                    v_isShared_696_ = v_isSharedCheck_700_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_693_);
                                    lean_dec(v___x_681_);
                                    v___x_695_ = lean_box(0);
                                    v_isShared_696_ = v_isSharedCheck_700_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_673_);
                            lean_dec_ref(v___y_666_);
                            lean_dec(v_userNameNew_665_);
                            lean_dec(v_fvarId_664_);
                            lean_dec(v_mvarId_662_);
                            v_a_701_ = lean_ctor_get(v___x_674_, 0);
                            v_isSharedCheck_708_ = (!lean_is_exclusive(v___x_674_)) as u8;
                            if v_isSharedCheck_708_ == 0 {
                                v___x_703_ = v___x_674_;
                                v_isShared_704_ = v_isSharedCheck_708_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_701_);
                                lean_dec(v___x_674_);
                                v___x_703_ = lean_box(0);
                                v_isShared_704_ = v_isSharedCheck_708_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_666_);
                        lean_dec(v_userNameNew_665_);
                        lean_dec(v_fvarId_664_);
                        lean_dec(v_mvarId_662_);
                        v_a_709_ = lean_ctor_get(v___x_672_, 0);
                        v_isSharedCheck_716_ = (!lean_is_exclusive(v___x_672_)) as u8;
                        if v_isSharedCheck_716_ == 0 {
                            v___x_711_ = v___x_672_;
                            v_isShared_712_ = v_isSharedCheck_716_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_709_);
                            lean_dec(v___x_672_);
                            v___x_711_ = lean_box(0);
                            v_isShared_712_ = v_isSharedCheck_716_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_666_);
                    lean_dec(v_userNameNew_665_);
                    lean_dec(v_fvarId_664_);
                    lean_dec(v_mvarId_662_);
                    v_a_717_ = lean_ctor_get(v___x_671_, 0);
                    v_isSharedCheck_724_ = (!lean_is_exclusive(v___x_671_)) as u8;
                    if v_isSharedCheck_724_ == 0 {
                        v___x_719_ = v___x_671_;
                        v_isShared_720_ = v_isSharedCheck_724_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_717_);
                        lean_dec(v___x_671_);
                        v___x_719_ = lean_box(0);
                        v_isShared_720_ = v_isSharedCheck_724_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_687_ = l_Lean_Expr_mvarId_x21(v_a_682_);
                lean_dec(v_a_682_);
                if v_isShared_686_ == 0 {
                    lean_ctor_set(v___x_685_, 0, v___x_687_);
                    v___x_689_ = v___x_685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
                    v___x_689_ = v_reuseFailAlloc_690_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_689_;
            }
            3 => {
                if v_isShared_696_ == 0 {
                    v___x_698_ = v___x_695_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
                    v___x_698_ = v_reuseFailAlloc_699_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_698_;
            }
            5 => {
                if v_isShared_704_ == 0 {
                    v___x_706_ = v___x_703_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
                    v___x_706_ = v_reuseFailAlloc_707_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_706_;
            }
            7 => {
                if v_isShared_712_ == 0 {
                    v___x_714_ = v___x_711_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
                    v___x_714_ = v_reuseFailAlloc_715_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_714_;
            }
            9 => {
                if v_isShared_720_ == 0 {
                    v___x_722_ = v___x_719_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
                    v___x_722_ = v_reuseFailAlloc_723_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_rename___lam__0___boxed(
    mut v_mvarId_725_: *mut LeanObject,
    mut v___x_726_: *mut LeanObject,
    mut v_fvarId_727_: *mut LeanObject,
    mut v_userNameNew_728_: *mut LeanObject,
    mut v___y_729_: *mut LeanObject,
    mut v___y_730_: *mut LeanObject,
    mut v___y_731_: *mut LeanObject,
    mut v___y_732_: *mut LeanObject,
    mut v___y_733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_734_: *mut LeanObject = core::ptr::null_mut();
    v_res_734_ = l_Lean_MVarId_rename___lam__0(
        v_mvarId_725_,
        v___x_726_,
        v_fvarId_727_,
        v_userNameNew_728_,
        v___y_729_,
        v___y_730_,
        v___y_731_,
        v___y_732_,
    );
    lean_dec(v___y_732_);
    lean_dec_ref(v___y_731_);
    lean_dec(v___y_730_);
    return v_res_734_;
}
pub unsafe fn l_Lean_MVarId_rename(
    mut v_mvarId_738_: *mut LeanObject,
    mut v_fvarId_739_: *mut LeanObject,
    mut v_userNameNew_740_: *mut LeanObject,
    mut v_a_741_: *mut LeanObject,
    mut v_a_742_: *mut LeanObject,
    mut v_a_743_: *mut LeanObject,
    mut v_a_744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    v___x_746_ = l_Lean_MVarId_rename___closed__1;
    lean_inc(v_mvarId_738_);
    v___f_747_ = lean_alloc_closure(
        l_Lean_MVarId_rename___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___f_747_, 0, v_mvarId_738_);
    lean_closure_set(v___f_747_, 1, v___x_746_);
    lean_closure_set(v___f_747_, 2, v_fvarId_739_);
    lean_closure_set(v___f_747_, 3, v_userNameNew_740_);
    v___x_748_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rename_spec__1___redArg(
        v_mvarId_738_,
        v___f_747_,
        v_a_741_,
        v_a_742_,
        v_a_743_,
        v_a_744_,
    );
    return v___x_748_;
}
pub unsafe fn l_Lean_MVarId_rename___boxed(
    mut v_mvarId_749_: *mut LeanObject,
    mut v_fvarId_750_: *mut LeanObject,
    mut v_userNameNew_751_: *mut LeanObject,
    mut v_a_752_: *mut LeanObject,
    mut v_a_753_: *mut LeanObject,
    mut v_a_754_: *mut LeanObject,
    mut v_a_755_: *mut LeanObject,
    mut v_a_756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_757_: *mut LeanObject = core::ptr::null_mut();
    v_res_757_ = l_Lean_MVarId_rename(
        v_mvarId_749_,
        v_fvarId_750_,
        v_userNameNew_751_,
        v_a_752_,
        v_a_753_,
        v_a_754_,
        v_a_755_,
    );
    lean_dec(v_a_755_);
    lean_dec_ref(v_a_754_);
    lean_dec(v_a_753_);
    lean_dec_ref(v_a_752_);
    return v_res_757_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0(
    mut v_mvarId_758_: *mut LeanObject,
    mut v_val_759_: *mut LeanObject,
    mut v___y_760_: *mut LeanObject,
    mut v___y_761_: *mut LeanObject,
    mut v___y_762_: *mut LeanObject,
    mut v___y_763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    v___x_765_ = l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0___redArg(
        v_mvarId_758_,
        v_val_759_,
        v___y_761_,
    );
    return v___x_765_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0___boxed(
    mut v_mvarId_766_: *mut LeanObject,
    mut v_val_767_: *mut LeanObject,
    mut v___y_768_: *mut LeanObject,
    mut v___y_769_: *mut LeanObject,
    mut v___y_770_: *mut LeanObject,
    mut v___y_771_: *mut LeanObject,
    mut v___y_772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_773_: *mut LeanObject = core::ptr::null_mut();
    v_res_773_ = l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0(
        v_mvarId_766_,
        v_val_767_,
        v___y_768_,
        v___y_769_,
        v___y_770_,
        v___y_771_,
    );
    lean_dec(v___y_771_);
    lean_dec_ref(v___y_770_);
    lean_dec(v___y_769_);
    lean_dec_ref(v___y_768_);
    return v_res_773_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0(
    mut v_00_u03b2_774_: *mut LeanObject,
    mut v_x_775_: *mut LeanObject,
    mut v_x_776_: *mut LeanObject,
    mut v_x_777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    v___x_778_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0___redArg(v_x_775_, v_x_776_, v_x_777_);
    return v___x_778_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2(
    mut v_00_u03b2_779_: *mut LeanObject,
    mut v_x_780_: *mut LeanObject,
    mut v_x_781_: usize,
    mut v_x_782_: usize,
    mut v_x_783_: *mut LeanObject,
    mut v_x_784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    v___x_785_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg(v_x_780_, v_x_781_, v_x_782_, v_x_783_, v_x_784_);
    return v___x_785_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_786_: *mut LeanObject,
    mut v_x_787_: *mut LeanObject,
    mut v_x_788_: *mut LeanObject,
    mut v_x_789_: *mut LeanObject,
    mut v_x_790_: *mut LeanObject,
    mut v_x_791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1907__boxed_792_: usize = 0;
    let mut v_x_1908__boxed_793_: usize = 0;
    let mut v_res_794_: *mut LeanObject = core::ptr::null_mut();
    v_x_1907__boxed_792_ = lean_unbox_usize(v_x_788_);
    lean_dec(v_x_788_);
    v_x_1908__boxed_793_ = lean_unbox_usize(v_x_789_);
    lean_dec(v_x_789_);
    v_res_794_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2(v_00_u03b2_786_, v_x_787_, v_x_1907__boxed_792_, v_x_1908__boxed_793_, v_x_790_, v_x_791_);
    return v_res_794_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_795_: *mut LeanObject,
    mut v_n_796_: *mut LeanObject,
    mut v_k_797_: *mut LeanObject,
    mut v_v_798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    v___x_799_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__3___redArg(v_n_796_, v_k_797_, v_v_798_);
    return v___x_799_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_800_: *mut LeanObject,
    mut v_depth_801_: usize,
    mut v_keys_802_: *mut LeanObject,
    mut v_vals_803_: *mut LeanObject,
    mut v_heq_804_: *mut LeanObject,
    mut v_i_805_: *mut LeanObject,
    mut v_entries_806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    v___x_807_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_801_, v_keys_802_, v_vals_803_, v_i_805_, v_entries_806_);
    return v___x_807_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_808_: *mut LeanObject,
    mut v_depth_809_: *mut LeanObject,
    mut v_keys_810_: *mut LeanObject,
    mut v_vals_811_: *mut LeanObject,
    mut v_heq_812_: *mut LeanObject,
    mut v_i_813_: *mut LeanObject,
    mut v_entries_814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_815_: usize = 0;
    let mut v_res_816_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_815_ = lean_unbox_usize(v_depth_809_);
    lean_dec(v_depth_809_);
    v_res_816_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_808_, v_depth_boxed_815_, v_keys_810_, v_vals_811_, v_heq_812_, v_i_813_, v_entries_814_);
    lean_dec_ref(v_vals_811_);
    lean_dec_ref(v_keys_810_);
    return v_res_816_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_00_u03b2_817_: *mut LeanObject,
    mut v_x_818_: *mut LeanObject,
    mut v_x_819_: *mut LeanObject,
    mut v_x_820_: *mut LeanObject,
    mut v_x_821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    v___x_822_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_818_, v_x_819_, v_x_820_, v_x_821_);
    return v___x_822_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Rename(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Rename(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Rename(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rename(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Rename(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Rename(builtin);
}
