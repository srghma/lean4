// Lean compiler output
// Module: Lean.Meta.Tactic.Rename
// Imports: Lean.Meta.Tactic.Util
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
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_rename___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_rename___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rename___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rename___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_rename___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16251432624378154990 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_rename___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rename___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_rename_spec__1___redArg(
    mut v_mvarId_412_: *mut crate::leanh::LeanObject,
    mut v_x_413_: *mut crate::leanh::LeanObject,
    mut v___y_414_: *mut crate::leanh::LeanObject,
    mut v___y_415_: *mut crate::leanh::LeanObject,
    mut v___y_416_: *mut crate::leanh::LeanObject,
    mut v___y_417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_423_: u8 = 0;
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_427_: u8 = 0;
    let mut v_a_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_431_: u8 = 0;
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_419_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_412_,
                    v_x_413_,
                    v___y_414_,
                    v___y_415_,
                    v___y_416_,
                    v___y_417_,
                );
                if crate::leanh::lean_obj_tag(v___x_419_) == 0 {
                    v_a_420_ = crate::leanh::lean_ctor_get(v___x_419_, 0);
                    v_isSharedCheck_427_ = (!crate::leanh::lean_is_exclusive(v___x_419_)) as u8;
                    if v_isSharedCheck_427_ == 0 {
                        v___x_422_ = v___x_419_;
                        v_isShared_423_ = v_isSharedCheck_427_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_420_);
                        crate::leanh::lean_dec(v___x_419_);
                        v___x_422_ = crate::leanh::lean_box(0);
                        v_isShared_423_ = v_isSharedCheck_427_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_428_ = crate::leanh::lean_ctor_get(v___x_419_, 0);
                    v_isSharedCheck_435_ = (!crate::leanh::lean_is_exclusive(v___x_419_)) as u8;
                    if v_isSharedCheck_435_ == 0 {
                        v___x_430_ = v___x_419_;
                        v_isShared_431_ = v_isSharedCheck_435_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_428_);
                        crate::leanh::lean_dec(v___x_419_);
                        v___x_430_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_426_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
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
                    v_reuseFailAlloc_434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
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
    mut v_mvarId_436_: *mut crate::leanh::LeanObject,
    mut v_x_437_: *mut crate::leanh::LeanObject,
    mut v___y_438_: *mut crate::leanh::LeanObject,
    mut v___y_439_: *mut crate::leanh::LeanObject,
    mut v___y_440_: *mut crate::leanh::LeanObject,
    mut v___y_441_: *mut crate::leanh::LeanObject,
    mut v___y_442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_443_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rename_spec__1___redArg(
        v_mvarId_436_,
        v_x_437_,
        v___y_438_,
        v___y_439_,
        v___y_440_,
        v___y_441_,
    );
    crate::leanh::lean_dec(v___y_441_);
    crate::leanh::lean_dec_ref(v___y_440_);
    crate::leanh::lean_dec(v___y_439_);
    crate::leanh::lean_dec_ref(v___y_438_);
    return v_res_443_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_rename_spec__1(
    mut v_00_u03b1_444_: *mut crate::leanh::LeanObject,
    mut v_mvarId_445_: *mut crate::leanh::LeanObject,
    mut v_x_446_: *mut crate::leanh::LeanObject,
    mut v___y_447_: *mut crate::leanh::LeanObject,
    mut v___y_448_: *mut crate::leanh::LeanObject,
    mut v___y_449_: *mut crate::leanh::LeanObject,
    mut v___y_450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_453_: *mut crate::leanh::LeanObject,
    mut v_mvarId_454_: *mut crate::leanh::LeanObject,
    mut v_x_455_: *mut crate::leanh::LeanObject,
    mut v___y_456_: *mut crate::leanh::LeanObject,
    mut v___y_457_: *mut crate::leanh::LeanObject,
    mut v___y_458_: *mut crate::leanh::LeanObject,
    mut v___y_459_: *mut crate::leanh::LeanObject,
    mut v___y_460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_461_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rename_spec__1(
        v_00_u03b1_453_,
        v_mvarId_454_,
        v_x_455_,
        v___y_456_,
        v___y_457_,
        v___y_458_,
        v___y_459_,
    );
    crate::leanh::lean_dec(v___y_459_);
    crate::leanh::lean_dec_ref(v___y_458_);
    crate::leanh::lean_dec(v___y_457_);
    crate::leanh::lean_dec_ref(v___y_456_);
    return v_res_461_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(
    mut v_x_462_: *mut crate::leanh::LeanObject,
    mut v_x_463_: *mut crate::leanh::LeanObject,
    mut v_x_464_: *mut crate::leanh::LeanObject,
    mut v_x_465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_470_: u8 = 0;
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: u8 = 0;
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: u8 = 0;
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_466_ = crate::leanh::lean_ctor_get(v_x_462_, 0);
                v_vs_467_ = crate::leanh::lean_ctor_get(v_x_462_, 1);
                v_isSharedCheck_491_ = (!crate::leanh::lean_is_exclusive(v_x_462_)) as u8;
                if v_isSharedCheck_491_ == 0 {
                    v___x_469_ = v_x_462_;
                    v_isShared_470_ = v_isSharedCheck_491_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_467_);
                    crate::leanh::lean_inc(v_ks_466_);
                    crate::leanh::lean_dec(v_x_462_);
                    v___x_469_ = crate::leanh::lean_box(0);
                    v_isShared_470_ = v_isSharedCheck_491_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_471_ = lean_array_get_size(v_ks_466_);
                v___x_472_ = lean_nat_dec_lt(v_x_463_, v___x_471_);
                if v___x_472_ == 0 {
                    crate::leanh::lean_dec(v_x_463_);
                    v___x_473_ = lean_array_push(v_ks_466_, v_x_464_);
                    v___x_474_ = lean_array_push(v_vs_467_, v_x_465_);
                    if v_isShared_470_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_469_, 1, v___x_474_);
                        crate::leanh::lean_ctor_set(v___x_469_, 0, v___x_473_);
                        v___x_476_ = v___x_469_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_477_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_473_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_474_);
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
                            v_reuseFailAlloc_485_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 0, v_ks_466_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 1, v_vs_467_);
                            v___x_481_ = v_reuseFailAlloc_485_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_486_ = lean_array_fset(v_ks_466_, v_x_463_, v_x_464_);
                        v___x_487_ = lean_array_fset(v_vs_467_, v_x_463_, v_x_465_);
                        crate::leanh::lean_dec(v_x_463_);
                        if v_isShared_470_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_469_, 1, v___x_487_);
                            crate::leanh::lean_ctor_set(v___x_469_, 0, v___x_486_);
                            v___x_489_ = v___x_469_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_490_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_486_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_490_, 1, v___x_487_);
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
                v___x_482_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_483_ = lean_nat_add(v_x_463_, v___x_482_);
                crate::leanh::lean_dec(v_x_463_);
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
    mut v_n_492_: *mut crate::leanh::LeanObject,
    mut v_k_493_: *mut crate::leanh::LeanObject,
    mut v_v_494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_495_ = crate::leanh::lean_unsigned_to_nat(0);
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
    v___x_501_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_502_ = lean_usize_sub(v___x_501_, v___x_500_);
    return v___x_502_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_503_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_503_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg(
    mut v_x_504_: *mut crate::leanh::LeanObject,
    mut v_x_505_: usize,
    mut v_x_506_: usize,
    mut v_x_507_: *mut crate::leanh::LeanObject,
    mut v_x_508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: usize = 0;
    let mut v___x_511_: usize = 0;
    let mut v___x_512_: usize = 0;
    let mut v___x_513_: usize = 0;
    let mut v_j_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u8 = 0;
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_519_: u8 = 0;
    let mut v_v_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_533_: u8 = 0;
    let mut v___x_534_: u8 = 0;
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_540_: u8 = 0;
    let mut v_node_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_544_: u8 = 0;
    let mut v___x_545_: usize = 0;
    let mut v___x_546_: usize = 0;
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_551_: u8 = 0;
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_553_: u8 = 0;
    let mut v_unused_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_559_: u8 = 0;
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_564_: u8 = 0;
    let mut v_ks_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: usize = 0;
    let mut v___x_571_: u8 = 0;
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: u8 = 0;
    let mut v_reuseFailAlloc_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_504_) == 0 {
                    v_es_509_ = crate::leanh::lean_ctor_get(v_x_504_, 0);
                    v___x_510_ = 5usize;
                    v___x_511_ = 1usize;
                    v___x_512_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_513_ = lean_usize_land(v_x_505_, v___x_512_);
                    v_j_514_ = lean_usize_to_nat(v___x_513_);
                    v___x_515_ = lean_array_get_size(v_es_509_);
                    v___x_516_ = lean_nat_dec_lt(v_j_514_, v___x_515_);
                    if v___x_516_ == 0 {
                        crate::leanh::lean_dec(v_j_514_);
                        crate::leanh::lean_dec(v_x_508_);
                        crate::leanh::lean_dec(v_x_507_);
                        return v_x_504_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_509_);
                        v_isSharedCheck_553_ = (!crate::leanh::lean_is_exclusive(v_x_504_)) as u8;
                        if v_isSharedCheck_553_ == 0 {
                            v_unused_554_ = crate::leanh::lean_ctor_get(v_x_504_, 0);
                            crate::leanh::lean_dec(v_unused_554_);
                            v___x_518_ = v_x_504_;
                            v_isShared_519_ = v_isSharedCheck_553_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_504_);
                            v___x_518_ = crate::leanh::lean_box(0);
                            v_isShared_519_ = v_isSharedCheck_553_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_555_ = crate::leanh::lean_ctor_get(v_x_504_, 0);
                    v_vs_556_ = crate::leanh::lean_ctor_get(v_x_504_, 1);
                    v_isSharedCheck_576_ = (!crate::leanh::lean_is_exclusive(v_x_504_)) as u8;
                    if v_isSharedCheck_576_ == 0 {
                        v___x_558_ = v_x_504_;
                        v_isShared_559_ = v_isSharedCheck_576_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_556_);
                        crate::leanh::lean_inc(v_ks_555_);
                        crate::leanh::lean_dec(v_x_504_);
                        v___x_558_ = crate::leanh::lean_box(0);
                        v_isShared_559_ = v_isSharedCheck_576_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_520_ = lean_array_fget(v_es_509_, v_j_514_);
                v___x_521_ = crate::leanh::lean_box(0);
                v_xs_x27_522_ = lean_array_fset(v_es_509_, v_j_514_, v___x_521_);
                match crate::leanh::lean_obj_tag(v_v_520_) {
                    0 => {
                        v_key_529_ = crate::leanh::lean_ctor_get(v_v_520_, 0);
                        v_val_530_ = crate::leanh::lean_ctor_get(v_v_520_, 1);
                        v_isSharedCheck_540_ = (!crate::leanh::lean_is_exclusive(v_v_520_)) as u8;
                        if v_isSharedCheck_540_ == 0 {
                            v___x_532_ = v_v_520_;
                            v_isShared_533_ = v_isSharedCheck_540_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_530_);
                            crate::leanh::lean_inc(v_key_529_);
                            crate::leanh::lean_dec(v_v_520_);
                            v___x_532_ = crate::leanh::lean_box(0);
                            v_isShared_533_ = v_isSharedCheck_540_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_541_ = crate::leanh::lean_ctor_get(v_v_520_, 0);
                        v_isSharedCheck_551_ = (!crate::leanh::lean_is_exclusive(v_v_520_)) as u8;
                        if v_isSharedCheck_551_ == 0 {
                            v___x_543_ = v_v_520_;
                            v_isShared_544_ = v_isSharedCheck_551_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_541_);
                            crate::leanh::lean_dec(v_v_520_);
                            v___x_543_ = crate::leanh::lean_box(0);
                            v_isShared_544_ = v_isSharedCheck_551_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_552_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_552_, 0, v_x_507_);
                        crate::leanh::lean_ctor_set(v___x_552_, 1, v_x_508_);
                        v___y_524_ = v___x_552_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_525_ = lean_array_fset(v_xs_x27_522_, v_j_514_, v___y_524_);
                crate::leanh::lean_dec(v_j_514_);
                if v_isShared_519_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_518_, 0, v___x_525_);
                    v___x_527_ = v___x_518_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_528_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
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
                    crate::leanh::lean_del_object(v___x_532_);
                    v___x_535_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_529_, v_val_530_, v_x_507_, v_x_508_,
                    );
                    v___x_536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_536_, 0, v___x_535_);
                    v___y_524_ = v___x_536_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_530_);
                    crate::leanh::lean_dec(v_key_529_);
                    if v_isShared_533_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_532_, 1, v_x_508_);
                        crate::leanh::lean_ctor_set(v___x_532_, 0, v_x_507_);
                        v___x_538_ = v___x_532_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_539_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_539_, 0, v_x_507_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_539_, 1, v_x_508_);
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
                    crate::leanh::lean_ctor_set(v___x_543_, 0, v___x_547_);
                    v___x_549_ = v___x_543_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_550_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
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
                    v_reuseFailAlloc_575_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_575_, 0, v_ks_555_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_575_, 1, v_vs_556_);
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
                    v___x_573_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_574_ = lean_nat_dec_lt(v___x_572_, v___x_573_);
                    crate::leanh::lean_dec(v___x_572_);
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
                    v_ks_565_ = crate::leanh::lean_ctor_get(v_newNode_562_, 0);
                    crate::leanh::lean_inc_ref(v_ks_565_);
                    v_vs_566_ = crate::leanh::lean_ctor_get(v_newNode_562_, 1);
                    crate::leanh::lean_inc_ref(v_vs_566_);
                    crate::leanh::lean_dec_ref(v_newNode_562_);
                    v___x_567_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_568_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_569_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__4___redArg(v_x_506_, v_ks_565_, v_vs_566_, v___x_567_, v___x_568_);
                    crate::leanh::lean_dec_ref(v_vs_566_);
                    crate::leanh::lean_dec_ref(v_ks_565_);
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
    mut v_keys_578_: *mut crate::leanh::LeanObject,
    mut v_vals_579_: *mut crate::leanh::LeanObject,
    mut v_i_580_: *mut crate::leanh::LeanObject,
    mut v_entries_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: u8 = 0;
    let mut v_k_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u64 = 0;
    let mut v_h_587_: usize = 0;
    let mut v___x_588_: usize = 0;
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: usize = 0;
    let mut v___x_591_: usize = 0;
    let mut v___x_592_: usize = 0;
    let mut v_h_593_: usize = 0;
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_582_ = lean_array_get_size(v_keys_578_);
                v___x_583_ = lean_nat_dec_lt(v_i_580_, v___x_582_);
                if v___x_583_ == 0 {
                    crate::leanh::lean_dec(v_i_580_);
                    return v_entries_581_;
                } else {
                    v_k_584_ = lean_array_fget_borrowed(v_keys_578_, v_i_580_);
                    v_v_585_ = lean_array_fget_borrowed(v_vals_579_, v_i_580_);
                    v___x_586_ = l_Lean_instHashableMVarId_hash(v_k_584_);
                    v_h_587_ = lean_uint64_to_usize(v___x_586_);
                    v___x_588_ = 5usize;
                    v___x_589_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_590_ = 1usize;
                    v___x_591_ = lean_usize_sub(v_depth_577_, v___x_590_);
                    v___x_592_ = lean_usize_mul(v___x_588_, v___x_591_);
                    v_h_593_ = lean_usize_shift_right(v_h_587_, v___x_592_);
                    v___x_594_ = lean_nat_add(v_i_580_, v___x_589_);
                    crate::leanh::lean_dec(v_i_580_);
                    crate::leanh::lean_inc(v_v_585_);
                    crate::leanh::lean_inc(v_k_584_);
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
    mut v_depth_597_: *mut crate::leanh::LeanObject,
    mut v_keys_598_: *mut crate::leanh::LeanObject,
    mut v_vals_599_: *mut crate::leanh::LeanObject,
    mut v_i_600_: *mut crate::leanh::LeanObject,
    mut v_entries_601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_602_: usize = 0;
    let mut v_res_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_602_ = crate::leanh::lean_unbox_usize(v_depth_597_);
    crate::leanh::lean_dec(v_depth_597_);
    v_res_603_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_602_, v_keys_598_, v_vals_599_, v_i_600_, v_entries_601_);
    crate::leanh::lean_dec_ref(v_vals_599_);
    crate::leanh::lean_dec_ref(v_keys_598_);
    return v_res_603_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_604_: *mut crate::leanh::LeanObject,
    mut v_x_605_: *mut crate::leanh::LeanObject,
    mut v_x_606_: *mut crate::leanh::LeanObject,
    mut v_x_607_: *mut crate::leanh::LeanObject,
    mut v_x_608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1519__boxed_609_: usize = 0;
    let mut v_x_1520__boxed_610_: usize = 0;
    let mut v_res_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1519__boxed_609_ = crate::leanh::lean_unbox_usize(v_x_605_);
    crate::leanh::lean_dec(v_x_605_);
    v_x_1520__boxed_610_ = crate::leanh::lean_unbox_usize(v_x_606_);
    crate::leanh::lean_dec(v_x_606_);
    v_res_611_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg(v_x_604_, v_x_1519__boxed_609_, v_x_1520__boxed_610_, v_x_607_, v_x_608_);
    return v_res_611_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0___redArg(
    mut v_x_612_: *mut crate::leanh::LeanObject,
    mut v_x_613_: *mut crate::leanh::LeanObject,
    mut v_x_614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_615_: u64 = 0;
    let mut v___x_616_: usize = 0;
    let mut v___x_617_: usize = 0;
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_615_ = l_Lean_instHashableMVarId_hash(v_x_613_);
    v___x_616_ = lean_uint64_to_usize(v___x_615_);
    v___x_617_ = 1usize;
    v___x_618_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg(v_x_612_, v___x_616_, v___x_617_, v_x_613_, v_x_614_);
    return v___x_618_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0___redArg(
    mut v_mvarId_619_: *mut crate::leanh::LeanObject,
    mut v_val_620_: *mut crate::leanh::LeanObject,
    mut v___y_621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_631_: u8 = 0;
    let mut v_depth_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_644_: u8 = 0;
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_655_: u8 = 0;
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_623_ = lean_st_ref_take(v___y_621_);
                v_mctx_624_ = crate::leanh::lean_ctor_get(v___x_623_, 0);
                v_cache_625_ = crate::leanh::lean_ctor_get(v___x_623_, 1);
                v_zetaDeltaFVarIds_626_ = crate::leanh::lean_ctor_get(v___x_623_, 2);
                v_postponed_627_ = crate::leanh::lean_ctor_get(v___x_623_, 3);
                v_diag_628_ = crate::leanh::lean_ctor_get(v___x_623_, 4);
                v_isSharedCheck_656_ = (!crate::leanh::lean_is_exclusive(v___x_623_)) as u8;
                if v_isSharedCheck_656_ == 0 {
                    v___x_630_ = v___x_623_;
                    v_isShared_631_ = v_isSharedCheck_656_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_628_);
                    crate::leanh::lean_inc(v_postponed_627_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_626_);
                    crate::leanh::lean_inc(v_cache_625_);
                    crate::leanh::lean_inc(v_mctx_624_);
                    crate::leanh::lean_dec(v___x_623_);
                    v___x_630_ = crate::leanh::lean_box(0);
                    v_isShared_631_ = v_isSharedCheck_656_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_632_ = crate::leanh::lean_ctor_get(v_mctx_624_, 0);
                v_levelAssignDepth_633_ = crate::leanh::lean_ctor_get(v_mctx_624_, 1);
                v_lmvarCounter_634_ = crate::leanh::lean_ctor_get(v_mctx_624_, 2);
                v_mvarCounter_635_ = crate::leanh::lean_ctor_get(v_mctx_624_, 3);
                v_lDecls_636_ = crate::leanh::lean_ctor_get(v_mctx_624_, 4);
                v_decls_637_ = crate::leanh::lean_ctor_get(v_mctx_624_, 5);
                v_userNames_638_ = crate::leanh::lean_ctor_get(v_mctx_624_, 6);
                v_lAssignment_639_ = crate::leanh::lean_ctor_get(v_mctx_624_, 7);
                v_eAssignment_640_ = crate::leanh::lean_ctor_get(v_mctx_624_, 8);
                v_dAssignment_641_ = crate::leanh::lean_ctor_get(v_mctx_624_, 9);
                v_isSharedCheck_655_ = (!crate::leanh::lean_is_exclusive(v_mctx_624_)) as u8;
                if v_isSharedCheck_655_ == 0 {
                    v___x_643_ = v_mctx_624_;
                    v_isShared_644_ = v_isSharedCheck_655_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_641_);
                    crate::leanh::lean_inc(v_eAssignment_640_);
                    crate::leanh::lean_inc(v_lAssignment_639_);
                    crate::leanh::lean_inc(v_userNames_638_);
                    crate::leanh::lean_inc(v_decls_637_);
                    crate::leanh::lean_inc(v_lDecls_636_);
                    crate::leanh::lean_inc(v_mvarCounter_635_);
                    crate::leanh::lean_inc(v_lmvarCounter_634_);
                    crate::leanh::lean_inc(v_levelAssignDepth_633_);
                    crate::leanh::lean_inc(v_depth_632_);
                    crate::leanh::lean_dec(v_mctx_624_);
                    v___x_643_ = crate::leanh::lean_box(0);
                    v_isShared_644_ = v_isSharedCheck_655_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_645_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0___redArg(v_eAssignment_640_, v_mvarId_619_, v_val_620_);
                if v_isShared_644_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_643_, 8, v___x_645_);
                    v___x_647_ = v___x_643_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_654_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 0, v_depth_632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 1, v_levelAssignDepth_633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 2, v_lmvarCounter_634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 3, v_mvarCounter_635_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 4, v_lDecls_636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 5, v_decls_637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 6, v_userNames_638_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 7, v_lAssignment_639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 8, v___x_645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 9, v_dAssignment_641_);
                    v___x_647_ = v_reuseFailAlloc_654_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_631_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_630_, 0, v___x_647_);
                    v___x_649_ = v___x_630_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_653_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 1, v_cache_625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 2, v_zetaDeltaFVarIds_626_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 3, v_postponed_627_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 4, v_diag_628_);
                    v___x_649_ = v_reuseFailAlloc_653_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_650_ = lean_st_ref_set(v___y_621_, v___x_649_);
                v___x_651_ = crate::leanh::lean_box(0);
                v___x_652_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_652_, 0, v___x_651_);
                return v___x_652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0___redArg___boxed(
    mut v_mvarId_657_: *mut crate::leanh::LeanObject,
    mut v_val_658_: *mut crate::leanh::LeanObject,
    mut v___y_659_: *mut crate::leanh::LeanObject,
    mut v___y_660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_661_ = l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0___redArg(
        v_mvarId_657_,
        v_val_658_,
        v___y_659_,
    );
    crate::leanh::lean_dec(v___y_659_);
    return v_res_661_;
}
pub unsafe fn l_Lean_MVarId_rename___lam__0(
    mut v_mvarId_662_: *mut crate::leanh::LeanObject,
    mut v___x_663_: *mut crate::leanh::LeanObject,
    mut v_fvarId_664_: *mut crate::leanh::LeanObject,
    mut v_userNameNew_665_: *mut crate::leanh::LeanObject,
    mut v___y_666_: *mut crate::leanh::LeanObject,
    mut v___y_667_: *mut crate::leanh::LeanObject,
    mut v___y_668_: *mut crate::leanh::LeanObject,
    mut v___y_669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: u8 = 0;
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_686_: u8 = 0;
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_691_: u8 = 0;
    let mut v_unused_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_696_: u8 = 0;
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_700_: u8 = 0;
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
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_662_);
                v___x_671_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_662_,
                    v___x_663_,
                    v___y_666_,
                    v___y_667_,
                    v___y_668_,
                    v___y_669_,
                );
                if crate::leanh::lean_obj_tag(v___x_671_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_671_, 1);
                    crate::leanh::lean_inc(v_mvarId_662_);
                    v___x_672_ = l_Lean_MVarId_getType(
                        v_mvarId_662_,
                        v___y_666_,
                        v___y_667_,
                        v___y_668_,
                        v___y_669_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_672_) == 0 {
                        v_a_673_ = crate::leanh::lean_ctor_get(v___x_672_, 0);
                        crate::leanh::lean_inc(v_a_673_);
                        crate::leanh::lean_dec_ref_known(v___x_672_, 1);
                        crate::leanh::lean_inc(v_mvarId_662_);
                        v___x_674_ = l_Lean_MVarId_getTag(
                            v_mvarId_662_,
                            v___y_666_,
                            v___y_667_,
                            v___y_668_,
                            v___y_669_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_674_) == 0 {
                            v_a_675_ = crate::leanh::lean_ctor_get(v___x_674_, 0);
                            crate::leanh::lean_inc(v_a_675_);
                            crate::leanh::lean_dec_ref_known(v___x_674_, 1);
                            v_lctx_676_ = crate::leanh::lean_ctor_get(v___y_666_, 2);
                            v_localInstances_677_ = crate::leanh::lean_ctor_get(v___y_666_, 3);
                            crate::leanh::lean_inc_ref(v_localInstances_677_);
                            crate::leanh::lean_inc_ref(v_lctx_676_);
                            v___x_678_ = l_Lean_LocalContext_setUserName(
                                v_lctx_676_,
                                v_fvarId_664_,
                                v_userNameNew_665_,
                            );
                            v___x_679_ = 2;
                            v___x_680_ = crate::leanh::lean_unsigned_to_nat(0);
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
                            crate::leanh::lean_dec_ref(v___y_666_);
                            if crate::leanh::lean_obj_tag(v___x_681_) == 0 {
                                v_a_682_ = crate::leanh::lean_ctor_get(v___x_681_, 0);
                                crate::leanh::lean_inc_n(v_a_682_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_681_, 1);
                                v___x_683_ = l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0___redArg(v_mvarId_662_, v_a_682_, v___y_667_);
                                v_isSharedCheck_691_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_683_)) as u8;
                                if v_isSharedCheck_691_ == 0 {
                                    v_unused_692_ = crate::leanh::lean_ctor_get(v___x_683_, 0);
                                    crate::leanh::lean_dec(v_unused_692_);
                                    v___x_685_ = v___x_683_;
                                    v_isShared_686_ = v_isSharedCheck_691_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_683_);
                                    v___x_685_ = crate::leanh::lean_box(0);
                                    v_isShared_686_ = v_isSharedCheck_691_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_mvarId_662_);
                                v_a_693_ = crate::leanh::lean_ctor_get(v___x_681_, 0);
                                v_isSharedCheck_700_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_681_)) as u8;
                                if v_isSharedCheck_700_ == 0 {
                                    v___x_695_ = v___x_681_;
                                    v_isShared_696_ = v_isSharedCheck_700_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_693_);
                                    crate::leanh::lean_dec(v___x_681_);
                                    v___x_695_ = crate::leanh::lean_box(0);
                                    v_isShared_696_ = v_isSharedCheck_700_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_673_);
                            crate::leanh::lean_dec_ref(v___y_666_);
                            crate::leanh::lean_dec(v_userNameNew_665_);
                            crate::leanh::lean_dec(v_fvarId_664_);
                            crate::leanh::lean_dec(v_mvarId_662_);
                            v_a_701_ = crate::leanh::lean_ctor_get(v___x_674_, 0);
                            v_isSharedCheck_708_ =
                                (!crate::leanh::lean_is_exclusive(v___x_674_)) as u8;
                            if v_isSharedCheck_708_ == 0 {
                                v___x_703_ = v___x_674_;
                                v_isShared_704_ = v_isSharedCheck_708_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_701_);
                                crate::leanh::lean_dec(v___x_674_);
                                v___x_703_ = crate::leanh::lean_box(0);
                                v_isShared_704_ = v_isSharedCheck_708_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_666_);
                        crate::leanh::lean_dec(v_userNameNew_665_);
                        crate::leanh::lean_dec(v_fvarId_664_);
                        crate::leanh::lean_dec(v_mvarId_662_);
                        v_a_709_ = crate::leanh::lean_ctor_get(v___x_672_, 0);
                        v_isSharedCheck_716_ = (!crate::leanh::lean_is_exclusive(v___x_672_)) as u8;
                        if v_isSharedCheck_716_ == 0 {
                            v___x_711_ = v___x_672_;
                            v_isShared_712_ = v_isSharedCheck_716_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_709_);
                            crate::leanh::lean_dec(v___x_672_);
                            v___x_711_ = crate::leanh::lean_box(0);
                            v_isShared_712_ = v_isSharedCheck_716_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_666_);
                    crate::leanh::lean_dec(v_userNameNew_665_);
                    crate::leanh::lean_dec(v_fvarId_664_);
                    crate::leanh::lean_dec(v_mvarId_662_);
                    v_a_717_ = crate::leanh::lean_ctor_get(v___x_671_, 0);
                    v_isSharedCheck_724_ = (!crate::leanh::lean_is_exclusive(v___x_671_)) as u8;
                    if v_isSharedCheck_724_ == 0 {
                        v___x_719_ = v___x_671_;
                        v_isShared_720_ = v_isSharedCheck_724_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_717_);
                        crate::leanh::lean_dec(v___x_671_);
                        v___x_719_ = crate::leanh::lean_box(0);
                        v_isShared_720_ = v_isSharedCheck_724_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_687_ = l_Lean_Expr_mvarId_x21(v_a_682_);
                crate::leanh::lean_dec(v_a_682_);
                if v_isShared_686_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_685_, 0, v___x_687_);
                    v___x_689_ = v___x_685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_690_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
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
                    v_reuseFailAlloc_699_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
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
                    v_reuseFailAlloc_707_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
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
                    v_reuseFailAlloc_715_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
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
                    v_reuseFailAlloc_723_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
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
    mut v_mvarId_725_: *mut crate::leanh::LeanObject,
    mut v___x_726_: *mut crate::leanh::LeanObject,
    mut v_fvarId_727_: *mut crate::leanh::LeanObject,
    mut v_userNameNew_728_: *mut crate::leanh::LeanObject,
    mut v___y_729_: *mut crate::leanh::LeanObject,
    mut v___y_730_: *mut crate::leanh::LeanObject,
    mut v___y_731_: *mut crate::leanh::LeanObject,
    mut v___y_732_: *mut crate::leanh::LeanObject,
    mut v___y_733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_732_);
    crate::leanh::lean_dec_ref(v___y_731_);
    crate::leanh::lean_dec(v___y_730_);
    return v_res_734_;
}
pub unsafe fn l_Lean_MVarId_rename(
    mut v_mvarId_738_: *mut crate::leanh::LeanObject,
    mut v_fvarId_739_: *mut crate::leanh::LeanObject,
    mut v_userNameNew_740_: *mut crate::leanh::LeanObject,
    mut v_a_741_: *mut crate::leanh::LeanObject,
    mut v_a_742_: *mut crate::leanh::LeanObject,
    mut v_a_743_: *mut crate::leanh::LeanObject,
    mut v_a_744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_746_ = l_Lean_MVarId_rename___closed__1;
    crate::leanh::lean_inc(v_mvarId_738_);
    v___f_747_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_rename___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_747_, 0, v_mvarId_738_);
    crate::leanh::lean_closure_set(v___f_747_, 1, v___x_746_);
    crate::leanh::lean_closure_set(v___f_747_, 2, v_fvarId_739_);
    crate::leanh::lean_closure_set(v___f_747_, 3, v_userNameNew_740_);
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
    mut v_mvarId_749_: *mut crate::leanh::LeanObject,
    mut v_fvarId_750_: *mut crate::leanh::LeanObject,
    mut v_userNameNew_751_: *mut crate::leanh::LeanObject,
    mut v_a_752_: *mut crate::leanh::LeanObject,
    mut v_a_753_: *mut crate::leanh::LeanObject,
    mut v_a_754_: *mut crate::leanh::LeanObject,
    mut v_a_755_: *mut crate::leanh::LeanObject,
    mut v_a_756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_757_ = l_Lean_MVarId_rename(
        v_mvarId_749_,
        v_fvarId_750_,
        v_userNameNew_751_,
        v_a_752_,
        v_a_753_,
        v_a_754_,
        v_a_755_,
    );
    crate::leanh::lean_dec(v_a_755_);
    crate::leanh::lean_dec_ref(v_a_754_);
    crate::leanh::lean_dec(v_a_753_);
    crate::leanh::lean_dec_ref(v_a_752_);
    return v_res_757_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0(
    mut v_mvarId_758_: *mut crate::leanh::LeanObject,
    mut v_val_759_: *mut crate::leanh::LeanObject,
    mut v___y_760_: *mut crate::leanh::LeanObject,
    mut v___y_761_: *mut crate::leanh::LeanObject,
    mut v___y_762_: *mut crate::leanh::LeanObject,
    mut v___y_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0___redArg(
        v_mvarId_758_,
        v_val_759_,
        v___y_761_,
    );
    return v___x_765_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0___boxed(
    mut v_mvarId_766_: *mut crate::leanh::LeanObject,
    mut v_val_767_: *mut crate::leanh::LeanObject,
    mut v___y_768_: *mut crate::leanh::LeanObject,
    mut v___y_769_: *mut crate::leanh::LeanObject,
    mut v___y_770_: *mut crate::leanh::LeanObject,
    mut v___y_771_: *mut crate::leanh::LeanObject,
    mut v___y_772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_773_ = l_Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0(
        v_mvarId_766_,
        v_val_767_,
        v___y_768_,
        v___y_769_,
        v___y_770_,
        v___y_771_,
    );
    crate::leanh::lean_dec(v___y_771_);
    crate::leanh::lean_dec_ref(v___y_770_);
    crate::leanh::lean_dec(v___y_769_);
    crate::leanh::lean_dec_ref(v___y_768_);
    return v_res_773_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0(
    mut v_00_u03b2_774_: *mut crate::leanh::LeanObject,
    mut v_x_775_: *mut crate::leanh::LeanObject,
    mut v_x_776_: *mut crate::leanh::LeanObject,
    mut v_x_777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_778_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0___redArg(v_x_775_, v_x_776_, v_x_777_);
    return v___x_778_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2(
    mut v_00_u03b2_779_: *mut crate::leanh::LeanObject,
    mut v_x_780_: *mut crate::leanh::LeanObject,
    mut v_x_781_: usize,
    mut v_x_782_: usize,
    mut v_x_783_: *mut crate::leanh::LeanObject,
    mut v_x_784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_785_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___redArg(v_x_780_, v_x_781_, v_x_782_, v_x_783_, v_x_784_);
    return v___x_785_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_786_: *mut crate::leanh::LeanObject,
    mut v_x_787_: *mut crate::leanh::LeanObject,
    mut v_x_788_: *mut crate::leanh::LeanObject,
    mut v_x_789_: *mut crate::leanh::LeanObject,
    mut v_x_790_: *mut crate::leanh::LeanObject,
    mut v_x_791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1907__boxed_792_: usize = 0;
    let mut v_x_1908__boxed_793_: usize = 0;
    let mut v_res_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1907__boxed_792_ = crate::leanh::lean_unbox_usize(v_x_788_);
    crate::leanh::lean_dec(v_x_788_);
    v_x_1908__boxed_793_ = crate::leanh::lean_unbox_usize(v_x_789_);
    crate::leanh::lean_dec(v_x_789_);
    v_res_794_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2(v_00_u03b2_786_, v_x_787_, v_x_1907__boxed_792_, v_x_1908__boxed_793_, v_x_790_, v_x_791_);
    return v_res_794_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_795_: *mut crate::leanh::LeanObject,
    mut v_n_796_: *mut crate::leanh::LeanObject,
    mut v_k_797_: *mut crate::leanh::LeanObject,
    mut v_v_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_799_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__3___redArg(v_n_796_, v_k_797_, v_v_798_);
    return v___x_799_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_800_: *mut crate::leanh::LeanObject,
    mut v_depth_801_: usize,
    mut v_keys_802_: *mut crate::leanh::LeanObject,
    mut v_vals_803_: *mut crate::leanh::LeanObject,
    mut v_heq_804_: *mut crate::leanh::LeanObject,
    mut v_i_805_: *mut crate::leanh::LeanObject,
    mut v_entries_806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_807_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_801_, v_keys_802_, v_vals_803_, v_i_805_, v_entries_806_);
    return v___x_807_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_808_: *mut crate::leanh::LeanObject,
    mut v_depth_809_: *mut crate::leanh::LeanObject,
    mut v_keys_810_: *mut crate::leanh::LeanObject,
    mut v_vals_811_: *mut crate::leanh::LeanObject,
    mut v_heq_812_: *mut crate::leanh::LeanObject,
    mut v_i_813_: *mut crate::leanh::LeanObject,
    mut v_entries_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_815_: usize = 0;
    let mut v_res_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_815_ = crate::leanh::lean_unbox_usize(v_depth_809_);
    crate::leanh::lean_dec(v_depth_809_);
    v_res_816_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_808_, v_depth_boxed_815_, v_keys_810_, v_vals_811_, v_heq_812_, v_i_813_, v_entries_814_);
    crate::leanh::lean_dec_ref(v_vals_811_);
    crate::leanh::lean_dec_ref(v_keys_810_);
    return v_res_816_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_00_u03b2_817_: *mut crate::leanh::LeanObject,
    mut v_x_818_: *mut crate::leanh::LeanObject,
    mut v_x_819_: *mut crate::leanh::LeanObject,
    mut v_x_820_: *mut crate::leanh::LeanObject,
    mut v_x_821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_822_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_rename_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_818_, v_x_819_, v_x_820_, v_x_821_);
    return v___x_822_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Rename(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Rename(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Rename(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rename(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Rename(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Rename(builtin);
}
