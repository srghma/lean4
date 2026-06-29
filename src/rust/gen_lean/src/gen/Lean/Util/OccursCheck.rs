// Lean compiler output
// Module: Lean.Util.OccursCheck
// Imports: Lean.MetavarContext
use crate::ffi::lean_mk_array;
use crate::r#gen::Init::Control::Except::{
    l_ExceptT_bind, l_ExceptT_instMonad___redArg___lam__1, l_ExceptT_instMonad___redArg___lam__4,
    l_ExceptT_instMonad___redArg___lam__7, l_ExceptT_instMonad___redArg___lam__9, l_ExceptT_lift,
    l_ExceptT_lift___redArg___lam__0, l_ExceptT_map, l_ExceptT_pure,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_lift,
    l_StateT_map, l_StateT_pure,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_eqv___boxed, l_Lean_Expr_hasExprMVar, l_Lean_Expr_hash___boxed,
    l_Lean_instBEqMVarId_beq,
};
use crate::r#gen::Lean::MetavarContext::{
    initialize_Lean_MetavarContext, l_Lean_getDelayedMVarAssignment_x3f___redArg,
    l_Lean_getExprMVarAssignment_x3f___redArg, l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0,
    runtime_initialize_Lean_MetavarContext,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
};
pub static l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Expr_eqv___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Expr_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_ExceptT_lift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_occursCheck___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_occursCheck___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_occursCheck___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_occursCheck___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__7(
    mut v_toPure_407_: *mut crate::leanh::LeanObject,
    mut v_____x_408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_413_: u8 = 0;
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_419_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_409_ = crate::leanh::lean_ctor_get(v_____x_408_, 0);
                v_snd_410_ = crate::leanh::lean_ctor_get(v_____x_408_, 1);
                v_isSharedCheck_419_ = (!crate::leanh::lean_is_exclusive(v_____x_408_)) as u8;
                if v_isSharedCheck_419_ == 0 {
                    v___x_412_ = v_____x_408_;
                    v_isShared_413_ = v_isSharedCheck_419_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_410_);
                    crate::leanh::lean_inc(v_fst_409_);
                    crate::leanh::lean_dec(v_____x_408_);
                    v___x_412_ = crate::leanh::lean_box(0);
                    v_isShared_413_ = v_isSharedCheck_419_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_414_, 0, v_fst_409_);
                if v_isShared_413_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_412_, 0, v___x_414_);
                    v___x_416_ = v___x_412_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_418_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_418_, 1, v_snd_410_);
                    v___x_416_ = v_reuseFailAlloc_418_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_417_ = crate::leanh::lean_apply_2(
                    v_toPure_407_,
                    crate::leanh::lean_box(0),
                    v___x_416_,
                );
                return v___x_417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__5(
    mut v_toPure_420_: *mut crate::leanh::LeanObject,
    mut v_____x_421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_426_: u8 = 0;
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_432_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_422_ = crate::leanh::lean_ctor_get(v_____x_421_, 0);
                v_snd_423_ = crate::leanh::lean_ctor_get(v_____x_421_, 1);
                v_isSharedCheck_432_ = (!crate::leanh::lean_is_exclusive(v_____x_421_)) as u8;
                if v_isSharedCheck_432_ == 0 {
                    v___x_425_ = v_____x_421_;
                    v_isShared_426_ = v_isSharedCheck_432_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_423_);
                    crate::leanh::lean_inc(v_fst_422_);
                    crate::leanh::lean_dec(v_____x_421_);
                    v___x_425_ = crate::leanh::lean_box(0);
                    v_isShared_426_ = v_isSharedCheck_432_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_427_, 0, v_fst_422_);
                if v_isShared_426_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_425_, 0, v___x_427_);
                    v___x_429_ = v___x_425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_431_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_427_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_431_, 1, v_snd_423_);
                    v___x_429_ = v_reuseFailAlloc_431_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_430_ = crate::leanh::lean_apply_2(
                    v_toPure_420_,
                    crate::leanh::lean_box(0),
                    v___x_429_,
                );
                return v___x_430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6(
    mut v_toPure_437_: *mut crate::leanh::LeanObject,
    mut v_e_438_: *mut crate::leanh::LeanObject,
    mut v_toBind_439_: *mut crate::leanh::LeanObject,
    mut v___f_440_: *mut crate::leanh::LeanObject,
    mut v_____x_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_446_: u8 = 0;
    let mut v_a_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_450_: u8 = 0;
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_458_: u8 = 0;
    let mut v_isSharedCheck_459_: u8 = 0;
    let mut v_unused_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_464_: u8 = 0;
    let mut v_a_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: u8 = 0;
    let mut v___f_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_483_: u8 = 0;
    let mut v_unused_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_442_ = crate::leanh::lean_ctor_get(v_____x_441_, 0);
                crate::leanh::lean_inc(v_fst_442_);
                if crate::leanh::lean_obj_tag(v_fst_442_) == 0 {
                    crate::leanh::lean_dec(v___f_440_);
                    crate::leanh::lean_dec(v_toBind_439_);
                    crate::leanh::lean_dec_ref(v_e_438_);
                    v_snd_443_ = crate::leanh::lean_ctor_get(v_____x_441_, 1);
                    v_isSharedCheck_459_ = (!crate::leanh::lean_is_exclusive(v_____x_441_)) as u8;
                    if v_isSharedCheck_459_ == 0 {
                        v_unused_460_ = crate::leanh::lean_ctor_get(v_____x_441_, 0);
                        crate::leanh::lean_dec(v_unused_460_);
                        v___x_445_ = v_____x_441_;
                        v_isShared_446_ = v_isSharedCheck_459_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_443_);
                        crate::leanh::lean_dec(v_____x_441_);
                        v___x_445_ = crate::leanh::lean_box(0);
                        v_isShared_446_ = v_isSharedCheck_459_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_461_ = crate::leanh::lean_ctor_get(v_____x_441_, 1);
                    v_isSharedCheck_483_ = (!crate::leanh::lean_is_exclusive(v_____x_441_)) as u8;
                    if v_isSharedCheck_483_ == 0 {
                        v_unused_484_ = crate::leanh::lean_ctor_get(v_____x_441_, 0);
                        crate::leanh::lean_dec(v_unused_484_);
                        v___x_463_ = v_____x_441_;
                        v_isShared_464_ = v_isSharedCheck_483_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_461_);
                        crate::leanh::lean_dec(v_____x_441_);
                        v___x_463_ = crate::leanh::lean_box(0);
                        v_isShared_464_ = v_isSharedCheck_483_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_447_ = crate::leanh::lean_ctor_get(v_fst_442_, 0);
                v_isSharedCheck_458_ = (!crate::leanh::lean_is_exclusive(v_fst_442_)) as u8;
                if v_isSharedCheck_458_ == 0 {
                    v___x_449_ = v_fst_442_;
                    v_isShared_450_ = v_isSharedCheck_458_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_447_);
                    crate::leanh::lean_dec(v_fst_442_);
                    v___x_449_ = crate::leanh::lean_box(0);
                    v_isShared_450_ = v_isSharedCheck_458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_450_ == 0 {
                    v___x_452_ = v___x_449_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_457_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_447_);
                    v___x_452_ = v_reuseFailAlloc_457_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_446_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_445_, 0, v___x_452_);
                    v___x_454_ = v___x_445_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_456_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_456_, 1, v_snd_443_);
                    v___x_454_ = v_reuseFailAlloc_456_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_455_ = crate::leanh::lean_apply_2(
                    v_toPure_437_,
                    crate::leanh::lean_box(0),
                    v___x_454_,
                );
                return v___x_455_;
            }
            5 => {
                v_a_465_ = crate::leanh::lean_ctor_get(v_fst_442_, 0);
                crate::leanh::lean_inc(v_a_465_);
                crate::leanh::lean_dec_ref_known(v_fst_442_, 1);
                v___x_466_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0;
                v___x_467_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__1;
                crate::leanh::lean_inc_ref(v_e_438_);
                v___x_468_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
                    v___x_466_, v___x_467_, v_a_465_, v_e_438_,
                );
                crate::leanh::lean_dec(v_a_465_);
                if v___x_468_ == 0 {
                    crate::leanh::lean_inc(v_toPure_437_);
                    v___f_469_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__5 as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_469_, 0, v_toPure_437_);
                    v___x_470_ = crate::leanh::lean_box(0);
                    v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                        v___x_466_, v___x_467_, v_snd_461_, v_e_438_, v___x_470_,
                    );
                    if v_isShared_464_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_463_, 1, v___x_471_);
                        crate::leanh::lean_ctor_set(v___x_463_, 0, v___x_470_);
                        v___x_473_ = v___x_463_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_477_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_470_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_471_);
                        v___x_473_ = v_reuseFailAlloc_477_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___f_440_);
                    crate::leanh::lean_dec(v_toBind_439_);
                    crate::leanh::lean_dec_ref(v_e_438_);
                    v___x_478_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2;
                    if v_isShared_464_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_463_, 0, v___x_478_);
                        v___x_480_ = v___x_463_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_482_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_478_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_482_, 1, v_snd_461_);
                        v___x_480_ = v_reuseFailAlloc_482_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v___x_474_ = crate::leanh::lean_apply_2(
                    v_toPure_437_,
                    crate::leanh::lean_box(0),
                    v___x_473_,
                );
                crate::leanh::lean_inc(v_toBind_439_);
                v___x_475_ = crate::leanh::lean_apply_4(
                    v_toBind_439_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_474_,
                    v___f_469_,
                );
                v___x_476_ = crate::leanh::lean_apply_4(
                    v_toBind_439_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_475_,
                    v___f_440_,
                );
                return v___x_476_;
            }
            7 => {
                v___x_481_ = crate::leanh::lean_apply_2(
                    v_toPure_437_,
                    crate::leanh::lean_box(0),
                    v___x_480_,
                );
                return v___x_481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__1(
    mut v_toPure_485_: *mut crate::leanh::LeanObject,
    mut v_inst_486_: *mut crate::leanh::LeanObject,
    mut v_inst_487_: *mut crate::leanh::LeanObject,
    mut v_mvarId_488_: *mut crate::leanh::LeanObject,
    mut v_body_489_: *mut crate::leanh::LeanObject,
    mut v_____x_490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_491_ = crate::leanh::lean_ctor_get(v_____x_490_, 0);
    if crate::leanh::lean_obj_tag(v_fst_491_) == 0 {
        let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_body_489_);
        crate::leanh::lean_dec(v_mvarId_488_);
        crate::leanh::lean_dec_ref(v_inst_487_);
        crate::leanh::lean_dec_ref(v_inst_486_);
        v___x_492_ =
            crate::leanh::lean_apply_2(v_toPure_485_, crate::leanh::lean_box(0), v_____x_490_);
        return v___x_492_;
    } else {
        let mut v_snd_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_485_);
        v_snd_493_ = crate::leanh::lean_ctor_get(v_____x_490_, 1);
        crate::leanh::lean_inc(v_snd_493_);
        crate::leanh::lean_dec_ref(v_____x_490_);
        v___x_494_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(
            v_inst_486_,
            v_inst_487_,
            v_mvarId_488_,
            v_body_489_,
            v_snd_493_,
        );
        return v___x_494_;
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__2(
    mut v_toPure_495_: *mut crate::leanh::LeanObject,
    mut v_inst_496_: *mut crate::leanh::LeanObject,
    mut v_inst_497_: *mut crate::leanh::LeanObject,
    mut v_mvarId_498_: *mut crate::leanh::LeanObject,
    mut v_value_499_: *mut crate::leanh::LeanObject,
    mut v_toBind_500_: *mut crate::leanh::LeanObject,
    mut v___f_501_: *mut crate::leanh::LeanObject,
    mut v_____x_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_503_ = crate::leanh::lean_ctor_get(v_____x_502_, 0);
    if crate::leanh::lean_obj_tag(v_fst_503_) == 0 {
        let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_501_);
        crate::leanh::lean_dec(v_toBind_500_);
        crate::leanh::lean_dec_ref(v_value_499_);
        crate::leanh::lean_dec(v_mvarId_498_);
        crate::leanh::lean_dec_ref(v_inst_497_);
        crate::leanh::lean_dec_ref(v_inst_496_);
        v___x_504_ =
            crate::leanh::lean_apply_2(v_toPure_495_, crate::leanh::lean_box(0), v_____x_502_);
        return v___x_504_;
    } else {
        let mut v_snd_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_495_);
        v_snd_505_ = crate::leanh::lean_ctor_get(v_____x_502_, 1);
        crate::leanh::lean_inc(v_snd_505_);
        crate::leanh::lean_dec_ref(v_____x_502_);
        v___x_506_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(
            v_inst_496_,
            v_inst_497_,
            v_mvarId_498_,
            v_value_499_,
            v_snd_505_,
        );
        v___x_507_ = crate::leanh::lean_apply_4(
            v_toBind_500_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_506_,
            v___f_501_,
        );
        return v___x_507_;
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__3(
    mut v_toPure_508_: *mut crate::leanh::LeanObject,
    mut v_inst_509_: *mut crate::leanh::LeanObject,
    mut v_inst_510_: *mut crate::leanh::LeanObject,
    mut v_mvarId_511_: *mut crate::leanh::LeanObject,
    mut v_arg_512_: *mut crate::leanh::LeanObject,
    mut v_____x_513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_514_ = crate::leanh::lean_ctor_get(v_____x_513_, 0);
    if crate::leanh::lean_obj_tag(v_fst_514_) == 0 {
        let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_arg_512_);
        crate::leanh::lean_dec(v_mvarId_511_);
        crate::leanh::lean_dec_ref(v_inst_510_);
        crate::leanh::lean_dec_ref(v_inst_509_);
        v___x_515_ =
            crate::leanh::lean_apply_2(v_toPure_508_, crate::leanh::lean_box(0), v_____x_513_);
        return v___x_515_;
    } else {
        let mut v_snd_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_508_);
        v_snd_516_ = crate::leanh::lean_ctor_get(v_____x_513_, 1);
        crate::leanh::lean_inc(v_snd_516_);
        crate::leanh::lean_dec_ref(v_____x_513_);
        v___x_517_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(
            v_inst_509_,
            v_inst_510_,
            v_mvarId_511_,
            v_arg_512_,
            v_snd_516_,
        );
        return v___x_517_;
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__0(
    mut v_toApplicative_519_: *mut crate::leanh::LeanObject,
    mut v_inst_520_: *mut crate::leanh::LeanObject,
    mut v_inst_521_: *mut crate::leanh::LeanObject,
    mut v_mvarId_522_: *mut crate::leanh::LeanObject,
    mut v_____x_523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_528_: u8 = 0;
    let mut v_a_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_532_: u8 = 0;
    let mut v_toPure_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_541_: u8 = 0;
    let mut v_isSharedCheck_542_: u8 = 0;
    let mut v_unused_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_548_: u8 = 0;
    let mut v_toPure_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_555_: u8 = 0;
    let mut v_unused_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIdPending_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_524_ = crate::leanh::lean_ctor_get(v_____x_523_, 0);
                crate::leanh::lean_inc(v_fst_524_);
                if crate::leanh::lean_obj_tag(v_fst_524_) == 0 {
                    crate::leanh::lean_dec(v_mvarId_522_);
                    crate::leanh::lean_dec_ref(v_inst_521_);
                    crate::leanh::lean_dec_ref(v_inst_520_);
                    v_snd_525_ = crate::leanh::lean_ctor_get(v_____x_523_, 1);
                    v_isSharedCheck_542_ = (!crate::leanh::lean_is_exclusive(v_____x_523_)) as u8;
                    if v_isSharedCheck_542_ == 0 {
                        v_unused_543_ = crate::leanh::lean_ctor_get(v_____x_523_, 0);
                        crate::leanh::lean_dec(v_unused_543_);
                        v___x_527_ = v_____x_523_;
                        v_isShared_528_ = v_isSharedCheck_542_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_525_);
                        crate::leanh::lean_dec(v_____x_523_);
                        v___x_527_ = crate::leanh::lean_box(0);
                        v_isShared_528_ = v_isSharedCheck_542_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_544_ = crate::leanh::lean_ctor_get(v_fst_524_, 0);
                    crate::leanh::lean_inc(v_a_544_);
                    crate::leanh::lean_dec_ref_known(v_fst_524_, 1);
                    if crate::leanh::lean_obj_tag(v_a_544_) == 0 {
                        crate::leanh::lean_dec(v_mvarId_522_);
                        crate::leanh::lean_dec_ref(v_inst_521_);
                        crate::leanh::lean_dec_ref(v_inst_520_);
                        v_snd_545_ = crate::leanh::lean_ctor_get(v_____x_523_, 1);
                        v_isSharedCheck_555_ =
                            (!crate::leanh::lean_is_exclusive(v_____x_523_)) as u8;
                        if v_isSharedCheck_555_ == 0 {
                            v_unused_556_ = crate::leanh::lean_ctor_get(v_____x_523_, 0);
                            crate::leanh::lean_dec(v_unused_556_);
                            v___x_547_ = v_____x_523_;
                            v_isShared_548_ = v_isSharedCheck_555_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_545_);
                            crate::leanh::lean_dec(v_____x_523_);
                            v___x_547_ = crate::leanh::lean_box(0);
                            v_isShared_548_ = v_isSharedCheck_555_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_toApplicative_519_);
                        v_val_557_ = crate::leanh::lean_ctor_get(v_a_544_, 0);
                        crate::leanh::lean_inc(v_val_557_);
                        crate::leanh::lean_dec_ref_known(v_a_544_, 1);
                        v_snd_558_ = crate::leanh::lean_ctor_get(v_____x_523_, 1);
                        crate::leanh::lean_inc(v_snd_558_);
                        crate::leanh::lean_dec_ref(v_____x_523_);
                        v_mvarIdPending_559_ = crate::leanh::lean_ctor_get(v_val_557_, 1);
                        crate::leanh::lean_inc(v_mvarIdPending_559_);
                        crate::leanh::lean_dec(v_val_557_);
                        v___x_560_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(v_inst_520_, v_inst_521_, v_mvarId_522_, v_mvarIdPending_559_, v_snd_558_);
                        return v___x_560_;
                    }
                }
            }
            1 => {
                v_a_529_ = crate::leanh::lean_ctor_get(v_fst_524_, 0);
                v_isSharedCheck_541_ = (!crate::leanh::lean_is_exclusive(v_fst_524_)) as u8;
                if v_isSharedCheck_541_ == 0 {
                    v___x_531_ = v_fst_524_;
                    v_isShared_532_ = v_isSharedCheck_541_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_529_);
                    crate::leanh::lean_dec(v_fst_524_);
                    v___x_531_ = crate::leanh::lean_box(0);
                    v_isShared_532_ = v_isSharedCheck_541_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_toPure_533_ = crate::leanh::lean_ctor_get(v_toApplicative_519_, 1);
                crate::leanh::lean_inc(v_toPure_533_);
                crate::leanh::lean_dec_ref(v_toApplicative_519_);
                if v_isShared_532_ == 0 {
                    v___x_535_ = v___x_531_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_540_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_529_);
                    v___x_535_ = v_reuseFailAlloc_540_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_528_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_527_, 0, v___x_535_);
                    v___x_537_ = v___x_527_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_539_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_535_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_539_, 1, v_snd_525_);
                    v___x_537_ = v_reuseFailAlloc_539_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_538_ = crate::leanh::lean_apply_2(
                    v_toPure_533_,
                    crate::leanh::lean_box(0),
                    v___x_537_,
                );
                return v___x_538_;
            }
            5 => {
                v_toPure_549_ = crate::leanh::lean_ctor_get(v_toApplicative_519_, 1);
                crate::leanh::lean_inc(v_toPure_549_);
                crate::leanh::lean_dec_ref(v_toApplicative_519_);
                v___x_550_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2;
                if v_isShared_548_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_547_, 0, v___x_550_);
                    v___x_552_ = v___x_547_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_554_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_554_, 1, v_snd_545_);
                    v___x_552_ = v_reuseFailAlloc_554_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_553_ = crate::leanh::lean_apply_2(
                    v_toPure_549_,
                    crate::leanh::lean_box(0),
                    v___x_552_,
                );
                return v___x_553_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__1(
    mut v_toApplicative_561_: *mut crate::leanh::LeanObject,
    mut v___x_562_: *mut crate::leanh::LeanObject,
    mut v___x_563_: *mut crate::leanh::LeanObject,
    mut v_mvarId_x27_564_: *mut crate::leanh::LeanObject,
    mut v_toBind_565_: *mut crate::leanh::LeanObject,
    mut v___f_566_: *mut crate::leanh::LeanObject,
    mut v_inst_567_: *mut crate::leanh::LeanObject,
    mut v_inst_568_: *mut crate::leanh::LeanObject,
    mut v_mvarId_569_: *mut crate::leanh::LeanObject,
    mut v_____x_570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_575_: u8 = 0;
    let mut v_a_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_579_: u8 = 0;
    let mut v_toPure_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_588_: u8 = 0;
    let mut v_isSharedCheck_589_: u8 = 0;
    let mut v_unused_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693__overap_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_571_ = crate::leanh::lean_ctor_get(v_____x_570_, 0);
                crate::leanh::lean_inc(v_fst_571_);
                if crate::leanh::lean_obj_tag(v_fst_571_) == 0 {
                    crate::leanh::lean_dec(v_mvarId_569_);
                    crate::leanh::lean_dec_ref(v_inst_568_);
                    crate::leanh::lean_dec_ref(v_inst_567_);
                    crate::leanh::lean_dec(v___f_566_);
                    crate::leanh::lean_dec(v_toBind_565_);
                    crate::leanh::lean_dec(v_mvarId_x27_564_);
                    crate::leanh::lean_dec_ref(v___x_563_);
                    crate::leanh::lean_dec_ref(v___x_562_);
                    v_snd_572_ = crate::leanh::lean_ctor_get(v_____x_570_, 1);
                    v_isSharedCheck_589_ = (!crate::leanh::lean_is_exclusive(v_____x_570_)) as u8;
                    if v_isSharedCheck_589_ == 0 {
                        v_unused_590_ = crate::leanh::lean_ctor_get(v_____x_570_, 0);
                        crate::leanh::lean_dec(v_unused_590_);
                        v___x_574_ = v_____x_570_;
                        v_isShared_575_ = v_isSharedCheck_589_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_572_);
                        crate::leanh::lean_dec(v_____x_570_);
                        v___x_574_ = crate::leanh::lean_box(0);
                        v_isShared_575_ = v_isSharedCheck_589_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_toApplicative_561_);
                    v_a_591_ = crate::leanh::lean_ctor_get(v_fst_571_, 0);
                    crate::leanh::lean_inc(v_a_591_);
                    crate::leanh::lean_dec_ref_known(v_fst_571_, 1);
                    if crate::leanh::lean_obj_tag(v_a_591_) == 0 {
                        crate::leanh::lean_dec(v_mvarId_569_);
                        crate::leanh::lean_dec_ref(v_inst_568_);
                        crate::leanh::lean_dec_ref(v_inst_567_);
                        v_snd_592_ = crate::leanh::lean_ctor_get(v_____x_570_, 1);
                        crate::leanh::lean_inc(v_snd_592_);
                        crate::leanh::lean_dec_ref(v_____x_570_);
                        v___x_5693__overap_593_ = l_Lean_getDelayedMVarAssignment_x3f___redArg(
                            v___x_562_,
                            v___x_563_,
                            v_mvarId_x27_564_,
                        );
                        v___x_594_ =
                            crate::leanh::lean_apply_1(v___x_5693__overap_593_, v_snd_592_);
                        v___x_595_ = crate::leanh::lean_apply_4(
                            v_toBind_565_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_594_,
                            v___f_566_,
                        );
                        return v___x_595_;
                    } else {
                        crate::leanh::lean_dec(v___f_566_);
                        crate::leanh::lean_dec(v_toBind_565_);
                        crate::leanh::lean_dec(v_mvarId_x27_564_);
                        crate::leanh::lean_dec_ref(v___x_563_);
                        crate::leanh::lean_dec_ref(v___x_562_);
                        v_snd_596_ = crate::leanh::lean_ctor_get(v_____x_570_, 1);
                        crate::leanh::lean_inc(v_snd_596_);
                        crate::leanh::lean_dec_ref(v_____x_570_);
                        v_val_597_ = crate::leanh::lean_ctor_get(v_a_591_, 0);
                        crate::leanh::lean_inc(v_val_597_);
                        crate::leanh::lean_dec_ref_known(v_a_591_, 1);
                        v___x_598_ =
                            l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(
                                v_inst_567_,
                                v_inst_568_,
                                v_mvarId_569_,
                                v_val_597_,
                                v_snd_596_,
                            );
                        return v___x_598_;
                    }
                }
            }
            1 => {
                v_a_576_ = crate::leanh::lean_ctor_get(v_fst_571_, 0);
                v_isSharedCheck_588_ = (!crate::leanh::lean_is_exclusive(v_fst_571_)) as u8;
                if v_isSharedCheck_588_ == 0 {
                    v___x_578_ = v_fst_571_;
                    v_isShared_579_ = v_isSharedCheck_588_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_576_);
                    crate::leanh::lean_dec(v_fst_571_);
                    v___x_578_ = crate::leanh::lean_box(0);
                    v_isShared_579_ = v_isSharedCheck_588_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_toPure_580_ = crate::leanh::lean_ctor_get(v_toApplicative_561_, 1);
                crate::leanh::lean_inc(v_toPure_580_);
                crate::leanh::lean_dec_ref(v_toApplicative_561_);
                if v_isShared_579_ == 0 {
                    v___x_582_ = v___x_578_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_587_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_576_);
                    v___x_582_ = v_reuseFailAlloc_587_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_575_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_574_, 0, v___x_582_);
                    v___x_584_ = v___x_574_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_582_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_586_, 1, v_snd_572_);
                    v___x_584_ = v_reuseFailAlloc_586_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_585_ = crate::leanh::lean_apply_2(
                    v_toPure_580_,
                    crate::leanh::lean_box(0),
                    v___x_584_,
                );
                return v___x_585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(
    mut v_inst_601_: *mut crate::leanh::LeanObject,
    mut v_inst_602_: *mut crate::leanh::LeanObject,
    mut v_mvarId_603_: *mut crate::leanh::LeanObject,
    mut v_mvarId_x27_604_: *mut crate::leanh::LeanObject,
    mut v_a_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_606_: u8 = 0;
    let mut v___f_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getMCtx_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyMCtx_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342__overap_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_647_: u8 = 0;
    let mut v_toPure_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_654_: u8 = 0;
    let mut v_unused_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_606_ = l_Lean_instBEqMVarId_beq(v_mvarId_603_, v_mvarId_x27_604_);
                if v___x_606_ == 0 {
                    crate::leanh::lean_inc_ref_n(v_inst_601_, 11);
                    v___f_607_ = crate::leanh::lean_alloc_closure(
                        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_607_, 0, v_inst_601_);
                    v___f_608_ = crate::leanh::lean_alloc_closure(
                        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_608_, 0, v_inst_601_);
                    v___f_609_ = crate::leanh::lean_alloc_closure(
                        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_609_, 0, v_inst_601_);
                    v___f_610_ = crate::leanh::lean_alloc_closure(
                        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_610_, 0, v_inst_601_);
                    v___x_611_ = crate::leanh::lean_alloc_closure(
                        l_StateT_map as *mut core::ffi::c_void,
                        8,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_611_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_611_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_611_, 2, v_inst_601_);
                    v___x_612_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_612_, 0, v___x_611_);
                    crate::leanh::lean_ctor_set(v___x_612_, 1, v___f_607_);
                    v___x_613_ = crate::leanh::lean_alloc_closure(
                        l_StateT_pure as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_613_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_613_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_613_, 2, v_inst_601_);
                    v___x_614_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_614_, 0, v___x_612_);
                    crate::leanh::lean_ctor_set(v___x_614_, 1, v___x_613_);
                    crate::leanh::lean_ctor_set(v___x_614_, 2, v___f_608_);
                    crate::leanh::lean_ctor_set(v___x_614_, 3, v___f_609_);
                    crate::leanh::lean_ctor_set(v___x_614_, 4, v___f_610_);
                    v___x_615_ = crate::leanh::lean_alloc_closure(
                        l_StateT_bind as *mut core::ffi::c_void,
                        8,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_615_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_615_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_615_, 2, v_inst_601_);
                    v___x_616_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_616_, 0, v___x_614_);
                    crate::leanh::lean_ctor_set(v___x_616_, 1, v___x_615_);
                    crate::leanh::lean_inc_ref_n(v___x_616_, 7);
                    v___f_617_ = crate::leanh::lean_alloc_closure(
                        l_ExceptT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_617_, 0, v___x_616_);
                    v___f_618_ = crate::leanh::lean_alloc_closure(
                        l_ExceptT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_618_, 0, v___x_616_);
                    v___f_619_ = crate::leanh::lean_alloc_closure(
                        l_ExceptT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_619_, 0, v___x_616_);
                    v___f_620_ = crate::leanh::lean_alloc_closure(
                        l_ExceptT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_620_, 0, v___x_616_);
                    v___x_621_ = crate::leanh::lean_alloc_closure(
                        l_ExceptT_map as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_621_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_621_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_621_, 2, v___x_616_);
                    v___x_622_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_622_, 0, v___x_621_);
                    crate::leanh::lean_ctor_set(v___x_622_, 1, v___f_617_);
                    v___x_623_ = crate::leanh::lean_alloc_closure(
                        l_ExceptT_pure as *mut core::ffi::c_void,
                        5,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_623_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_623_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_623_, 2, v___x_616_);
                    v___x_624_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_624_, 0, v___x_622_);
                    crate::leanh::lean_ctor_set(v___x_624_, 1, v___x_623_);
                    crate::leanh::lean_ctor_set(v___x_624_, 2, v___f_618_);
                    crate::leanh::lean_ctor_set(v___x_624_, 3, v___f_619_);
                    crate::leanh::lean_ctor_set(v___x_624_, 4, v___f_620_);
                    v___x_625_ = crate::leanh::lean_alloc_closure(
                        l_ExceptT_bind as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_625_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_625_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_625_, 2, v___x_616_);
                    v___x_626_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_626_, 0, v___x_624_);
                    crate::leanh::lean_ctor_set(v___x_626_, 1, v___x_625_);
                    v_getMCtx_627_ = crate::leanh::lean_ctor_get(v_inst_602_, 0);
                    v_modifyMCtx_628_ = crate::leanh::lean_ctor_get(v_inst_602_, 1);
                    v___x_629_ = crate::leanh::lean_alloc_closure(
                        l_ExceptT_lift as *mut core::ffi::c_void,
                        5,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_629_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_629_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_629_, 2, v___x_616_);
                    v___x_630_ = crate::leanh::lean_alloc_closure(
                        l_StateT_lift as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_630_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_630_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_630_, 2, v_inst_601_);
                    crate::leanh::lean_inc(v_modifyMCtx_628_);
                    v___f_631_ = crate::leanh::lean_alloc_closure(
                        l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_631_, 0, v_modifyMCtx_628_);
                    crate::leanh::lean_closure_set(v___f_631_, 1, v___x_630_);
                    crate::leanh::lean_inc(v_getMCtx_627_);
                    v___x_632_ = crate::leanh::lean_alloc_closure(
                        l_StateT_lift as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    crate::leanh::lean_closure_set(v___x_632_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_632_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_632_, 2, v_inst_601_);
                    crate::leanh::lean_closure_set(v___x_632_, 3, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_632_, 4, v_getMCtx_627_);
                    v___f_633_ = crate::leanh::lean_alloc_closure(
                        l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_633_, 0, v___f_631_);
                    crate::leanh::lean_closure_set(v___f_633_, 1, v___x_629_);
                    v___f_634_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__0;
                    v___x_635_ = crate::leanh::lean_alloc_closure(
                        l_StateT_map as *mut core::ffi::c_void,
                        8,
                        7,
                    );
                    crate::leanh::lean_closure_set(v___x_635_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_635_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_635_, 2, v_inst_601_);
                    crate::leanh::lean_closure_set(v___x_635_, 3, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_635_, 4, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_635_, 5, v___f_634_);
                    crate::leanh::lean_closure_set(v___x_635_, 6, v___x_632_);
                    v___x_636_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_636_, 0, v___x_635_);
                    crate::leanh::lean_ctor_set(v___x_636_, 1, v___f_633_);
                    v_toApplicative_637_ = crate::leanh::lean_ctor_get(v_inst_601_, 0);
                    crate::leanh::lean_inc_ref_n(v_toApplicative_637_, 2);
                    v_toBind_638_ = crate::leanh::lean_ctor_get(v_inst_601_, 1);
                    crate::leanh::lean_inc_n(v_toBind_638_, 2);
                    crate::leanh::lean_inc(v_mvarId_603_);
                    crate::leanh::lean_inc_ref(v_inst_602_);
                    v___f_639_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__0 as *mut core::ffi::c_void, 5, 4);
                    crate::leanh::lean_closure_set(v___f_639_, 0, v_toApplicative_637_);
                    crate::leanh::lean_closure_set(v___f_639_, 1, v_inst_601_);
                    crate::leanh::lean_closure_set(v___f_639_, 2, v_inst_602_);
                    crate::leanh::lean_closure_set(v___f_639_, 3, v_mvarId_603_);
                    crate::leanh::lean_inc(v_mvarId_x27_604_);
                    crate::leanh::lean_inc_ref(v___x_636_);
                    crate::leanh::lean_inc_ref(v___x_626_);
                    v___f_640_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__1 as *mut core::ffi::c_void, 10, 9);
                    crate::leanh::lean_closure_set(v___f_640_, 0, v_toApplicative_637_);
                    crate::leanh::lean_closure_set(v___f_640_, 1, v___x_626_);
                    crate::leanh::lean_closure_set(v___f_640_, 2, v___x_636_);
                    crate::leanh::lean_closure_set(v___f_640_, 3, v_mvarId_x27_604_);
                    crate::leanh::lean_closure_set(v___f_640_, 4, v_toBind_638_);
                    crate::leanh::lean_closure_set(v___f_640_, 5, v___f_639_);
                    crate::leanh::lean_closure_set(v___f_640_, 6, v_inst_601_);
                    crate::leanh::lean_closure_set(v___f_640_, 7, v_inst_602_);
                    crate::leanh::lean_closure_set(v___f_640_, 8, v_mvarId_603_);
                    v___x_1342__overap_641_ = l_Lean_getExprMVarAssignment_x3f___redArg(
                        v___x_626_,
                        v___x_636_,
                        v_mvarId_x27_604_,
                    );
                    v___x_642_ = crate::leanh::lean_apply_1(v___x_1342__overap_641_, v_a_605_);
                    v___x_643_ = crate::leanh::lean_apply_4(
                        v_toBind_638_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_642_,
                        v___f_640_,
                    );
                    return v___x_643_;
                } else {
                    crate::leanh::lean_dec(v_mvarId_x27_604_);
                    crate::leanh::lean_dec(v_mvarId_603_);
                    crate::leanh::lean_dec_ref(v_inst_602_);
                    v_toApplicative_644_ = crate::leanh::lean_ctor_get(v_inst_601_, 0);
                    v_isSharedCheck_654_ = (!crate::leanh::lean_is_exclusive(v_inst_601_)) as u8;
                    if v_isSharedCheck_654_ == 0 {
                        v_unused_655_ = crate::leanh::lean_ctor_get(v_inst_601_, 1);
                        crate::leanh::lean_dec(v_unused_655_);
                        v___x_646_ = v_inst_601_;
                        v_isShared_647_ = v_isSharedCheck_654_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_toApplicative_644_);
                        crate::leanh::lean_dec(v_inst_601_);
                        v___x_646_ = crate::leanh::lean_box(0);
                        v_isShared_647_ = v_isSharedCheck_654_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_toPure_648_ = crate::leanh::lean_ctor_get(v_toApplicative_644_, 1);
                crate::leanh::lean_inc(v_toPure_648_);
                crate::leanh::lean_dec_ref(v_toApplicative_644_);
                v___x_649_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__1;
                if v_isShared_647_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_646_, 1, v_a_605_);
                    crate::leanh::lean_ctor_set(v___x_646_, 0, v___x_649_);
                    v___x_651_ = v___x_646_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_653_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 1, v_a_605_);
                    v___x_651_ = v_reuseFailAlloc_653_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_652_ = crate::leanh::lean_apply_2(
                    v_toPure_648_,
                    crate::leanh::lean_box(0),
                    v___x_651_,
                );
                return v___x_652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__4(
    mut v_toPure_656_: *mut crate::leanh::LeanObject,
    mut v_inst_657_: *mut crate::leanh::LeanObject,
    mut v_inst_658_: *mut crate::leanh::LeanObject,
    mut v_mvarId_659_: *mut crate::leanh::LeanObject,
    mut v_toBind_660_: *mut crate::leanh::LeanObject,
    mut v_e_661_: *mut crate::leanh::LeanObject,
    mut v_____x_662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_704_: u8 = 0;
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_710_: u8 = 0;
    let mut v_unused_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_670_ = crate::leanh::lean_ctor_get(v_____x_662_, 0);
                if crate::leanh::lean_obj_tag(v_fst_670_) == 0 {
                    crate::leanh::lean_dec_ref(v_e_661_);
                    crate::leanh::lean_dec(v_toBind_660_);
                    crate::leanh::lean_dec(v_mvarId_659_);
                    crate::leanh::lean_dec_ref(v_inst_658_);
                    crate::leanh::lean_dec_ref(v_inst_657_);
                    v___x_671_ = crate::leanh::lean_apply_2(
                        v_toPure_656_,
                        crate::leanh::lean_box(0),
                        v_____x_662_,
                    );
                    return v___x_671_;
                } else {
                    match crate::leanh::lean_obj_tag(v_e_661_) {
                        11 => {
                            crate::leanh::lean_dec(v_toBind_660_);
                            crate::leanh::lean_dec(v_toPure_656_);
                            v_snd_672_ = crate::leanh::lean_ctor_get(v_____x_662_, 1);
                            crate::leanh::lean_inc(v_snd_672_);
                            crate::leanh::lean_dec_ref(v_____x_662_);
                            v_struct_673_ = crate::leanh::lean_ctor_get(v_e_661_, 2);
                            crate::leanh::lean_inc_ref(v_struct_673_);
                            crate::leanh::lean_dec_ref_known(v_e_661_, 3);
                            v___x_674_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_657_, v_inst_658_, v_mvarId_659_, v_struct_673_, v_snd_672_);
                            return v___x_674_;
                        }
                        7 => {
                            v_snd_675_ = crate::leanh::lean_ctor_get(v_____x_662_, 1);
                            crate::leanh::lean_inc(v_snd_675_);
                            crate::leanh::lean_dec_ref(v_____x_662_);
                            v_binderType_676_ = crate::leanh::lean_ctor_get(v_e_661_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_676_);
                            v_body_677_ = crate::leanh::lean_ctor_get(v_e_661_, 2);
                            crate::leanh::lean_inc_ref(v_body_677_);
                            crate::leanh::lean_dec_ref_known(v_e_661_, 3);
                            v_d_664_ = v_binderType_676_;
                            v_b_665_ = v_body_677_;
                            v___y_666_ = v_snd_675_;
                            state = 1;
                            continue;
                        }
                        6 => {
                            v_snd_678_ = crate::leanh::lean_ctor_get(v_____x_662_, 1);
                            crate::leanh::lean_inc(v_snd_678_);
                            crate::leanh::lean_dec_ref(v_____x_662_);
                            v_binderType_679_ = crate::leanh::lean_ctor_get(v_e_661_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_679_);
                            v_body_680_ = crate::leanh::lean_ctor_get(v_e_661_, 2);
                            crate::leanh::lean_inc_ref(v_body_680_);
                            crate::leanh::lean_dec_ref_known(v_e_661_, 3);
                            v_d_664_ = v_binderType_679_;
                            v_b_665_ = v_body_680_;
                            v___y_666_ = v_snd_678_;
                            state = 1;
                            continue;
                        }
                        8 => {
                            v_snd_681_ = crate::leanh::lean_ctor_get(v_____x_662_, 1);
                            crate::leanh::lean_inc(v_snd_681_);
                            crate::leanh::lean_dec_ref(v_____x_662_);
                            v_type_682_ = crate::leanh::lean_ctor_get(v_e_661_, 1);
                            crate::leanh::lean_inc_ref(v_type_682_);
                            v_value_683_ = crate::leanh::lean_ctor_get(v_e_661_, 2);
                            crate::leanh::lean_inc_ref(v_value_683_);
                            v_body_684_ = crate::leanh::lean_ctor_get(v_e_661_, 3);
                            crate::leanh::lean_inc_ref(v_body_684_);
                            crate::leanh::lean_dec_ref_known(v_e_661_, 4);
                            crate::leanh::lean_inc_n(v_mvarId_659_, 2);
                            crate::leanh::lean_inc_ref_n(v_inst_658_, 2);
                            crate::leanh::lean_inc_ref_n(v_inst_657_, 2);
                            crate::leanh::lean_inc(v_toPure_656_);
                            v___f_685_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__1 as *mut core::ffi::c_void, 6, 5);
                            crate::leanh::lean_closure_set(v___f_685_, 0, v_toPure_656_);
                            crate::leanh::lean_closure_set(v___f_685_, 1, v_inst_657_);
                            crate::leanh::lean_closure_set(v___f_685_, 2, v_inst_658_);
                            crate::leanh::lean_closure_set(v___f_685_, 3, v_mvarId_659_);
                            crate::leanh::lean_closure_set(v___f_685_, 4, v_body_684_);
                            crate::leanh::lean_inc(v_toBind_660_);
                            v___f_686_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__2 as *mut core::ffi::c_void, 8, 7);
                            crate::leanh::lean_closure_set(v___f_686_, 0, v_toPure_656_);
                            crate::leanh::lean_closure_set(v___f_686_, 1, v_inst_657_);
                            crate::leanh::lean_closure_set(v___f_686_, 2, v_inst_658_);
                            crate::leanh::lean_closure_set(v___f_686_, 3, v_mvarId_659_);
                            crate::leanh::lean_closure_set(v___f_686_, 4, v_value_683_);
                            crate::leanh::lean_closure_set(v___f_686_, 5, v_toBind_660_);
                            crate::leanh::lean_closure_set(v___f_686_, 6, v___f_685_);
                            v___x_687_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_657_, v_inst_658_, v_mvarId_659_, v_type_682_, v_snd_681_);
                            v___x_688_ = crate::leanh::lean_apply_4(
                                v_toBind_660_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_687_,
                                v___f_686_,
                            );
                            return v___x_688_;
                        }
                        10 => {
                            crate::leanh::lean_dec(v_toBind_660_);
                            crate::leanh::lean_dec(v_toPure_656_);
                            v_snd_689_ = crate::leanh::lean_ctor_get(v_____x_662_, 1);
                            crate::leanh::lean_inc(v_snd_689_);
                            crate::leanh::lean_dec_ref(v_____x_662_);
                            v_expr_690_ = crate::leanh::lean_ctor_get(v_e_661_, 1);
                            crate::leanh::lean_inc_ref(v_expr_690_);
                            crate::leanh::lean_dec_ref_known(v_e_661_, 2);
                            v___x_691_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_657_, v_inst_658_, v_mvarId_659_, v_expr_690_, v_snd_689_);
                            return v___x_691_;
                        }
                        5 => {
                            v_snd_692_ = crate::leanh::lean_ctor_get(v_____x_662_, 1);
                            crate::leanh::lean_inc(v_snd_692_);
                            crate::leanh::lean_dec_ref(v_____x_662_);
                            v_fn_693_ = crate::leanh::lean_ctor_get(v_e_661_, 0);
                            crate::leanh::lean_inc_ref(v_fn_693_);
                            v_arg_694_ = crate::leanh::lean_ctor_get(v_e_661_, 1);
                            crate::leanh::lean_inc_ref(v_arg_694_);
                            crate::leanh::lean_dec_ref_known(v_e_661_, 2);
                            crate::leanh::lean_inc(v_mvarId_659_);
                            crate::leanh::lean_inc_ref(v_inst_658_);
                            crate::leanh::lean_inc_ref(v_inst_657_);
                            v___f_695_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__3 as *mut core::ffi::c_void, 6, 5);
                            crate::leanh::lean_closure_set(v___f_695_, 0, v_toPure_656_);
                            crate::leanh::lean_closure_set(v___f_695_, 1, v_inst_657_);
                            crate::leanh::lean_closure_set(v___f_695_, 2, v_inst_658_);
                            crate::leanh::lean_closure_set(v___f_695_, 3, v_mvarId_659_);
                            crate::leanh::lean_closure_set(v___f_695_, 4, v_arg_694_);
                            v___x_696_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_657_, v_inst_658_, v_mvarId_659_, v_fn_693_, v_snd_692_);
                            v___x_697_ = crate::leanh::lean_apply_4(
                                v_toBind_660_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_696_,
                                v___f_695_,
                            );
                            return v___x_697_;
                        }
                        2 => {
                            crate::leanh::lean_dec(v_toBind_660_);
                            crate::leanh::lean_dec(v_toPure_656_);
                            v_snd_698_ = crate::leanh::lean_ctor_get(v_____x_662_, 1);
                            crate::leanh::lean_inc(v_snd_698_);
                            crate::leanh::lean_dec_ref(v_____x_662_);
                            v_mvarId_699_ = crate::leanh::lean_ctor_get(v_e_661_, 0);
                            crate::leanh::lean_inc(v_mvarId_699_);
                            crate::leanh::lean_dec_ref_known(v_e_661_, 1);
                            v___x_700_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(v_inst_657_, v_inst_658_, v_mvarId_659_, v_mvarId_699_, v_snd_698_);
                            return v___x_700_;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_e_661_);
                            crate::leanh::lean_dec(v_toBind_660_);
                            crate::leanh::lean_dec(v_mvarId_659_);
                            crate::leanh::lean_dec_ref(v_inst_658_);
                            crate::leanh::lean_dec_ref(v_inst_657_);
                            v_snd_701_ = crate::leanh::lean_ctor_get(v_____x_662_, 1);
                            v_isSharedCheck_710_ =
                                (!crate::leanh::lean_is_exclusive(v_____x_662_)) as u8;
                            if v_isSharedCheck_710_ == 0 {
                                v_unused_711_ = crate::leanh::lean_ctor_get(v_____x_662_, 0);
                                crate::leanh::lean_dec(v_unused_711_);
                                v___x_703_ = v_____x_662_;
                                v_isShared_704_ = v_isSharedCheck_710_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_701_);
                                crate::leanh::lean_dec(v_____x_662_);
                                v___x_703_ = crate::leanh::lean_box(0);
                                v_isShared_704_ = v_isSharedCheck_710_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_mvarId_659_);
                crate::leanh::lean_inc_ref(v_inst_658_);
                crate::leanh::lean_inc_ref(v_inst_657_);
                v___f_667_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__0
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_667_, 0, v_toPure_656_);
                crate::leanh::lean_closure_set(v___f_667_, 1, v_inst_657_);
                crate::leanh::lean_closure_set(v___f_667_, 2, v_inst_658_);
                crate::leanh::lean_closure_set(v___f_667_, 3, v_mvarId_659_);
                crate::leanh::lean_closure_set(v___f_667_, 4, v_b_665_);
                v___x_668_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(
                    v_inst_657_,
                    v_inst_658_,
                    v_mvarId_659_,
                    v_d_664_,
                    v___y_666_,
                );
                v___x_669_ = crate::leanh::lean_apply_4(
                    v_toBind_660_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_668_,
                    v___f_667_,
                );
                return v___x_669_;
            }
            2 => {
                v___x_705_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2;
                if v_isShared_704_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_703_, 0, v___x_705_);
                    v___x_707_ = v___x_703_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_709_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_709_, 1, v_snd_701_);
                    v___x_707_ = v_reuseFailAlloc_709_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_708_ = crate::leanh::lean_apply_2(
                    v_toPure_656_,
                    crate::leanh::lean_box(0),
                    v___x_707_,
                );
                return v___x_708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(
    mut v_inst_712_: *mut crate::leanh::LeanObject,
    mut v_inst_713_: *mut crate::leanh::LeanObject,
    mut v_mvarId_714_: *mut crate::leanh::LeanObject,
    mut v_e_715_: *mut crate::leanh::LeanObject,
    mut v_a_716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_717_: u8 = 0;
    let mut v_toApplicative_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_721_: u8 = 0;
    let mut v_toPure_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_728_: u8 = 0;
    let mut v_unused_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_717_ = l_Lean_Expr_hasExprMVar(v_e_715_);
                if v___x_717_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_715_);
                    crate::leanh::lean_dec(v_mvarId_714_);
                    crate::leanh::lean_dec_ref(v_inst_713_);
                    v_toApplicative_718_ = crate::leanh::lean_ctor_get(v_inst_712_, 0);
                    v_isSharedCheck_728_ = (!crate::leanh::lean_is_exclusive(v_inst_712_)) as u8;
                    if v_isSharedCheck_728_ == 0 {
                        v_unused_729_ = crate::leanh::lean_ctor_get(v_inst_712_, 1);
                        crate::leanh::lean_dec(v_unused_729_);
                        v___x_720_ = v_inst_712_;
                        v_isShared_721_ = v_isSharedCheck_728_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_toApplicative_718_);
                        crate::leanh::lean_dec(v_inst_712_);
                        v___x_720_ = crate::leanh::lean_box(0);
                        v_isShared_721_ = v_isSharedCheck_728_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_toApplicative_730_ = crate::leanh::lean_ctor_get(v_inst_712_, 0);
                    v_toBind_731_ = crate::leanh::lean_ctor_get(v_inst_712_, 1);
                    crate::leanh::lean_inc_n(v_toBind_731_, 4);
                    v_toPure_732_ = crate::leanh::lean_ctor_get(v_toApplicative_730_, 1);
                    crate::leanh::lean_inc_n(v_toPure_732_, 4);
                    crate::leanh::lean_inc_ref(v_e_715_);
                    v___f_733_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__4 as *mut core::ffi::c_void, 7, 6);
                    crate::leanh::lean_closure_set(v___f_733_, 0, v_toPure_732_);
                    crate::leanh::lean_closure_set(v___f_733_, 1, v_inst_712_);
                    crate::leanh::lean_closure_set(v___f_733_, 2, v_inst_713_);
                    crate::leanh::lean_closure_set(v___f_733_, 3, v_mvarId_714_);
                    crate::leanh::lean_closure_set(v___f_733_, 4, v_toBind_731_);
                    crate::leanh::lean_closure_set(v___f_733_, 5, v_e_715_);
                    v___f_734_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6 as *mut core::ffi::c_void, 5, 4);
                    crate::leanh::lean_closure_set(v___f_734_, 0, v_toPure_732_);
                    crate::leanh::lean_closure_set(v___f_734_, 1, v_e_715_);
                    crate::leanh::lean_closure_set(v___f_734_, 2, v_toBind_731_);
                    crate::leanh::lean_closure_set(v___f_734_, 3, v___f_733_);
                    v___f_735_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__7 as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_735_, 0, v_toPure_732_);
                    crate::leanh::lean_inc_ref(v_a_716_);
                    v___x_736_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_736_, 0, v_a_716_);
                    crate::leanh::lean_ctor_set(v___x_736_, 1, v_a_716_);
                    v___x_737_ = crate::leanh::lean_apply_2(
                        v_toPure_732_,
                        crate::leanh::lean_box(0),
                        v___x_736_,
                    );
                    v___x_738_ = crate::leanh::lean_apply_4(
                        v_toBind_731_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_737_,
                        v___f_735_,
                    );
                    v___x_739_ = crate::leanh::lean_apply_4(
                        v_toBind_731_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_738_,
                        v___f_734_,
                    );
                    return v___x_739_;
                }
            }
            1 => {
                v_toPure_722_ = crate::leanh::lean_ctor_get(v_toApplicative_718_, 1);
                crate::leanh::lean_inc(v_toPure_722_);
                crate::leanh::lean_dec_ref(v_toApplicative_718_);
                v___x_723_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2;
                if v_isShared_721_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_720_, 1, v_a_716_);
                    crate::leanh::lean_ctor_set(v___x_720_, 0, v___x_723_);
                    v___x_725_ = v___x_720_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_727_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_723_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_727_, 1, v_a_716_);
                    v___x_725_ = v_reuseFailAlloc_727_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_726_ = crate::leanh::lean_apply_2(
                    v_toPure_722_,
                    crate::leanh::lean_box(0),
                    v___x_725_,
                );
                return v___x_726_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__0(
    mut v_toPure_740_: *mut crate::leanh::LeanObject,
    mut v_inst_741_: *mut crate::leanh::LeanObject,
    mut v_inst_742_: *mut crate::leanh::LeanObject,
    mut v_mvarId_743_: *mut crate::leanh::LeanObject,
    mut v_b_744_: *mut crate::leanh::LeanObject,
    mut v_____x_745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_746_ = crate::leanh::lean_ctor_get(v_____x_745_, 0);
    if crate::leanh::lean_obj_tag(v_fst_746_) == 0 {
        let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_b_744_);
        crate::leanh::lean_dec(v_mvarId_743_);
        crate::leanh::lean_dec_ref(v_inst_742_);
        crate::leanh::lean_dec_ref(v_inst_741_);
        v___x_747_ =
            crate::leanh::lean_apply_2(v_toPure_740_, crate::leanh::lean_box(0), v_____x_745_);
        return v___x_747_;
    } else {
        let mut v_snd_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_740_);
        v_snd_748_ = crate::leanh::lean_ctor_get(v_____x_745_, 1);
        crate::leanh::lean_inc(v_snd_748_);
        crate::leanh::lean_dec_ref(v_____x_745_);
        v___x_749_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(
            v_inst_741_,
            v_inst_742_,
            v_mvarId_743_,
            v_b_744_,
            v_snd_748_,
        );
        return v___x_749_;
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar(
    mut v_m_750_: *mut crate::leanh::LeanObject,
    mut v_inst_751_: *mut crate::leanh::LeanObject,
    mut v_inst_752_: *mut crate::leanh::LeanObject,
    mut v_mvarId_753_: *mut crate::leanh::LeanObject,
    mut v_mvarId_x27_754_: *mut crate::leanh::LeanObject,
    mut v_a_755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_756_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(
        v_inst_751_,
        v_inst_752_,
        v_mvarId_753_,
        v_mvarId_x27_754_,
        v_a_755_,
    );
    return v___x_756_;
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit(
    mut v_m_757_: *mut crate::leanh::LeanObject,
    mut v_inst_758_: *mut crate::leanh::LeanObject,
    mut v_inst_759_: *mut crate::leanh::LeanObject,
    mut v_mvarId_760_: *mut crate::leanh::LeanObject,
    mut v_e_761_: *mut crate::leanh::LeanObject,
    mut v_a_762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_763_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(
        v_inst_758_,
        v_inst_759_,
        v_mvarId_760_,
        v_e_761_,
        v_a_762_,
    );
    return v___x_763_;
}
pub unsafe fn l_Lean_occursCheck___redArg___lam__0(
    mut v_toApplicative_764_: *mut crate::leanh::LeanObject,
    mut v___x_765_: u8,
    mut v___x_766_: u8,
    mut v_____do__lift_767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_768_ = crate::leanh::lean_ctor_get(v_____do__lift_767_, 0);
    if crate::leanh::lean_obj_tag(v_fst_768_) == 0 {
        let mut v_toPure_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toPure_769_ = crate::leanh::lean_ctor_get(v_toApplicative_764_, 1);
        crate::leanh::lean_inc(v_toPure_769_);
        crate::leanh::lean_dec_ref(v_toApplicative_764_);
        v___x_770_ = crate::leanh::lean_box((v___x_765_) as usize);
        v___x_771_ =
            crate::leanh::lean_apply_2(v_toPure_769_, crate::leanh::lean_box(0), v___x_770_);
        return v___x_771_;
    } else {
        let mut v_toPure_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toPure_772_ = crate::leanh::lean_ctor_get(v_toApplicative_764_, 1);
        crate::leanh::lean_inc(v_toPure_772_);
        crate::leanh::lean_dec_ref(v_toApplicative_764_);
        v___x_773_ = crate::leanh::lean_box((v___x_766_) as usize);
        v___x_774_ =
            crate::leanh::lean_apply_2(v_toPure_772_, crate::leanh::lean_box(0), v___x_773_);
        return v___x_774_;
    }
}
pub unsafe fn l_Lean_occursCheck___redArg___lam__0___boxed(
    mut v_toApplicative_775_: *mut crate::leanh::LeanObject,
    mut v___x_776_: *mut crate::leanh::LeanObject,
    mut v___x_777_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_245__boxed_779_: u8 = 0;
    let mut v___x_246__boxed_780_: u8 = 0;
    let mut v_res_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_245__boxed_779_ = (crate::leanh::lean_unbox(v___x_776_) as u8);
    v___x_246__boxed_780_ = (crate::leanh::lean_unbox(v___x_777_) as u8);
    v_res_781_ = l_Lean_occursCheck___redArg___lam__0(
        v_toApplicative_775_,
        v___x_245__boxed_779_,
        v___x_246__boxed_780_,
        v_____do__lift_778_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_778_);
    return v_res_781_;
}
pub unsafe fn _init_l_Lean_occursCheck___redArg___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_782_ = crate::leanh::lean_box(0);
    v___x_783_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_784_ = lean_mk_array(v___x_783_, v___x_782_);
    return v___x_784_;
}
pub unsafe fn _init_l_Lean_occursCheck___redArg___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_785_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_occursCheck___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_occursCheck___redArg___closed__0_once),
        _init_l_Lean_occursCheck___redArg___closed__0,
    );
    v___x_786_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_787_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_787_, 0, v___x_786_);
    crate::leanh::lean_ctor_set(v___x_787_, 1, v___x_785_);
    return v___x_787_;
}
pub unsafe fn l_Lean_occursCheck___redArg(
    mut v_inst_788_: *mut crate::leanh::LeanObject,
    mut v_inst_789_: *mut crate::leanh::LeanObject,
    mut v_mvarId_790_: *mut crate::leanh::LeanObject,
    mut v_e_791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_792_: u8 = 0;
    v___x_792_ = l_Lean_Expr_hasExprMVar(v_e_791_);
    if v___x_792_ == 0 {
        let mut v_toApplicative_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_795_: u8 = 0;
        let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_791_);
        crate::leanh::lean_dec(v_mvarId_790_);
        crate::leanh::lean_dec_ref(v_inst_789_);
        v_toApplicative_793_ = crate::leanh::lean_ctor_get(v_inst_788_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_793_);
        crate::leanh::lean_dec_ref(v_inst_788_);
        v_toPure_794_ = crate::leanh::lean_ctor_get(v_toApplicative_793_, 1);
        crate::leanh::lean_inc(v_toPure_794_);
        crate::leanh::lean_dec_ref(v_toApplicative_793_);
        v___x_795_ = 1;
        v___x_796_ = crate::leanh::lean_box((v___x_795_) as usize);
        v___x_797_ =
            crate::leanh::lean_apply_2(v_toPure_794_, crate::leanh::lean_box(0), v___x_796_);
        return v___x_797_;
    } else {
        let mut v_toApplicative_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_800_: u8 = 0;
        let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_798_ = crate::leanh::lean_ctor_get(v_inst_788_, 0);
        v_toBind_799_ = crate::leanh::lean_ctor_get(v_inst_788_, 1);
        crate::leanh::lean_inc(v_toBind_799_);
        v___x_800_ = 0;
        v___x_801_ = crate::leanh::lean_box((v___x_800_) as usize);
        v___x_802_ = crate::leanh::lean_box((v___x_792_) as usize);
        crate::leanh::lean_inc_ref(v_toApplicative_798_);
        v___f_803_ = crate::leanh::lean_alloc_closure(
            l_Lean_occursCheck___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_803_, 0, v_toApplicative_798_);
        crate::leanh::lean_closure_set(v___f_803_, 1, v___x_801_);
        crate::leanh::lean_closure_set(v___f_803_, 2, v___x_802_);
        v___x_804_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_occursCheck___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Lean_occursCheck___redArg___closed__1_once),
            _init_l_Lean_occursCheck___redArg___closed__1,
        );
        v___x_805_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(
            v_inst_788_,
            v_inst_789_,
            v_mvarId_790_,
            v_e_791_,
            v___x_804_,
        );
        v___x_806_ = crate::leanh::lean_apply_4(
            v_toBind_799_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_805_,
            v___f_803_,
        );
        return v___x_806_;
    }
}
pub unsafe fn l_Lean_occursCheck(
    mut v_m_807_: *mut crate::leanh::LeanObject,
    mut v_inst_808_: *mut crate::leanh::LeanObject,
    mut v_inst_809_: *mut crate::leanh::LeanObject,
    mut v_mvarId_810_: *mut crate::leanh::LeanObject,
    mut v_e_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_812_ = l_Lean_occursCheck___redArg(v_inst_808_, v_inst_809_, v_mvarId_810_, v_e_811_);
    return v___x_812_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_OccursCheck(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_MetavarContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_OccursCheck(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_OccursCheck(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_MetavarContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_OccursCheck(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_OccursCheck(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_OccursCheck(builtin);
}
