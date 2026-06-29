// Lean compiler output
// Module: Lean.Meta.HasAssignableMVar
// Imports: Lean.Meta.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_uget_borrowed,
    lean_array_uset, lean_expr_eqv, lean_mk_array, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasMVar, l_Lean_Expr_hash};
use crate::r#gen::Lean::Level::l_Lean_Level_hasMVar;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_getDecl, l_Lean_MetavarContext_getLevelDecl,
};
pub static l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [104, 97, 115, 65, 115, 115, 105, 103, 110, 97, 98, 108, 101, 77, 86, 97, 114, 0]};
static mut l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_hasAssignableMVar___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_hasAssignableMVar___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_hasAssignableMVar___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_hasAssignableMVar___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(
    mut v_mvarId_463_: *mut crate::leanh::LeanObject,
    mut v___y_464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: u8 = 0;
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_466_ = lean_st_ref_get(v___y_464_);
    v_mctx_467_ = crate::leanh::lean_ctor_get(v___x_466_, 0);
    crate::leanh::lean_inc_ref(v_mctx_467_);
    crate::leanh::lean_dec(v___x_466_);
    v_levelAssignDepth_468_ = crate::leanh::lean_ctor_get(v_mctx_467_, 1);
    crate::leanh::lean_inc(v_levelAssignDepth_468_);
    v_decl_469_ = l_Lean_MetavarContext_getLevelDecl(v_mctx_467_, v_mvarId_463_);
    crate::leanh::lean_dec_ref(v_mctx_467_);
    v_depth_470_ = crate::leanh::lean_ctor_get(v_decl_469_, 0);
    crate::leanh::lean_inc(v_depth_470_);
    crate::leanh::lean_dec_ref(v_decl_469_);
    v___x_471_ = lean_nat_dec_le(v_levelAssignDepth_468_, v_depth_470_);
    crate::leanh::lean_dec(v_depth_470_);
    crate::leanh::lean_dec(v_levelAssignDepth_468_);
    v___x_472_ = crate::leanh::lean_box((v___x_471_) as usize);
    v___x_473_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_473_, 0, v___x_472_);
    return v___x_473_;
}
pub unsafe fn l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg___boxed(
    mut v_mvarId_474_: *mut crate::leanh::LeanObject,
    mut v___y_475_: *mut crate::leanh::LeanObject,
    mut v___y_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_477_ =
        l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(
            v_mvarId_474_,
            v___y_475_,
        );
    crate::leanh::lean_dec(v___y_475_);
    return v_res_477_;
}
pub unsafe fn l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0(
    mut v_mvarId_478_: *mut crate::leanh::LeanObject,
    mut v___y_479_: *mut crate::leanh::LeanObject,
    mut v___y_480_: *mut crate::leanh::LeanObject,
    mut v___y_481_: *mut crate::leanh::LeanObject,
    mut v___y_482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_484_ =
        l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(
            v_mvarId_478_,
            v___y_480_,
        );
    return v___x_484_;
}
pub unsafe fn l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___boxed(
    mut v_mvarId_485_: *mut crate::leanh::LeanObject,
    mut v___y_486_: *mut crate::leanh::LeanObject,
    mut v___y_487_: *mut crate::leanh::LeanObject,
    mut v___y_488_: *mut crate::leanh::LeanObject,
    mut v___y_489_: *mut crate::leanh::LeanObject,
    mut v___y_490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_491_ = l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0(
        v_mvarId_485_,
        v___y_486_,
        v___y_487_,
        v___y_488_,
        v___y_489_,
    );
    crate::leanh::lean_dec(v___y_489_);
    crate::leanh::lean_dec_ref(v___y_488_);
    crate::leanh::lean_dec(v___y_487_);
    crate::leanh::lean_dec_ref(v___y_486_);
    return v_res_491_;
}
pub unsafe fn l_Lean_Meta_hasAssignableLevelMVar(
    mut v_x_492_: *mut crate::leanh::LeanObject,
    mut v_a_493_: *mut crate::leanh::LeanObject,
    mut v_a_494_: *mut crate::leanh::LeanObject,
    mut v_a_495_: *mut crate::leanh::LeanObject,
    mut v_a_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_505_: u8 = 0;
    let mut v___x_506_: u8 = 0;
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lvl_u2081_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lvl_u2082_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: u8 = 0;
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: u8 = 0;
    let mut v_a_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: u8 = 0;
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: u8 = 0;
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_492_) {
                1 => {
                    v_a_523_ = crate::leanh::lean_ctor_get(v_x_492_, 0);
                    crate::leanh::lean_inc(v_a_523_);
                    crate::leanh::lean_dec_ref_known(v_x_492_, 1);
                    v___x_524_ = l_Lean_Level_hasMVar(v_a_523_);
                    if v___x_524_ == 0 {
                        crate::leanh::lean_dec(v_a_523_);
                        v___x_525_ = crate::leanh::lean_box((v___x_524_) as usize);
                        v___x_526_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_526_, 0, v___x_525_);
                        return v___x_526_;
                    } else {
                        v_x_492_ = v_a_523_;
                        state = 0;
                        continue;
                    }
                }
                2 => {
                    v_a_528_ = crate::leanh::lean_ctor_get(v_x_492_, 0);
                    crate::leanh::lean_inc(v_a_528_);
                    v_a_529_ = crate::leanh::lean_ctor_get(v_x_492_, 1);
                    crate::leanh::lean_inc(v_a_529_);
                    crate::leanh::lean_dec_ref_known(v_x_492_, 2);
                    v_lvl_u2081_511_ = v_a_528_;
                    v_lvl_u2082_512_ = v_a_529_;
                    v___y_513_ = v_a_493_;
                    v___y_514_ = v_a_494_;
                    v___y_515_ = v_a_495_;
                    v___y_516_ = v_a_496_;
                    state = 2;
                    continue;
                }
                3 => {
                    v_a_530_ = crate::leanh::lean_ctor_get(v_x_492_, 0);
                    crate::leanh::lean_inc(v_a_530_);
                    v_a_531_ = crate::leanh::lean_ctor_get(v_x_492_, 1);
                    crate::leanh::lean_inc(v_a_531_);
                    crate::leanh::lean_dec_ref_known(v_x_492_, 2);
                    v_lvl_u2081_511_ = v_a_530_;
                    v_lvl_u2082_512_ = v_a_531_;
                    v___y_513_ = v_a_493_;
                    v___y_514_ = v_a_494_;
                    v___y_515_ = v_a_495_;
                    v___y_516_ = v_a_496_;
                    state = 2;
                    continue;
                }
                5 => {
                    v_a_532_ = crate::leanh::lean_ctor_get(v_x_492_, 0);
                    crate::leanh::lean_inc(v_a_532_);
                    crate::leanh::lean_dec_ref_known(v_x_492_, 1);
                    v___x_533_ = l_Lean_isLevelMVarAssignable___at___00Lean_Meta_hasAssignableLevelMVar_spec__0___redArg(v_a_532_, v_a_494_);
                    return v___x_533_;
                }
                _ => {
                    crate::leanh::lean_dec(v_x_492_);
                    v___x_534_ = 0;
                    v___x_535_ = crate::leanh::lean_box((v___x_534_) as usize);
                    v___x_536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_536_, 0, v___x_535_);
                    return v___x_536_;
                }
            },
            1 => {
                if v_a_505_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_504_);
                    v___x_506_ = l_Lean_Level_hasMVar(v___y_501_);
                    if v___x_506_ == 0 {
                        crate::leanh::lean_dec(v___y_501_);
                        v___x_507_ = crate::leanh::lean_box((v___x_506_) as usize);
                        v___x_508_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_508_, 0, v___x_507_);
                        return v___x_508_;
                    } else {
                        v_x_492_ = v___y_501_;
                        v_a_493_ = v___y_500_;
                        v_a_494_ = v___y_503_;
                        v_a_495_ = v___y_499_;
                        v_a_496_ = v___y_502_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_501_);
                    return v___y_504_;
                }
            }
            2 => {
                v___x_517_ = l_Lean_Level_hasMVar(v_lvl_u2081_511_);
                if v___x_517_ == 0 {
                    crate::leanh::lean_dec(v_lvl_u2081_511_);
                    v___x_518_ = crate::leanh::lean_box((v___x_517_) as usize);
                    v___x_519_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_519_, 0, v___x_518_);
                    v___y_499_ = v___y_515_;
                    v___y_500_ = v___y_513_;
                    v___y_501_ = v_lvl_u2082_512_;
                    v___y_502_ = v___y_516_;
                    v___y_503_ = v___y_514_;
                    v___y_504_ = v___x_519_;
                    v_a_505_ = v___x_517_;
                    state = 1;
                    continue;
                } else {
                    v___x_520_ = l_Lean_Meta_hasAssignableLevelMVar(
                        v_lvl_u2081_511_,
                        v___y_513_,
                        v___y_514_,
                        v___y_515_,
                        v___y_516_,
                    );
                    v_a_521_ = crate::leanh::lean_ctor_get(v___x_520_, 0);
                    crate::leanh::lean_inc(v_a_521_);
                    v___x_522_ = (crate::leanh::lean_unbox(v_a_521_) as u8);
                    crate::leanh::lean_dec(v_a_521_);
                    v___y_499_ = v___y_515_;
                    v___y_500_ = v___y_513_;
                    v___y_501_ = v_lvl_u2082_512_;
                    v___y_502_ = v___y_516_;
                    v___y_503_ = v___y_514_;
                    v___y_504_ = v___x_520_;
                    v_a_505_ = v___x_522_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_hasAssignableLevelMVar___boxed(
    mut v_x_537_: *mut crate::leanh::LeanObject,
    mut v_a_538_: *mut crate::leanh::LeanObject,
    mut v_a_539_: *mut crate::leanh::LeanObject,
    mut v_a_540_: *mut crate::leanh::LeanObject,
    mut v_a_541_: *mut crate::leanh::LeanObject,
    mut v_a_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_543_ =
        l_Lean_Meta_hasAssignableLevelMVar(v_x_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
    crate::leanh::lean_dec(v_a_541_);
    crate::leanh::lean_dec_ref(v_a_540_);
    crate::leanh::lean_dec(v_a_539_);
    crate::leanh::lean_dec_ref(v_a_538_);
    return v_res_543_;
}
pub unsafe fn l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(
    mut v_mvarId_544_: *mut crate::leanh::LeanObject,
    mut v___y_545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: u8 = 0;
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_547_ = lean_st_ref_get(v___y_545_);
    v_mctx_548_ = crate::leanh::lean_ctor_get(v___x_547_, 0);
    crate::leanh::lean_inc_ref(v_mctx_548_);
    crate::leanh::lean_dec(v___x_547_);
    v_decl_549_ = l_Lean_MetavarContext_getDecl(v_mctx_548_, v_mvarId_544_);
    v_depth_550_ = crate::leanh::lean_ctor_get(v_decl_549_, 3);
    crate::leanh::lean_inc(v_depth_550_);
    crate::leanh::lean_dec_ref(v_decl_549_);
    v_depth_551_ = crate::leanh::lean_ctor_get(v_mctx_548_, 0);
    crate::leanh::lean_inc(v_depth_551_);
    crate::leanh::lean_dec_ref(v_mctx_548_);
    v___x_552_ = lean_nat_dec_eq(v_depth_550_, v_depth_551_);
    crate::leanh::lean_dec(v_depth_551_);
    crate::leanh::lean_dec(v_depth_550_);
    v___x_553_ = crate::leanh::lean_box((v___x_552_) as usize);
    v___x_554_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_554_, 0, v___x_553_);
    return v___x_554_;
}
pub unsafe fn l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg___boxed(
    mut v_mvarId_555_: *mut crate::leanh::LeanObject,
    mut v___y_556_: *mut crate::leanh::LeanObject,
    mut v___y_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_558_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(v_mvarId_555_, v___y_556_);
    crate::leanh::lean_dec(v___y_556_);
    return v_res_558_;
}
pub unsafe fn l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0(
    mut v_mvarId_559_: *mut crate::leanh::LeanObject,
    mut v___y_560_: *mut crate::leanh::LeanObject,
    mut v___y_561_: *mut crate::leanh::LeanObject,
    mut v___y_562_: *mut crate::leanh::LeanObject,
    mut v___y_563_: *mut crate::leanh::LeanObject,
    mut v___y_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(v_mvarId_559_, v___y_562_);
    return v___x_566_;
}
pub unsafe fn l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___boxed(
    mut v_mvarId_567_: *mut crate::leanh::LeanObject,
    mut v___y_568_: *mut crate::leanh::LeanObject,
    mut v___y_569_: *mut crate::leanh::LeanObject,
    mut v___y_570_: *mut crate::leanh::LeanObject,
    mut v___y_571_: *mut crate::leanh::LeanObject,
    mut v___y_572_: *mut crate::leanh::LeanObject,
    mut v___y_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_574_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0(v_mvarId_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
    crate::leanh::lean_dec(v___y_572_);
    crate::leanh::lean_dec_ref(v___y_571_);
    crate::leanh::lean_dec(v___y_570_);
    crate::leanh::lean_dec_ref(v___y_569_);
    crate::leanh::lean_dec(v___y_568_);
    return v_res_574_;
}
pub unsafe fn l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(
    mut v_x_575_: *mut crate::leanh::LeanObject,
    mut v___y_576_: *mut crate::leanh::LeanObject,
    mut v___y_577_: *mut crate::leanh::LeanObject,
    mut v___y_578_: *mut crate::leanh::LeanObject,
    mut v___y_579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_581_: u8 = 0;
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_575_) == 0 {
                    v___x_581_ = 0;
                    v___x_582_ = crate::leanh::lean_box((v___x_581_) as usize);
                    v___x_583_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_583_, 0, v___x_582_);
                    return v___x_583_;
                } else {
                    v_head_584_ = crate::leanh::lean_ctor_get(v_x_575_, 0);
                    crate::leanh::lean_inc(v_head_584_);
                    v_tail_585_ = crate::leanh::lean_ctor_get(v_x_575_, 1);
                    crate::leanh::lean_inc(v_tail_585_);
                    crate::leanh::lean_dec_ref_known(v_x_575_, 2);
                    v___x_586_ = l_Lean_Meta_hasAssignableLevelMVar(
                        v_head_584_,
                        v___y_576_,
                        v___y_577_,
                        v___y_578_,
                        v___y_579_,
                    );
                    v_a_587_ = crate::leanh::lean_ctor_get(v___x_586_, 0);
                    crate::leanh::lean_inc(v_a_587_);
                    v___x_588_ = (crate::leanh::lean_unbox(v_a_587_) as u8);
                    crate::leanh::lean_dec(v_a_587_);
                    if v___x_588_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_586_);
                        v_x_575_ = v_tail_585_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_585_);
                        return v___x_586_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg___boxed(
    mut v_x_590_: *mut crate::leanh::LeanObject,
    mut v___y_591_: *mut crate::leanh::LeanObject,
    mut v___y_592_: *mut crate::leanh::LeanObject,
    mut v___y_593_: *mut crate::leanh::LeanObject,
    mut v___y_594_: *mut crate::leanh::LeanObject,
    mut v___y_595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_596_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_x_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
    crate::leanh::lean_dec(v___y_594_);
    crate::leanh::lean_dec_ref(v___y_593_);
    crate::leanh::lean_dec(v___y_592_);
    crate::leanh::lean_dec_ref(v___y_591_);
    return v_res_596_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(
    mut v_a_597_: *mut crate::leanh::LeanObject,
    mut v_x_598_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_599_: u8 = 0;
    let mut v_key_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_598_) == 0 {
                    v___x_599_ = 0;
                    return v___x_599_;
                } else {
                    v_key_600_ = crate::leanh::lean_ctor_get(v_x_598_, 0);
                    v_tail_601_ = crate::leanh::lean_ctor_get(v_x_598_, 2);
                    v___x_602_ = lean_expr_eqv(v_key_600_, v_a_597_);
                    if v___x_602_ == 0 {
                        v_x_598_ = v_tail_601_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_602_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg___boxed(
    mut v_a_604_: *mut crate::leanh::LeanObject,
    mut v_x_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_606_: u8 = 0;
    let mut v_r_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_606_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_604_, v_x_605_);
    crate::leanh::lean_dec(v_x_605_);
    crate::leanh::lean_dec_ref(v_a_604_);
    v_r_607_ = crate::leanh::lean_box((v_res_606_) as usize);
    return v_r_607_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(
    mut v_m_608_: *mut crate::leanh::LeanObject,
    mut v_a_609_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: u64 = 0;
    let mut v___x_613_: u64 = 0;
    let mut v___x_614_: u64 = 0;
    let mut v_fold_615_: u64 = 0;
    let mut v___x_616_: u64 = 0;
    let mut v___x_617_: u64 = 0;
    let mut v___x_618_: u64 = 0;
    let mut v___x_619_: usize = 0;
    let mut v___x_620_: usize = 0;
    let mut v___x_621_: usize = 0;
    let mut v___x_622_: usize = 0;
    let mut v___x_623_: usize = 0;
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: u8 = 0;
    v_buckets_610_ = crate::leanh::lean_ctor_get(v_m_608_, 1);
    v___x_611_ = lean_array_get_size(v_buckets_610_);
    v___x_612_ = l_Lean_Expr_hash(v_a_609_);
    v___x_613_ = 32u64;
    v___x_614_ = lean_uint64_shift_right(v___x_612_, v___x_613_);
    v_fold_615_ = lean_uint64_xor(v___x_612_, v___x_614_);
    v___x_616_ = 16u64;
    v___x_617_ = lean_uint64_shift_right(v_fold_615_, v___x_616_);
    v___x_618_ = lean_uint64_xor(v_fold_615_, v___x_617_);
    v___x_619_ = lean_uint64_to_usize(v___x_618_);
    v___x_620_ = lean_usize_of_nat(v___x_611_);
    v___x_621_ = 1usize;
    v___x_622_ = lean_usize_sub(v___x_620_, v___x_621_);
    v___x_623_ = lean_usize_land(v___x_619_, v___x_622_);
    v___x_624_ = lean_array_uget_borrowed(v_buckets_610_, v___x_623_);
    v___x_625_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_609_, v___x_624_);
    return v___x_625_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg___boxed(
    mut v_m_626_: *mut crate::leanh::LeanObject,
    mut v_a_627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_628_: u8 = 0;
    let mut v_r_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_628_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v_m_626_, v_a_627_);
    crate::leanh::lean_dec_ref(v_a_627_);
    crate::leanh::lean_dec_ref(v_m_626_);
    v_r_629_ = crate::leanh::lean_box((v_res_628_) as usize);
    return v_r_629_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7___redArg(
    mut v_x_630_: *mut crate::leanh::LeanObject,
    mut v_x_631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_637_: u8 = 0;
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: u64 = 0;
    let mut v___x_640_: u64 = 0;
    let mut v___x_641_: u64 = 0;
    let mut v_fold_642_: u64 = 0;
    let mut v___x_643_: u64 = 0;
    let mut v___x_644_: u64 = 0;
    let mut v___x_645_: u64 = 0;
    let mut v___x_646_: usize = 0;
    let mut v___x_647_: usize = 0;
    let mut v___x_648_: usize = 0;
    let mut v___x_649_: usize = 0;
    let mut v___x_650_: usize = 0;
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_631_) == 0 {
                    return v_x_630_;
                } else {
                    v_key_632_ = crate::leanh::lean_ctor_get(v_x_631_, 0);
                    v_value_633_ = crate::leanh::lean_ctor_get(v_x_631_, 1);
                    v_tail_634_ = crate::leanh::lean_ctor_get(v_x_631_, 2);
                    v_isSharedCheck_657_ = (!crate::leanh::lean_is_exclusive(v_x_631_)) as u8;
                    if v_isSharedCheck_657_ == 0 {
                        v___x_636_ = v_x_631_;
                        v_isShared_637_ = v_isSharedCheck_657_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_634_);
                        crate::leanh::lean_inc(v_value_633_);
                        crate::leanh::lean_inc(v_key_632_);
                        crate::leanh::lean_dec(v_x_631_);
                        v___x_636_ = crate::leanh::lean_box(0);
                        v_isShared_637_ = v_isSharedCheck_657_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_638_ = lean_array_get_size(v_x_630_);
                v___x_639_ = l_Lean_Expr_hash(v_key_632_);
                v___x_640_ = 32u64;
                v___x_641_ = lean_uint64_shift_right(v___x_639_, v___x_640_);
                v_fold_642_ = lean_uint64_xor(v___x_639_, v___x_641_);
                v___x_643_ = 16u64;
                v___x_644_ = lean_uint64_shift_right(v_fold_642_, v___x_643_);
                v___x_645_ = lean_uint64_xor(v_fold_642_, v___x_644_);
                v___x_646_ = lean_uint64_to_usize(v___x_645_);
                v___x_647_ = lean_usize_of_nat(v___x_638_);
                v___x_648_ = 1usize;
                v___x_649_ = lean_usize_sub(v___x_647_, v___x_648_);
                v___x_650_ = lean_usize_land(v___x_646_, v___x_649_);
                v___x_651_ = lean_array_uget_borrowed(v_x_630_, v___x_650_);
                crate::leanh::lean_inc(v___x_651_);
                if v_isShared_637_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_636_, 2, v___x_651_);
                    v___x_653_ = v___x_636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_656_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_656_, 0, v_key_632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_656_, 1, v_value_633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_656_, 2, v___x_651_);
                    v___x_653_ = v_reuseFailAlloc_656_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_654_ = lean_array_uset(v_x_630_, v___x_650_, v___x_653_);
                v_x_630_ = v___x_654_;
                v_x_631_ = v_tail_634_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6___redArg(
    mut v_i_658_: *mut crate::leanh::LeanObject,
    mut v_source_659_: *mut crate::leanh::LeanObject,
    mut v_target_660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: u8 = 0;
    let mut v_es_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_661_ = lean_array_get_size(v_source_659_);
                v___x_662_ = lean_nat_dec_lt(v_i_658_, v___x_661_);
                if v___x_662_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_659_);
                    crate::leanh::lean_dec(v_i_658_);
                    return v_target_660_;
                } else {
                    v_es_663_ = lean_array_fget(v_source_659_, v_i_658_);
                    v___x_664_ = crate::leanh::lean_box(0);
                    v_source_665_ = lean_array_fset(v_source_659_, v_i_658_, v___x_664_);
                    v_target_666_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_target_660_, v_es_663_);
                    v___x_667_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_668_ = lean_nat_add(v_i_658_, v___x_667_);
                    crate::leanh::lean_dec(v_i_658_);
                    v_i_658_ = v___x_668_;
                    v_source_659_ = v_source_665_;
                    v_target_660_ = v_target_666_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(
    mut v_data_670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_671_ = lean_array_get_size(v_data_670_);
    v___x_672_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_673_ = lean_nat_mul(v___x_671_, v___x_672_);
    v___x_674_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_675_ = crate::leanh::lean_box(0);
    v___x_676_ = lean_mk_array(v_nbuckets_673_, v___x_675_);
    v___x_677_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6___redArg(v___x_674_, v_data_670_, v___x_676_);
    return v___x_677_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(
    mut v_m_678_: *mut crate::leanh::LeanObject,
    mut v_a_679_: *mut crate::leanh::LeanObject,
    mut v_b_680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: u64 = 0;
    let mut v___x_685_: u64 = 0;
    let mut v___x_686_: u64 = 0;
    let mut v_fold_687_: u64 = 0;
    let mut v___x_688_: u64 = 0;
    let mut v___x_689_: u64 = 0;
    let mut v___x_690_: u64 = 0;
    let mut v___x_691_: usize = 0;
    let mut v___x_692_: usize = 0;
    let mut v___x_693_: usize = 0;
    let mut v___x_694_: usize = 0;
    let mut v___x_695_: usize = 0;
    let mut v_bkt_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: u8 = 0;
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_700_: u8 = 0;
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: u8 = 0;
    let mut v_val_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_718_: u8 = 0;
    let mut v_unused_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_681_ = crate::leanh::lean_ctor_get(v_m_678_, 0);
                v_buckets_682_ = crate::leanh::lean_ctor_get(v_m_678_, 1);
                v___x_683_ = lean_array_get_size(v_buckets_682_);
                v___x_684_ = l_Lean_Expr_hash(v_a_679_);
                v___x_685_ = 32u64;
                v___x_686_ = lean_uint64_shift_right(v___x_684_, v___x_685_);
                v_fold_687_ = lean_uint64_xor(v___x_684_, v___x_686_);
                v___x_688_ = 16u64;
                v___x_689_ = lean_uint64_shift_right(v_fold_687_, v___x_688_);
                v___x_690_ = lean_uint64_xor(v_fold_687_, v___x_689_);
                v___x_691_ = lean_uint64_to_usize(v___x_690_);
                v___x_692_ = lean_usize_of_nat(v___x_683_);
                v___x_693_ = 1usize;
                v___x_694_ = lean_usize_sub(v___x_692_, v___x_693_);
                v___x_695_ = lean_usize_land(v___x_691_, v___x_694_);
                v_bkt_696_ = lean_array_uget_borrowed(v_buckets_682_, v___x_695_);
                v___x_697_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_679_, v_bkt_696_);
                if v___x_697_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_682_);
                    crate::leanh::lean_inc(v_size_681_);
                    v_isSharedCheck_718_ = (!crate::leanh::lean_is_exclusive(v_m_678_)) as u8;
                    if v_isSharedCheck_718_ == 0 {
                        v_unused_719_ = crate::leanh::lean_ctor_get(v_m_678_, 1);
                        crate::leanh::lean_dec(v_unused_719_);
                        v_unused_720_ = crate::leanh::lean_ctor_get(v_m_678_, 0);
                        crate::leanh::lean_dec(v_unused_720_);
                        v___x_699_ = v_m_678_;
                        v_isShared_700_ = v_isSharedCheck_718_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_678_);
                        v___x_699_ = crate::leanh::lean_box(0);
                        v_isShared_700_ = v_isSharedCheck_718_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_680_);
                    crate::leanh::lean_dec_ref(v_a_679_);
                    return v_m_678_;
                }
            }
            1 => {
                v___x_701_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_702_ = lean_nat_add(v_size_681_, v___x_701_);
                crate::leanh::lean_dec(v_size_681_);
                crate::leanh::lean_inc(v_bkt_696_);
                v___x_703_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_703_, 0, v_a_679_);
                crate::leanh::lean_ctor_set(v___x_703_, 1, v_b_680_);
                crate::leanh::lean_ctor_set(v___x_703_, 2, v_bkt_696_);
                v_buckets_x27_704_ = lean_array_uset(v_buckets_682_, v___x_695_, v___x_703_);
                v___x_705_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_706_ = lean_nat_mul(v_size_x27_702_, v___x_705_);
                v___x_707_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_708_ = lean_nat_div(v___x_706_, v___x_707_);
                crate::leanh::lean_dec(v___x_706_);
                v___x_709_ = lean_array_get_size(v_buckets_x27_704_);
                v___x_710_ = lean_nat_dec_le(v___x_708_, v___x_709_);
                crate::leanh::lean_dec(v___x_708_);
                if v___x_710_ == 0 {
                    v_val_711_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(v_buckets_x27_704_);
                    if v_isShared_700_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_699_, 1, v_val_711_);
                        crate::leanh::lean_ctor_set(v___x_699_, 0, v_size_x27_702_);
                        v___x_713_ = v___x_699_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_714_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_714_, 0, v_size_x27_702_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_714_, 1, v_val_711_);
                        v___x_713_ = v_reuseFailAlloc_714_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_700_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_699_, 1, v_buckets_x27_704_);
                        crate::leanh::lean_ctor_set(v___x_699_, 0, v_size_x27_702_);
                        v___x_716_ = v___x_699_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_717_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_717_, 0, v_size_x27_702_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_717_, 1, v_buckets_x27_704_);
                        v___x_716_ = v_reuseFailAlloc_717_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_713_;
            }
            3 => {
                return v___x_716_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(
    mut v_e_722_: *mut crate::leanh::LeanObject,
    mut v_a_723_: *mut crate::leanh::LeanObject,
    mut v_a_724_: *mut crate::leanh::LeanObject,
    mut v_a_725_: *mut crate::leanh::LeanObject,
    mut v_a_726_: *mut crate::leanh::LeanObject,
    mut v_a_727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: u8 = 0;
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_746_: u8 = 0;
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_750_: u8 = 0;
    let mut v_mvarId_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: u8 = 0;
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_768_: u8 = 0;
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_772_: u8 = 0;
    let mut v_binderType_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: u8 = 0;
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: u8 = 0;
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_792_: u8 = 0;
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_796_: u8 = 0;
    let mut v_expr_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: u8 = 0;
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_722_) {
                2 => {
                    v_mvarId_751_ = crate::leanh::lean_ctor_get(v_e_722_, 0);
                    crate::leanh::lean_inc(v_mvarId_751_);
                    crate::leanh::lean_dec_ref_known(v_e_722_, 1);
                    v___x_752_ = l_Lean_MVarId_isAssignable___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__0___redArg(v_mvarId_751_, v_a_725_);
                    return v___x_752_;
                }
                3 => {
                    v_u_753_ = crate::leanh::lean_ctor_get(v_e_722_, 0);
                    crate::leanh::lean_inc(v_u_753_);
                    crate::leanh::lean_dec_ref_known(v_e_722_, 1);
                    v___x_754_ = l_Lean_Meta_hasAssignableLevelMVar(
                        v_u_753_, v_a_724_, v_a_725_, v_a_726_, v_a_727_,
                    );
                    return v___x_754_;
                }
                4 => {
                    v_us_755_ = crate::leanh::lean_ctor_get(v_e_722_, 1);
                    crate::leanh::lean_inc(v_us_755_);
                    crate::leanh::lean_dec_ref_known(v_e_722_, 2);
                    v___x_756_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_us_755_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
                    return v___x_756_;
                }
                5 => {
                    v_fn_757_ = crate::leanh::lean_ctor_get(v_e_722_, 0);
                    crate::leanh::lean_inc_ref(v_fn_757_);
                    v_arg_758_ = crate::leanh::lean_ctor_get(v_e_722_, 1);
                    crate::leanh::lean_inc_ref(v_arg_758_);
                    crate::leanh::lean_dec_ref_known(v_e_722_, 2);
                    v___x_759_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0;
                    v___x_760_ = l_Lean_Core_checkSystem(v___x_759_, v_a_726_, v_a_727_);
                    if crate::leanh::lean_obj_tag(v___x_760_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_760_, 1);
                        v___x_761_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_fn_757_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
                        if crate::leanh::lean_obj_tag(v___x_761_) == 0 {
                            v_a_762_ = crate::leanh::lean_ctor_get(v___x_761_, 0);
                            crate::leanh::lean_inc(v_a_762_);
                            v___x_763_ = (crate::leanh::lean_unbox(v_a_762_) as u8);
                            crate::leanh::lean_dec(v_a_762_);
                            if v___x_763_ == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_761_, 1);
                                v___x_764_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_arg_758_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
                                return v___x_764_;
                            } else {
                                crate::leanh::lean_dec_ref(v_arg_758_);
                                return v___x_761_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_arg_758_);
                            return v___x_761_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_758_);
                        crate::leanh::lean_dec_ref(v_fn_757_);
                        v_a_765_ = crate::leanh::lean_ctor_get(v___x_760_, 0);
                        v_isSharedCheck_772_ = (!crate::leanh::lean_is_exclusive(v___x_760_)) as u8;
                        if v_isSharedCheck_772_ == 0 {
                            v___x_767_ = v___x_760_;
                            v_isShared_768_ = v_isSharedCheck_772_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_765_);
                            crate::leanh::lean_dec(v___x_760_);
                            v___x_767_ = crate::leanh::lean_box(0);
                            v_isShared_768_ = v_isSharedCheck_772_;
                            state = 4;
                            continue;
                        }
                    }
                }
                6 => {
                    v_binderType_773_ = crate::leanh::lean_ctor_get(v_e_722_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_773_);
                    v_body_774_ = crate::leanh::lean_ctor_get(v_e_722_, 2);
                    crate::leanh::lean_inc_ref(v_body_774_);
                    crate::leanh::lean_dec_ref_known(v_e_722_, 3);
                    v_d_730_ = v_binderType_773_;
                    v_b_731_ = v_body_774_;
                    v___y_732_ = v_a_723_;
                    v___y_733_ = v_a_724_;
                    v___y_734_ = v_a_725_;
                    v___y_735_ = v_a_726_;
                    v___y_736_ = v_a_727_;
                    state = 1;
                    continue;
                }
                7 => {
                    v_binderType_775_ = crate::leanh::lean_ctor_get(v_e_722_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_775_);
                    v_body_776_ = crate::leanh::lean_ctor_get(v_e_722_, 2);
                    crate::leanh::lean_inc_ref(v_body_776_);
                    crate::leanh::lean_dec_ref_known(v_e_722_, 3);
                    v_d_730_ = v_binderType_775_;
                    v_b_731_ = v_body_776_;
                    v___y_732_ = v_a_723_;
                    v___y_733_ = v_a_724_;
                    v___y_734_ = v_a_725_;
                    v___y_735_ = v_a_726_;
                    v___y_736_ = v_a_727_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_type_777_ = crate::leanh::lean_ctor_get(v_e_722_, 1);
                    crate::leanh::lean_inc_ref(v_type_777_);
                    v_value_778_ = crate::leanh::lean_ctor_get(v_e_722_, 2);
                    crate::leanh::lean_inc_ref(v_value_778_);
                    v_body_779_ = crate::leanh::lean_ctor_get(v_e_722_, 3);
                    crate::leanh::lean_inc_ref(v_body_779_);
                    crate::leanh::lean_dec_ref_known(v_e_722_, 4);
                    v___x_780_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0;
                    v___x_781_ = l_Lean_Core_checkSystem(v___x_780_, v_a_726_, v_a_727_);
                    if crate::leanh::lean_obj_tag(v___x_781_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_781_, 1);
                        v___x_782_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_type_777_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
                        if crate::leanh::lean_obj_tag(v___x_782_) == 0 {
                            v_a_783_ = crate::leanh::lean_ctor_get(v___x_782_, 0);
                            crate::leanh::lean_inc(v_a_783_);
                            v___x_784_ = (crate::leanh::lean_unbox(v_a_783_) as u8);
                            crate::leanh::lean_dec(v_a_783_);
                            if v___x_784_ == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_782_, 1);
                                v___x_785_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_value_778_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
                                if crate::leanh::lean_obj_tag(v___x_785_) == 0 {
                                    v_a_786_ = crate::leanh::lean_ctor_get(v___x_785_, 0);
                                    crate::leanh::lean_inc(v_a_786_);
                                    v___x_787_ = (crate::leanh::lean_unbox(v_a_786_) as u8);
                                    crate::leanh::lean_dec(v_a_786_);
                                    if v___x_787_ == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_785_, 1);
                                        v___x_788_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_body_779_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
                                        return v___x_788_;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_body_779_);
                                        return v___x_785_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_body_779_);
                                    return v___x_785_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_body_779_);
                                crate::leanh::lean_dec_ref(v_value_778_);
                                return v___x_782_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_body_779_);
                            crate::leanh::lean_dec_ref(v_value_778_);
                            return v___x_782_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_779_);
                        crate::leanh::lean_dec_ref(v_value_778_);
                        crate::leanh::lean_dec_ref(v_type_777_);
                        v_a_789_ = crate::leanh::lean_ctor_get(v___x_781_, 0);
                        v_isSharedCheck_796_ = (!crate::leanh::lean_is_exclusive(v___x_781_)) as u8;
                        if v_isSharedCheck_796_ == 0 {
                            v___x_791_ = v___x_781_;
                            v_isShared_792_ = v_isSharedCheck_796_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_789_);
                            crate::leanh::lean_dec(v___x_781_);
                            v___x_791_ = crate::leanh::lean_box(0);
                            v_isShared_792_ = v_isSharedCheck_796_;
                            state = 6;
                            continue;
                        }
                    }
                }
                10 => {
                    v_expr_797_ = crate::leanh::lean_ctor_get(v_e_722_, 1);
                    crate::leanh::lean_inc_ref(v_expr_797_);
                    crate::leanh::lean_dec_ref_known(v_e_722_, 2);
                    v___x_798_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_expr_797_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
                    return v___x_798_;
                }
                11 => {
                    v_struct_799_ = crate::leanh::lean_ctor_get(v_e_722_, 2);
                    crate::leanh::lean_inc_ref(v_struct_799_);
                    crate::leanh::lean_dec_ref_known(v_e_722_, 3);
                    v___x_800_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_struct_799_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
                    return v___x_800_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_722_);
                    v___x_801_ = 0;
                    v___x_802_ = crate::leanh::lean_box((v___x_801_) as usize);
                    v___x_803_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_803_, 0, v___x_802_);
                    return v___x_803_;
                }
            },
            1 => {
                v___x_737_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___closed__0;
                v___x_738_ = l_Lean_Core_checkSystem(v___x_737_, v___y_735_, v___y_736_);
                if crate::leanh::lean_obj_tag(v___x_738_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_738_, 1);
                    v___x_739_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_d_730_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
                    if crate::leanh::lean_obj_tag(v___x_739_) == 0 {
                        v_a_740_ = crate::leanh::lean_ctor_get(v___x_739_, 0);
                        crate::leanh::lean_inc(v_a_740_);
                        v___x_741_ = (crate::leanh::lean_unbox(v_a_740_) as u8);
                        crate::leanh::lean_dec(v_a_740_);
                        if v___x_741_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_739_, 1);
                            v___x_742_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(v_b_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
                            return v___x_742_;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_731_);
                            return v___x_739_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_731_);
                        return v___x_739_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_731_);
                    crate::leanh::lean_dec_ref(v_d_730_);
                    v_a_743_ = crate::leanh::lean_ctor_get(v___x_738_, 0);
                    v_isSharedCheck_750_ = (!crate::leanh::lean_is_exclusive(v___x_738_)) as u8;
                    if v_isSharedCheck_750_ == 0 {
                        v___x_745_ = v___x_738_;
                        v_isShared_746_ = v_isSharedCheck_750_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_743_);
                        crate::leanh::lean_dec(v___x_738_);
                        v___x_745_ = crate::leanh::lean_box(0);
                        v_isShared_746_ = v_isSharedCheck_750_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_746_ == 0 {
                    v___x_748_ = v___x_745_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_749_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
                    v___x_748_ = v_reuseFailAlloc_749_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_748_;
            }
            4 => {
                if v_isShared_768_ == 0 {
                    v___x_770_ = v___x_767_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_771_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
                    v___x_770_ = v_reuseFailAlloc_771_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_770_;
            }
            6 => {
                if v_isShared_792_ == 0 {
                    v___x_794_ = v___x_791_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_795_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
                    v___x_794_ = v_reuseFailAlloc_795_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(
    mut v_e_804_: *mut crate::leanh::LeanObject,
    mut v_a_805_: *mut crate::leanh::LeanObject,
    mut v_a_806_: *mut crate::leanh::LeanObject,
    mut v_a_807_: *mut crate::leanh::LeanObject,
    mut v_a_808_: *mut crate::leanh::LeanObject,
    mut v_a_809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_811_: u8 = 0;
    v___x_811_ = l_Lean_Expr_hasMVar(v_e_804_);
    if v___x_811_ == 0 {
        let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_804_);
        v___x_812_ = crate::leanh::lean_box((v___x_811_) as usize);
        v___x_813_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_813_, 0, v___x_812_);
        return v___x_813_;
    } else {
        let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_815_: u8 = 0;
        v___x_814_ = lean_st_ref_get(v_a_805_);
        v___x_815_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v___x_814_, v_e_804_);
        crate::leanh::lean_dec(v___x_814_);
        if v___x_815_ == 0 {
            let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_816_ = lean_st_ref_take(v_a_805_);
            v___x_817_ = crate::leanh::lean_box(0);
            crate::leanh::lean_inc_ref(v_e_804_);
            v___x_818_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v___x_816_, v_e_804_, v___x_817_);
            v___x_819_ = lean_st_ref_set(v_a_805_, v___x_818_);
            v___x_820_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(
                v_e_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_,
            );
            return v___x_820_;
        } else {
            let mut v___x_821_: u8 = 0;
            let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_e_804_);
            v___x_821_ = 0;
            v___x_822_ = crate::leanh::lean_box((v___x_821_) as usize);
            v___x_823_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_823_, 0, v___x_822_);
            return v___x_823_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit___boxed(
    mut v_e_824_: *mut crate::leanh::LeanObject,
    mut v_a_825_: *mut crate::leanh::LeanObject,
    mut v_a_826_: *mut crate::leanh::LeanObject,
    mut v_a_827_: *mut crate::leanh::LeanObject,
    mut v_a_828_: *mut crate::leanh::LeanObject,
    mut v_a_829_: *mut crate::leanh::LeanObject,
    mut v_a_830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_831_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit(
        v_e_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_,
    );
    crate::leanh::lean_dec(v_a_829_);
    crate::leanh::lean_dec_ref(v_a_828_);
    crate::leanh::lean_dec(v_a_827_);
    crate::leanh::lean_dec_ref(v_a_826_);
    crate::leanh::lean_dec(v_a_825_);
    return v_res_831_;
}
pub unsafe fn l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go___boxed(
    mut v_e_832_: *mut crate::leanh::LeanObject,
    mut v_a_833_: *mut crate::leanh::LeanObject,
    mut v_a_834_: *mut crate::leanh::LeanObject,
    mut v_a_835_: *mut crate::leanh::LeanObject,
    mut v_a_836_: *mut crate::leanh::LeanObject,
    mut v_a_837_: *mut crate::leanh::LeanObject,
    mut v_a_838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_839_ = l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(
        v_e_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_,
    );
    crate::leanh::lean_dec(v_a_837_);
    crate::leanh::lean_dec_ref(v_a_836_);
    crate::leanh::lean_dec(v_a_835_);
    crate::leanh::lean_dec_ref(v_a_834_);
    crate::leanh::lean_dec(v_a_833_);
    return v_res_839_;
}
pub unsafe fn l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1(
    mut v_x_840_: *mut crate::leanh::LeanObject,
    mut v___y_841_: *mut crate::leanh::LeanObject,
    mut v___y_842_: *mut crate::leanh::LeanObject,
    mut v___y_843_: *mut crate::leanh::LeanObject,
    mut v___y_844_: *mut crate::leanh::LeanObject,
    mut v___y_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_847_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___redArg(v_x_840_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
    return v___x_847_;
}
pub unsafe fn l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1___boxed(
    mut v_x_848_: *mut crate::leanh::LeanObject,
    mut v___y_849_: *mut crate::leanh::LeanObject,
    mut v___y_850_: *mut crate::leanh::LeanObject,
    mut v___y_851_: *mut crate::leanh::LeanObject,
    mut v___y_852_: *mut crate::leanh::LeanObject,
    mut v___y_853_: *mut crate::leanh::LeanObject,
    mut v___y_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_855_ = l_List_anyM___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go_spec__1(v_x_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
    crate::leanh::lean_dec(v___y_853_);
    crate::leanh::lean_dec_ref(v___y_852_);
    crate::leanh::lean_dec(v___y_851_);
    crate::leanh::lean_dec_ref(v___y_850_);
    crate::leanh::lean_dec(v___y_849_);
    return v_res_855_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3(
    mut v_00_u03b2_856_: *mut crate::leanh::LeanObject,
    mut v_m_857_: *mut crate::leanh::LeanObject,
    mut v_a_858_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_859_: u8 = 0;
    v___x_859_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___redArg(v_m_857_, v_a_858_);
    return v___x_859_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3___boxed(
    mut v_00_u03b2_860_: *mut crate::leanh::LeanObject,
    mut v_m_861_: *mut crate::leanh::LeanObject,
    mut v_a_862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_863_: u8 = 0;
    let mut v_r_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_863_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3(v_00_u03b2_860_, v_m_861_, v_a_862_);
    crate::leanh::lean_dec_ref(v_a_862_);
    crate::leanh::lean_dec_ref(v_m_861_);
    v_r_864_ = crate::leanh::lean_box((v_res_863_) as usize);
    return v_r_864_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4(
    mut v_00_u03b2_865_: *mut crate::leanh::LeanObject,
    mut v_m_866_: *mut crate::leanh::LeanObject,
    mut v_a_867_: *mut crate::leanh::LeanObject,
    mut v_b_868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4___redArg(v_m_866_, v_a_867_, v_b_868_);
    return v___x_869_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3(
    mut v_00_u03b2_870_: *mut crate::leanh::LeanObject,
    mut v_a_871_: *mut crate::leanh::LeanObject,
    mut v_x_872_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_873_: u8 = 0;
    v___x_873_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___redArg(v_a_871_, v_x_872_);
    return v___x_873_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3___boxed(
    mut v_00_u03b2_874_: *mut crate::leanh::LeanObject,
    mut v_a_875_: *mut crate::leanh::LeanObject,
    mut v_x_876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_877_: u8 = 0;
    let mut v_r_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_877_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__3_spec__3(v_00_u03b2_874_, v_a_875_, v_x_876_);
    crate::leanh::lean_dec(v_x_876_);
    crate::leanh::lean_dec_ref(v_a_875_);
    v_r_878_ = crate::leanh::lean_box((v_res_877_) as usize);
    return v_r_878_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5(
    mut v_00_u03b2_879_: *mut crate::leanh::LeanObject,
    mut v_data_880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_881_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5___redArg(v_data_880_);
    return v___x_881_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6(
    mut v_00_u03b2_882_: *mut crate::leanh::LeanObject,
    mut v_i_883_: *mut crate::leanh::LeanObject,
    mut v_source_884_: *mut crate::leanh::LeanObject,
    mut v_target_885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6___redArg(v_i_883_, v_source_884_, v_target_885_);
    return v___x_886_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7(
    mut v_00_u03b2_887_: *mut crate::leanh::LeanObject,
    mut v_x_888_: *mut crate::leanh::LeanObject,
    mut v_x_889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_x_888_, v_x_889_);
    return v___x_890_;
}
pub unsafe fn _init_l_Lean_Meta_hasAssignableMVar___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = crate::leanh::lean_box(0);
    v___x_892_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_893_ = lean_mk_array(v___x_892_, v___x_891_);
    return v___x_893_;
}
pub unsafe fn _init_l_Lean_Meta_hasAssignableMVar___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_894_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_hasAssignableMVar___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_hasAssignableMVar___closed__0_once),
        _init_l_Lean_Meta_hasAssignableMVar___closed__0,
    );
    v___x_895_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_896_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_896_, 0, v___x_895_);
    crate::leanh::lean_ctor_set(v___x_896_, 1, v___x_894_);
    return v___x_896_;
}
pub unsafe fn l_Lean_Meta_hasAssignableMVar(
    mut v_e_897_: *mut crate::leanh::LeanObject,
    mut v_a_898_: *mut crate::leanh::LeanObject,
    mut v_a_899_: *mut crate::leanh::LeanObject,
    mut v_a_900_: *mut crate::leanh::LeanObject,
    mut v_a_901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_903_: u8 = 0;
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_912_: u8 = 0;
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_917_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_903_ = l_Lean_Expr_hasMVar(v_e_897_);
                if v___x_903_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_897_);
                    v___x_904_ = crate::leanh::lean_box((v___x_903_) as usize);
                    v___x_905_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_905_, 0, v___x_904_);
                    return v___x_905_;
                } else {
                    v___x_906_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_hasAssignableMVar___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_hasAssignableMVar___closed__1_once),
                        _init_l_Lean_Meta_hasAssignableMVar___closed__1,
                    );
                    v___x_907_ = lean_st_mk_ref(v___x_906_);
                    v___x_908_ =
                        l___private_Lean_Meta_HasAssignableMVar_0__Lean_Meta_hasAssignableMVar_go(
                            v_e_897_, v___x_907_, v_a_898_, v_a_899_, v_a_900_, v_a_901_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_908_) == 0 {
                        v_a_909_ = crate::leanh::lean_ctor_get(v___x_908_, 0);
                        v_isSharedCheck_917_ = (!crate::leanh::lean_is_exclusive(v___x_908_)) as u8;
                        if v_isSharedCheck_917_ == 0 {
                            v___x_911_ = v___x_908_;
                            v_isShared_912_ = v_isSharedCheck_917_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_909_);
                            crate::leanh::lean_dec(v___x_908_);
                            v___x_911_ = crate::leanh::lean_box(0);
                            v_isShared_912_ = v_isSharedCheck_917_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_907_);
                        return v___x_908_;
                    }
                }
            }
            1 => {
                v___x_913_ = lean_st_ref_get(v___x_907_);
                crate::leanh::lean_dec(v___x_907_);
                crate::leanh::lean_dec(v___x_913_);
                if v_isShared_912_ == 0 {
                    v___x_915_ = v___x_911_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_916_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_909_);
                    v___x_915_ = v_reuseFailAlloc_916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_915_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_hasAssignableMVar___boxed(
    mut v_e_918_: *mut crate::leanh::LeanObject,
    mut v_a_919_: *mut crate::leanh::LeanObject,
    mut v_a_920_: *mut crate::leanh::LeanObject,
    mut v_a_921_: *mut crate::leanh::LeanObject,
    mut v_a_922_: *mut crate::leanh::LeanObject,
    mut v_a_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_924_ = l_Lean_Meta_hasAssignableMVar(v_e_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
    crate::leanh::lean_dec(v_a_922_);
    crate::leanh::lean_dec_ref(v_a_921_);
    crate::leanh::lean_dec(v_a_920_);
    crate::leanh::lean_dec_ref(v_a_919_);
    return v_res_924_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_HasAssignableMVar(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_HasAssignableMVar(
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
pub unsafe fn initialize_Lean_Meta_HasAssignableMVar(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_HasAssignableMVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_HasAssignableMVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_HasAssignableMVar(builtin);
}
