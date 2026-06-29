// Lean compiler output
// Module: Lean.Util.ReplaceLevel
// Imports: Lean.Expr
use crate::ffi::{
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_ptr_addr,
    lean_usize_dec_eq, lean_usize_mod, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Util::l_ptrEqList___redArg;
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_app___override, l_Lean_Expr_const___override,
    l_Lean_Expr_forallE___override, l_Lean_Expr_lam___override, l_Lean_Expr_letE___override,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_Expr_sort___override,
    l_Lean_instBEqBinderInfo_beq, runtime_initialize_Lean_Expr,
};
use crate::r#gen::Lean::Level::{
    l_Lean_Level_succ___override, l_Lean_mkLevelIMax_x27, l_Lean_mkLevelMax_x27,
};
static mut l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0: usize = 0;
pub static mut l_Lean_Expr_ReplaceLevelImpl_cacheSize: usize = 0;
pub static l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17542774118954891045 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Expr_ReplaceLevelImpl_initCache: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Level_replace(
    mut v_f_x3f_350_: *mut crate::leanh::LeanObject,
    mut v_u_351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_f_x3f_350_);
    crate::leanh::lean_inc(v_u_351_);
    v___x_352_ = crate::leanh::lean_apply_1(v_f_x3f_350_, v_u_351_);
    if crate::leanh::lean_obj_tag(v___x_352_) == 0 {
        match crate::leanh::lean_obj_tag(v_u_351_) {
            2 => {
                let mut v_a_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_353_ = crate::leanh::lean_ctor_get(v_u_351_, 0);
                crate::leanh::lean_inc(v_a_353_);
                v_a_354_ = crate::leanh::lean_ctor_get(v_u_351_, 1);
                crate::leanh::lean_inc(v_a_354_);
                crate::leanh::lean_dec_ref_known(v_u_351_, 2);
                crate::leanh::lean_inc_ref(v_f_x3f_350_);
                v___x_355_ = l_Lean_Level_replace(v_f_x3f_350_, v_a_353_);
                v___x_356_ = l_Lean_Level_replace(v_f_x3f_350_, v_a_354_);
                v___x_357_ = l_Lean_mkLevelMax_x27(v___x_355_, v___x_356_);
                return v___x_357_;
            }
            3 => {
                let mut v_a_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_358_ = crate::leanh::lean_ctor_get(v_u_351_, 0);
                crate::leanh::lean_inc(v_a_358_);
                v_a_359_ = crate::leanh::lean_ctor_get(v_u_351_, 1);
                crate::leanh::lean_inc(v_a_359_);
                crate::leanh::lean_dec_ref_known(v_u_351_, 2);
                crate::leanh::lean_inc_ref(v_f_x3f_350_);
                v___x_360_ = l_Lean_Level_replace(v_f_x3f_350_, v_a_358_);
                v___x_361_ = l_Lean_Level_replace(v_f_x3f_350_, v_a_359_);
                v___x_362_ = l_Lean_mkLevelIMax_x27(v___x_360_, v___x_361_);
                return v___x_362_;
            }
            1 => {
                let mut v_a_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_363_ = crate::leanh::lean_ctor_get(v_u_351_, 0);
                crate::leanh::lean_inc(v_a_363_);
                crate::leanh::lean_dec_ref_known(v_u_351_, 1);
                v___x_364_ = l_Lean_Level_replace(v_f_x3f_350_, v_a_363_);
                v___x_365_ = l_Lean_Level_succ___override(v___x_364_);
                return v___x_365_;
            }
            _ => {
                crate::leanh::lean_dec_ref(v_f_x3f_350_);
                return v_u_351_;
            }
        }
    } else {
        let mut v_val_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_u_351_);
        crate::leanh::lean_dec_ref(v_f_x3f_350_);
        v_val_366_ = crate::leanh::lean_ctor_get(v___x_352_, 0);
        crate::leanh::lean_inc(v_val_366_);
        crate::leanh::lean_dec_ref_known(v___x_352_, 1);
        return v_val_366_;
    }
}
pub unsafe fn _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0() -> usize {
    let mut v___x_367_: usize = 0;
    let mut v___x_368_: usize = 0;
    let mut v___x_369_: usize = 0;
    v___x_367_ = 1usize;
    v___x_368_ = 8192usize;
    v___x_369_ = lean_usize_sub(v___x_368_, v___x_367_);
    return v___x_369_;
}
pub unsafe fn _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize() -> usize {
    let mut v___x_370_: usize = 0;
    v___x_370_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0_once),
        _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0,
    );
    return v___x_370_;
}
pub unsafe fn l_Lean_Expr_ReplaceLevelImpl_cache(
    mut v_i_371_: usize,
    mut v_key_372_: *mut crate::leanh::LeanObject,
    mut v_result_373_: *mut crate::leanh::LeanObject,
    mut v_a_374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keys_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_results_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_379_: u8 = 0;
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_keys_375_ = crate::leanh::lean_ctor_get(v_a_374_, 0);
                v_results_376_ = crate::leanh::lean_ctor_get(v_a_374_, 1);
                v_isSharedCheck_386_ = (!crate::leanh::lean_is_exclusive(v_a_374_)) as u8;
                if v_isSharedCheck_386_ == 0 {
                    v___x_378_ = v_a_374_;
                    v_isShared_379_ = v_isSharedCheck_386_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_results_376_);
                    crate::leanh::lean_inc(v_keys_375_);
                    crate::leanh::lean_dec(v_a_374_);
                    v___x_378_ = crate::leanh::lean_box(0);
                    v_isShared_379_ = v_isSharedCheck_386_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_380_ = lean_array_uset(v_keys_375_, v_i_371_, v_key_372_);
                crate::leanh::lean_inc_ref(v_result_373_);
                v___x_381_ = lean_array_uset(v_results_376_, v_i_371_, v_result_373_);
                if v_isShared_379_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_378_, 1, v___x_381_);
                    crate::leanh::lean_ctor_set(v___x_378_, 0, v___x_380_);
                    v___x_383_ = v___x_378_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_385_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_385_, 1, v___x_381_);
                    v___x_383_ = v_reuseFailAlloc_385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_384_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_384_, 0, v_result_373_);
                crate::leanh::lean_ctor_set(v___x_384_, 1, v___x_383_);
                return v___x_384_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_ReplaceLevelImpl_cache___boxed(
    mut v_i_387_: *mut crate::leanh::LeanObject,
    mut v_key_388_: *mut crate::leanh::LeanObject,
    mut v_result_389_: *mut crate::leanh::LeanObject,
    mut v_a_390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_391_: usize = 0;
    let mut v_res_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_391_ = crate::leanh::lean_unbox_usize(v_i_387_);
    crate::leanh::lean_dec(v_i_387_);
    v_res_392_ =
        l_Lean_Expr_ReplaceLevelImpl_cache(v_i_boxed_391_, v_key_388_, v_result_389_, v_a_390_);
    return v_res_392_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(
    mut v_f_x3f_393_: *mut crate::leanh::LeanObject,
    mut v_a_394_: *mut crate::leanh::LeanObject,
    mut v_a_395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_401_: u8 = 0;
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_394_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_x3f_393_);
                    v___x_396_ = l_List_reverse___redArg(v_a_395_);
                    return v___x_396_;
                } else {
                    v_head_397_ = crate::leanh::lean_ctor_get(v_a_394_, 0);
                    v_tail_398_ = crate::leanh::lean_ctor_get(v_a_394_, 1);
                    v_isSharedCheck_407_ = (!crate::leanh::lean_is_exclusive(v_a_394_)) as u8;
                    if v_isSharedCheck_407_ == 0 {
                        v___x_400_ = v_a_394_;
                        v_isShared_401_ = v_isSharedCheck_407_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_398_);
                        crate::leanh::lean_inc(v_head_397_);
                        crate::leanh::lean_dec(v_a_394_);
                        v___x_400_ = crate::leanh::lean_box(0);
                        v_isShared_401_ = v_isSharedCheck_407_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_x3f_393_);
                v___x_402_ = l_Lean_Level_replace(v_f_x3f_393_, v_head_397_);
                if v_isShared_401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_400_, 1, v_a_395_);
                    crate::leanh::lean_ctor_set(v___x_400_, 0, v___x_402_);
                    v___x_404_ = v___x_400_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_406_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_402_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_406_, 1, v_a_395_);
                    v___x_404_ = v_reuseFailAlloc_406_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_394_ = v_tail_398_;
                v_a_395_ = v___x_404_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(
    mut v_f_x3f_408_: *mut crate::leanh::LeanObject,
    mut v_size_409_: usize,
    mut v_e_410_: *mut crate::leanh::LeanObject,
    mut v_a_411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keys_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_results_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: usize = 0;
    let mut v___x_415_: usize = 0;
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: usize = 0;
    let mut v___x_418_: u8 = 0;
    let mut v_binderName_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_422_: u8 = 0;
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_430_: u8 = 0;
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: u8 = 0;
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: usize = 0;
    let mut v___x_438_: usize = 0;
    let mut v___x_439_: u8 = 0;
    let mut v___x_440_: usize = 0;
    let mut v___x_441_: usize = 0;
    let mut v___x_442_: u8 = 0;
    let mut v_binderName_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_446_: u8 = 0;
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_454_: u8 = 0;
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: u8 = 0;
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: usize = 0;
    let mut v___x_462_: usize = 0;
    let mut v___x_463_: u8 = 0;
    let mut v___x_464_: usize = 0;
    let mut v___x_465_: usize = 0;
    let mut v___x_466_: u8 = 0;
    let mut v_data_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: usize = 0;
    let mut v___x_473_: usize = 0;
    let mut v___x_474_: u8 = 0;
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_482_: u8 = 0;
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_493_: u8 = 0;
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: usize = 0;
    let mut v___x_497_: usize = 0;
    let mut v___x_498_: u8 = 0;
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: usize = 0;
    let mut v___x_503_: usize = 0;
    let mut v___x_504_: u8 = 0;
    let mut v___x_505_: usize = 0;
    let mut v___x_506_: usize = 0;
    let mut v___x_507_: u8 = 0;
    let mut v_fn_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_517_: u8 = 0;
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: usize = 0;
    let mut v___x_522_: usize = 0;
    let mut v___x_523_: u8 = 0;
    let mut v___x_524_: usize = 0;
    let mut v___x_525_: usize = 0;
    let mut v___x_526_: u8 = 0;
    let mut v_typeName_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: usize = 0;
    let mut v___x_534_: usize = 0;
    let mut v___x_535_: u8 = 0;
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: usize = 0;
    let mut v___x_542_: usize = 0;
    let mut v___x_543_: u8 = 0;
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: u8 = 0;
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_keys_412_ = crate::leanh::lean_ctor_get(v_a_411_, 0);
                v_results_413_ = crate::leanh::lean_ctor_get(v_a_411_, 1);
                v___x_414_ = lean_ptr_addr(v_e_410_);
                v___x_415_ = lean_usize_mod(v___x_414_, v_size_409_);
                v___x_416_ = lean_array_uget_borrowed(v_keys_412_, v___x_415_);
                v___x_417_ = lean_ptr_addr(v___x_416_);
                v___x_418_ = lean_usize_dec_eq(v___x_417_, v___x_414_);
                if v___x_418_ == 0 {
                    match crate::leanh::lean_obj_tag(v_e_410_) {
                        7 => {
                            v_binderName_419_ = crate::leanh::lean_ctor_get(v_e_410_, 0);
                            v_binderType_420_ = crate::leanh::lean_ctor_get(v_e_410_, 1);
                            v_body_421_ = crate::leanh::lean_ctor_get(v_e_410_, 2);
                            v_binderInfo_422_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_410_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_binderType_420_);
                            crate::leanh::lean_inc_ref(v_f_x3f_408_);
                            v___x_423_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_408_, v_size_409_, v_binderType_420_, v_a_411_);
                            v_fst_424_ = crate::leanh::lean_ctor_get(v___x_423_, 0);
                            crate::leanh::lean_inc(v_fst_424_);
                            v_snd_425_ = crate::leanh::lean_ctor_get(v___x_423_, 1);
                            crate::leanh::lean_inc(v_snd_425_);
                            crate::leanh::lean_dec_ref(v___x_423_);
                            crate::leanh::lean_inc_ref(v_body_421_);
                            v___x_426_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_408_, v_size_409_, v_body_421_, v_snd_425_);
                            v_fst_427_ = crate::leanh::lean_ctor_get(v___x_426_, 0);
                            crate::leanh::lean_inc(v_fst_427_);
                            v_snd_428_ = crate::leanh::lean_ctor_get(v___x_426_, 1);
                            crate::leanh::lean_inc(v_snd_428_);
                            crate::leanh::lean_dec_ref(v___x_426_);
                            v___x_437_ = lean_ptr_addr(v_binderType_420_);
                            v___x_438_ = lean_ptr_addr(v_fst_424_);
                            v___x_439_ = lean_usize_dec_eq(v___x_437_, v___x_438_);
                            if v___x_439_ == 0 {
                                v___y_430_ = v___x_439_;
                                state = 1;
                                continue;
                            } else {
                                v___x_440_ = lean_ptr_addr(v_body_421_);
                                v___x_441_ = lean_ptr_addr(v_fst_427_);
                                v___x_442_ = lean_usize_dec_eq(v___x_440_, v___x_441_);
                                v___y_430_ = v___x_442_;
                                state = 1;
                                continue;
                            }
                        }
                        6 => {
                            v_binderName_443_ = crate::leanh::lean_ctor_get(v_e_410_, 0);
                            v_binderType_444_ = crate::leanh::lean_ctor_get(v_e_410_, 1);
                            v_body_445_ = crate::leanh::lean_ctor_get(v_e_410_, 2);
                            v_binderInfo_446_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_410_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_binderType_444_);
                            crate::leanh::lean_inc_ref(v_f_x3f_408_);
                            v___x_447_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_408_, v_size_409_, v_binderType_444_, v_a_411_);
                            v_fst_448_ = crate::leanh::lean_ctor_get(v___x_447_, 0);
                            crate::leanh::lean_inc(v_fst_448_);
                            v_snd_449_ = crate::leanh::lean_ctor_get(v___x_447_, 1);
                            crate::leanh::lean_inc(v_snd_449_);
                            crate::leanh::lean_dec_ref(v___x_447_);
                            crate::leanh::lean_inc_ref(v_body_445_);
                            v___x_450_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_408_, v_size_409_, v_body_445_, v_snd_449_);
                            v_fst_451_ = crate::leanh::lean_ctor_get(v___x_450_, 0);
                            crate::leanh::lean_inc(v_fst_451_);
                            v_snd_452_ = crate::leanh::lean_ctor_get(v___x_450_, 1);
                            crate::leanh::lean_inc(v_snd_452_);
                            crate::leanh::lean_dec_ref(v___x_450_);
                            v___x_461_ = lean_ptr_addr(v_binderType_444_);
                            v___x_462_ = lean_ptr_addr(v_fst_448_);
                            v___x_463_ = lean_usize_dec_eq(v___x_461_, v___x_462_);
                            if v___x_463_ == 0 {
                                v___y_454_ = v___x_463_;
                                state = 2;
                                continue;
                            } else {
                                v___x_464_ = lean_ptr_addr(v_body_445_);
                                v___x_465_ = lean_ptr_addr(v_fst_451_);
                                v___x_466_ = lean_usize_dec_eq(v___x_464_, v___x_465_);
                                v___y_454_ = v___x_466_;
                                state = 2;
                                continue;
                            }
                        }
                        10 => {
                            v_data_467_ = crate::leanh::lean_ctor_get(v_e_410_, 0);
                            v_expr_468_ = crate::leanh::lean_ctor_get(v_e_410_, 1);
                            crate::leanh::lean_inc_ref(v_expr_468_);
                            v___x_469_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_408_, v_size_409_, v_expr_468_, v_a_411_);
                            v_fst_470_ = crate::leanh::lean_ctor_get(v___x_469_, 0);
                            crate::leanh::lean_inc(v_fst_470_);
                            v_snd_471_ = crate::leanh::lean_ctor_get(v___x_469_, 1);
                            crate::leanh::lean_inc(v_snd_471_);
                            crate::leanh::lean_dec_ref(v___x_469_);
                            v___x_472_ = lean_ptr_addr(v_expr_468_);
                            v___x_473_ = lean_ptr_addr(v_fst_470_);
                            v___x_474_ = lean_usize_dec_eq(v___x_472_, v___x_473_);
                            if v___x_474_ == 0 {
                                crate::leanh::lean_inc(v_data_467_);
                                v___x_475_ = l_Lean_Expr_mdata___override(v_data_467_, v_fst_470_);
                                v___x_476_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                                    v___x_415_, v_e_410_, v___x_475_, v_snd_471_,
                                );
                                return v___x_476_;
                            } else {
                                crate::leanh::lean_dec(v_fst_470_);
                                crate::leanh::lean_inc_ref(v_e_410_);
                                v___x_477_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                                    v___x_415_, v_e_410_, v_e_410_, v_snd_471_,
                                );
                                return v___x_477_;
                            }
                        }
                        8 => {
                            v_declName_478_ = crate::leanh::lean_ctor_get(v_e_410_, 0);
                            v_type_479_ = crate::leanh::lean_ctor_get(v_e_410_, 1);
                            v_value_480_ = crate::leanh::lean_ctor_get(v_e_410_, 2);
                            v_body_481_ = crate::leanh::lean_ctor_get(v_e_410_, 3);
                            v_nondep_482_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_410_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_type_479_);
                            crate::leanh::lean_inc_ref_n(v_f_x3f_408_, 2);
                            v___x_483_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_408_, v_size_409_, v_type_479_, v_a_411_);
                            v_fst_484_ = crate::leanh::lean_ctor_get(v___x_483_, 0);
                            crate::leanh::lean_inc(v_fst_484_);
                            v_snd_485_ = crate::leanh::lean_ctor_get(v___x_483_, 1);
                            crate::leanh::lean_inc(v_snd_485_);
                            crate::leanh::lean_dec_ref(v___x_483_);
                            crate::leanh::lean_inc_ref(v_value_480_);
                            v___x_486_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_408_, v_size_409_, v_value_480_, v_snd_485_);
                            v_fst_487_ = crate::leanh::lean_ctor_get(v___x_486_, 0);
                            crate::leanh::lean_inc(v_fst_487_);
                            v_snd_488_ = crate::leanh::lean_ctor_get(v___x_486_, 1);
                            crate::leanh::lean_inc(v_snd_488_);
                            crate::leanh::lean_dec_ref(v___x_486_);
                            crate::leanh::lean_inc_ref(v_body_481_);
                            v___x_489_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_408_, v_size_409_, v_body_481_, v_snd_488_);
                            v_fst_490_ = crate::leanh::lean_ctor_get(v___x_489_, 0);
                            crate::leanh::lean_inc(v_fst_490_);
                            v_snd_491_ = crate::leanh::lean_ctor_get(v___x_489_, 1);
                            crate::leanh::lean_inc(v_snd_491_);
                            crate::leanh::lean_dec_ref(v___x_489_);
                            v___x_502_ = lean_ptr_addr(v_type_479_);
                            v___x_503_ = lean_ptr_addr(v_fst_484_);
                            v___x_504_ = lean_usize_dec_eq(v___x_502_, v___x_503_);
                            if v___x_504_ == 0 {
                                v___y_493_ = v___x_504_;
                                state = 3;
                                continue;
                            } else {
                                v___x_505_ = lean_ptr_addr(v_value_480_);
                                v___x_506_ = lean_ptr_addr(v_fst_487_);
                                v___x_507_ = lean_usize_dec_eq(v___x_505_, v___x_506_);
                                v___y_493_ = v___x_507_;
                                state = 3;
                                continue;
                            }
                        }
                        5 => {
                            v_fn_508_ = crate::leanh::lean_ctor_get(v_e_410_, 0);
                            v_arg_509_ = crate::leanh::lean_ctor_get(v_e_410_, 1);
                            crate::leanh::lean_inc_ref(v_fn_508_);
                            crate::leanh::lean_inc_ref(v_f_x3f_408_);
                            v___x_510_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_408_, v_size_409_, v_fn_508_, v_a_411_);
                            v_fst_511_ = crate::leanh::lean_ctor_get(v___x_510_, 0);
                            crate::leanh::lean_inc(v_fst_511_);
                            v_snd_512_ = crate::leanh::lean_ctor_get(v___x_510_, 1);
                            crate::leanh::lean_inc(v_snd_512_);
                            crate::leanh::lean_dec_ref(v___x_510_);
                            crate::leanh::lean_inc_ref(v_arg_509_);
                            v___x_513_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_408_, v_size_409_, v_arg_509_, v_snd_512_);
                            v_fst_514_ = crate::leanh::lean_ctor_get(v___x_513_, 0);
                            crate::leanh::lean_inc(v_fst_514_);
                            v_snd_515_ = crate::leanh::lean_ctor_get(v___x_513_, 1);
                            crate::leanh::lean_inc(v_snd_515_);
                            crate::leanh::lean_dec_ref(v___x_513_);
                            v___x_521_ = lean_ptr_addr(v_fn_508_);
                            v___x_522_ = lean_ptr_addr(v_fst_511_);
                            v___x_523_ = lean_usize_dec_eq(v___x_521_, v___x_522_);
                            if v___x_523_ == 0 {
                                v___y_517_ = v___x_523_;
                                state = 4;
                                continue;
                            } else {
                                v___x_524_ = lean_ptr_addr(v_arg_509_);
                                v___x_525_ = lean_ptr_addr(v_fst_514_);
                                v___x_526_ = lean_usize_dec_eq(v___x_524_, v___x_525_);
                                v___y_517_ = v___x_526_;
                                state = 4;
                                continue;
                            }
                        }
                        11 => {
                            v_typeName_527_ = crate::leanh::lean_ctor_get(v_e_410_, 0);
                            v_idx_528_ = crate::leanh::lean_ctor_get(v_e_410_, 1);
                            v_struct_529_ = crate::leanh::lean_ctor_get(v_e_410_, 2);
                            crate::leanh::lean_inc_ref(v_struct_529_);
                            v___x_530_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(v_f_x3f_408_, v_size_409_, v_struct_529_, v_a_411_);
                            v_fst_531_ = crate::leanh::lean_ctor_get(v___x_530_, 0);
                            crate::leanh::lean_inc(v_fst_531_);
                            v_snd_532_ = crate::leanh::lean_ctor_get(v___x_530_, 1);
                            crate::leanh::lean_inc(v_snd_532_);
                            crate::leanh::lean_dec_ref(v___x_530_);
                            v___x_533_ = lean_ptr_addr(v_struct_529_);
                            v___x_534_ = lean_ptr_addr(v_fst_531_);
                            v___x_535_ = lean_usize_dec_eq(v___x_533_, v___x_534_);
                            if v___x_535_ == 0 {
                                crate::leanh::lean_inc(v_idx_528_);
                                crate::leanh::lean_inc(v_typeName_527_);
                                v___x_536_ = l_Lean_Expr_proj___override(
                                    v_typeName_527_,
                                    v_idx_528_,
                                    v_fst_531_,
                                );
                                v___x_537_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                                    v___x_415_, v_e_410_, v___x_536_, v_snd_532_,
                                );
                                return v___x_537_;
                            } else {
                                crate::leanh::lean_dec(v_fst_531_);
                                crate::leanh::lean_inc_ref(v_e_410_);
                                v___x_538_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                                    v___x_415_, v_e_410_, v_e_410_, v_snd_532_,
                                );
                                return v___x_538_;
                            }
                        }
                        3 => {
                            v_u_539_ = crate::leanh::lean_ctor_get(v_e_410_, 0);
                            crate::leanh::lean_inc(v_u_539_);
                            v___x_540_ = l_Lean_Level_replace(v_f_x3f_408_, v_u_539_);
                            v___x_541_ = lean_ptr_addr(v_u_539_);
                            v___x_542_ = lean_ptr_addr(v___x_540_);
                            v___x_543_ = lean_usize_dec_eq(v___x_541_, v___x_542_);
                            if v___x_543_ == 0 {
                                v___x_544_ = l_Lean_Expr_sort___override(v___x_540_);
                                v___x_545_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                                    v___x_415_, v_e_410_, v___x_544_, v_a_411_,
                                );
                                return v___x_545_;
                            } else {
                                crate::leanh::lean_dec(v___x_540_);
                                crate::leanh::lean_inc_ref(v_e_410_);
                                v___x_546_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                                    v___x_415_, v_e_410_, v_e_410_, v_a_411_,
                                );
                                return v___x_546_;
                            }
                        }
                        4 => {
                            v_declName_547_ = crate::leanh::lean_ctor_get(v_e_410_, 0);
                            v_us_548_ = crate::leanh::lean_ctor_get(v_e_410_, 1);
                            v___x_549_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v_us_548_);
                            v___x_550_ = l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(v_f_x3f_408_, v_us_548_, v___x_549_);
                            v___x_551_ = l_ptrEqList___redArg(v_us_548_, v___x_550_);
                            if v___x_551_ == 0 {
                                crate::leanh::lean_inc(v_declName_547_);
                                v___x_552_ =
                                    l_Lean_Expr_const___override(v_declName_547_, v___x_550_);
                                v___x_553_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                                    v___x_415_, v_e_410_, v___x_552_, v_a_411_,
                                );
                                return v___x_553_;
                            } else {
                                crate::leanh::lean_dec(v___x_550_);
                                crate::leanh::lean_inc_ref(v_e_410_);
                                v___x_554_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                                    v___x_415_, v_e_410_, v_e_410_, v_a_411_,
                                );
                                return v___x_554_;
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_f_x3f_408_);
                            v___x_555_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_555_, 0, v_e_410_);
                            crate::leanh::lean_ctor_set(v___x_555_, 1, v_a_411_);
                            return v___x_555_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_410_);
                    crate::leanh::lean_dec_ref(v_f_x3f_408_);
                    v___x_556_ = lean_array_uget(v_results_413_, v___x_415_);
                    v___x_557_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_557_, 0, v___x_556_);
                    crate::leanh::lean_ctor_set(v___x_557_, 1, v_a_411_);
                    return v___x_557_;
                }
            }
            1 => {
                if v___y_430_ == 0 {
                    crate::leanh::lean_inc(v_binderName_419_);
                    v___x_431_ = l_Lean_Expr_forallE___override(
                        v_binderName_419_,
                        v_fst_424_,
                        v_fst_427_,
                        v_binderInfo_422_,
                    );
                    v___x_432_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                        v___x_415_, v_e_410_, v___x_431_, v_snd_428_,
                    );
                    return v___x_432_;
                } else {
                    v___x_433_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_422_, v_binderInfo_422_);
                    if v___x_433_ == 0 {
                        crate::leanh::lean_inc(v_binderName_419_);
                        v___x_434_ = l_Lean_Expr_forallE___override(
                            v_binderName_419_,
                            v_fst_424_,
                            v_fst_427_,
                            v_binderInfo_422_,
                        );
                        v___x_435_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                            v___x_415_, v_e_410_, v___x_434_, v_snd_428_,
                        );
                        return v___x_435_;
                    } else {
                        crate::leanh::lean_dec(v_fst_427_);
                        crate::leanh::lean_dec(v_fst_424_);
                        crate::leanh::lean_inc_ref(v_e_410_);
                        v___x_436_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                            v___x_415_, v_e_410_, v_e_410_, v_snd_428_,
                        );
                        return v___x_436_;
                    }
                }
            }
            2 => {
                if v___y_454_ == 0 {
                    crate::leanh::lean_inc(v_binderName_443_);
                    v___x_455_ = l_Lean_Expr_lam___override(
                        v_binderName_443_,
                        v_fst_448_,
                        v_fst_451_,
                        v_binderInfo_446_,
                    );
                    v___x_456_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                        v___x_415_, v_e_410_, v___x_455_, v_snd_452_,
                    );
                    return v___x_456_;
                } else {
                    v___x_457_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_446_, v_binderInfo_446_);
                    if v___x_457_ == 0 {
                        crate::leanh::lean_inc(v_binderName_443_);
                        v___x_458_ = l_Lean_Expr_lam___override(
                            v_binderName_443_,
                            v_fst_448_,
                            v_fst_451_,
                            v_binderInfo_446_,
                        );
                        v___x_459_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                            v___x_415_, v_e_410_, v___x_458_, v_snd_452_,
                        );
                        return v___x_459_;
                    } else {
                        crate::leanh::lean_dec(v_fst_451_);
                        crate::leanh::lean_dec(v_fst_448_);
                        crate::leanh::lean_inc_ref(v_e_410_);
                        v___x_460_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                            v___x_415_, v_e_410_, v_e_410_, v_snd_452_,
                        );
                        return v___x_460_;
                    }
                }
            }
            3 => {
                if v___y_493_ == 0 {
                    crate::leanh::lean_inc(v_declName_478_);
                    v___x_494_ = l_Lean_Expr_letE___override(
                        v_declName_478_,
                        v_fst_484_,
                        v_fst_487_,
                        v_fst_490_,
                        v_nondep_482_,
                    );
                    v___x_495_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                        v___x_415_, v_e_410_, v___x_494_, v_snd_491_,
                    );
                    return v___x_495_;
                } else {
                    v___x_496_ = lean_ptr_addr(v_body_481_);
                    v___x_497_ = lean_ptr_addr(v_fst_490_);
                    v___x_498_ = lean_usize_dec_eq(v___x_496_, v___x_497_);
                    if v___x_498_ == 0 {
                        crate::leanh::lean_inc(v_declName_478_);
                        v___x_499_ = l_Lean_Expr_letE___override(
                            v_declName_478_,
                            v_fst_484_,
                            v_fst_487_,
                            v_fst_490_,
                            v_nondep_482_,
                        );
                        v___x_500_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                            v___x_415_, v_e_410_, v___x_499_, v_snd_491_,
                        );
                        return v___x_500_;
                    } else {
                        crate::leanh::lean_dec(v_fst_490_);
                        crate::leanh::lean_dec(v_fst_487_);
                        crate::leanh::lean_dec(v_fst_484_);
                        crate::leanh::lean_inc_ref(v_e_410_);
                        v___x_501_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                            v___x_415_, v_e_410_, v_e_410_, v_snd_491_,
                        );
                        return v___x_501_;
                    }
                }
            }
            4 => {
                if v___y_517_ == 0 {
                    v___x_518_ = l_Lean_Expr_app___override(v_fst_511_, v_fst_514_);
                    v___x_519_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                        v___x_415_, v_e_410_, v___x_518_, v_snd_515_,
                    );
                    return v___x_519_;
                } else {
                    crate::leanh::lean_dec(v_fst_514_);
                    crate::leanh::lean_dec(v_fst_511_);
                    crate::leanh::lean_inc_ref(v_e_410_);
                    v___x_520_ = l_Lean_Expr_ReplaceLevelImpl_cache(
                        v___x_415_, v_e_410_, v_e_410_, v_snd_515_,
                    );
                    return v___x_520_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(
    mut v_f_x3f_558_: *mut crate::leanh::LeanObject,
    mut v_size_559_: *mut crate::leanh::LeanObject,
    mut v_e_560_: *mut crate::leanh::LeanObject,
    mut v_a_561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_562_: usize = 0;
    let mut v_res_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_562_ = crate::leanh::lean_unbox_usize(v_size_559_);
    crate::leanh::lean_dec(v_size_559_);
    v_res_563_ =
        l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(
            v_f_x3f_558_,
            v_size_boxed_562_,
            v_e_560_,
            v_a_561_,
        );
    return v_res_563_;
}
pub unsafe fn l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(
    mut v_f_x3f_564_: *mut crate::leanh::LeanObject,
    mut v_size_565_: usize,
    mut v_e_566_: *mut crate::leanh::LeanObject,
    mut v_a_567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_568_ =
        l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(
            v_f_x3f_564_,
            v_size_565_,
            v_e_566_,
            v_a_567_,
        );
    return v___x_568_;
}
pub unsafe fn l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(
    mut v_f_x3f_569_: *mut crate::leanh::LeanObject,
    mut v_size_570_: *mut crate::leanh::LeanObject,
    mut v_e_571_: *mut crate::leanh::LeanObject,
    mut v_a_572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_573_: usize = 0;
    let mut v_res_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_573_ = crate::leanh::lean_unbox_usize(v_size_570_);
    crate::leanh::lean_dec(v_size_570_);
    v_res_574_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(
        v_f_x3f_569_,
        v_size_boxed_573_,
        v_e_571_,
        v_a_572_,
    );
    return v_res_574_;
}
pub unsafe fn _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_578_: usize = 0;
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_578_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0_once),
        _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0,
    );
    v___x_579_ = lean_usize_to_nat(v___x_578_);
    return v___x_579_;
}
pub unsafe fn _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_580_ = l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_notAnExpr;
    v___x_581_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0_once),
        _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0,
    );
    v___x_582_ = lean_mk_array(v___x_581_, v___x_580_);
    return v___x_582_;
}
pub unsafe fn _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_586_ = crate::leanh::lean_box(0);
    v___x_587_ = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
    v___x_588_ = l_Lean_Expr_const___override(v___x_587_, v___x_586_);
    return v___x_588_;
}
pub unsafe fn _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_589_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4_once),
        _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__4,
    );
    v___x_590_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0_once),
        _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__0,
    );
    v___x_591_ = lean_mk_array(v___x_590_, v___x_589_);
    return v___x_591_;
}
pub unsafe fn _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_592_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5_once),
        _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__5,
    );
    v___x_593_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1_once),
        _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1,
    );
    v___x_594_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_594_, 0, v___x_593_);
    crate::leanh::lean_ctor_set(v___x_594_, 1, v___x_592_);
    return v___x_594_;
}
pub unsafe fn _init_l_Lean_Expr_ReplaceLevelImpl_initCache() -> *mut crate::leanh::LeanObject {
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_595_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6_once),
        _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__6,
    );
    return v___x_595_;
}
pub unsafe fn l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(
    mut v_f_x3f_596_: *mut crate::leanh::LeanObject,
    mut v_e_597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_598_: usize = 0;
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_598_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0_once),
        _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize___closed__0,
    );
    v___x_599_ = l_Lean_Expr_ReplaceLevelImpl_initCache;
    v___x_600_ =
        l___private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(
            v_f_x3f_596_,
            v___x_598_,
            v_e_597_,
            v___x_599_,
        );
    v_fst_601_ = crate::leanh::lean_ctor_get(v___x_600_, 0);
    crate::leanh::lean_inc(v_fst_601_);
    crate::leanh::lean_dec_ref(v___x_600_);
    return v_fst_601_;
}
pub unsafe fn l_Lean_Expr_replaceLevel(
    mut v_f_x3f_602_: *mut crate::leanh::LeanObject,
    mut v_x_603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderName_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_607_: u8 = 0;
    let mut v_d_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_611_: u8 = 0;
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: u8 = 0;
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: usize = 0;
    let mut v___x_616_: usize = 0;
    let mut v___x_617_: u8 = 0;
    let mut v___x_618_: usize = 0;
    let mut v___x_619_: usize = 0;
    let mut v___x_620_: u8 = 0;
    let mut v_binderName_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_624_: u8 = 0;
    let mut v_d_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_628_: u8 = 0;
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: usize = 0;
    let mut v___x_633_: usize = 0;
    let mut v___x_634_: u8 = 0;
    let mut v___x_635_: usize = 0;
    let mut v___x_636_: usize = 0;
    let mut v___x_637_: u8 = 0;
    let mut v_data_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: usize = 0;
    let mut v___x_642_: usize = 0;
    let mut v___x_643_: u8 = 0;
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_649_: u8 = 0;
    let mut v_t_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_654_: u8 = 0;
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: usize = 0;
    let mut v___x_657_: usize = 0;
    let mut v___x_658_: u8 = 0;
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: usize = 0;
    let mut v___x_661_: usize = 0;
    let mut v___x_662_: u8 = 0;
    let mut v___x_663_: usize = 0;
    let mut v___x_664_: usize = 0;
    let mut v___x_665_: u8 = 0;
    let mut v_fn_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_671_: u8 = 0;
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: usize = 0;
    let mut v___x_674_: usize = 0;
    let mut v___x_675_: u8 = 0;
    let mut v___x_676_: usize = 0;
    let mut v___x_677_: usize = 0;
    let mut v___x_678_: u8 = 0;
    let mut v_typeName_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: usize = 0;
    let mut v___x_684_: usize = 0;
    let mut v___x_685_: u8 = 0;
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: usize = 0;
    let mut v___x_690_: usize = 0;
    let mut v___x_691_: u8 = 0;
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: u8 = 0;
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_603_) {
                7 => {
                    v_binderName_604_ = crate::leanh::lean_ctor_get(v_x_603_, 0);
                    v_binderType_605_ = crate::leanh::lean_ctor_get(v_x_603_, 1);
                    v_body_606_ = crate::leanh::lean_ctor_get(v_x_603_, 2);
                    v_binderInfo_607_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_603_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_605_);
                    crate::leanh::lean_inc_ref(v_f_x3f_602_);
                    v_d_608_ =
                        l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_602_, v_binderType_605_);
                    crate::leanh::lean_inc_ref(v_body_606_);
                    v_b_609_ =
                        l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_602_, v_body_606_);
                    v___x_615_ = lean_ptr_addr(v_binderType_605_);
                    v___x_616_ = lean_ptr_addr(v_d_608_);
                    v___x_617_ = lean_usize_dec_eq(v___x_615_, v___x_616_);
                    if v___x_617_ == 0 {
                        v___y_611_ = v___x_617_;
                        state = 1;
                        continue;
                    } else {
                        v___x_618_ = lean_ptr_addr(v_body_606_);
                        v___x_619_ = lean_ptr_addr(v_b_609_);
                        v___x_620_ = lean_usize_dec_eq(v___x_618_, v___x_619_);
                        v___y_611_ = v___x_620_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v_binderName_621_ = crate::leanh::lean_ctor_get(v_x_603_, 0);
                    v_binderType_622_ = crate::leanh::lean_ctor_get(v_x_603_, 1);
                    v_body_623_ = crate::leanh::lean_ctor_get(v_x_603_, 2);
                    v_binderInfo_624_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_603_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_622_);
                    crate::leanh::lean_inc_ref(v_f_x3f_602_);
                    v_d_625_ =
                        l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_602_, v_binderType_622_);
                    crate::leanh::lean_inc_ref(v_body_623_);
                    v_b_626_ =
                        l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_602_, v_body_623_);
                    v___x_632_ = lean_ptr_addr(v_binderType_622_);
                    v___x_633_ = lean_ptr_addr(v_d_625_);
                    v___x_634_ = lean_usize_dec_eq(v___x_632_, v___x_633_);
                    if v___x_634_ == 0 {
                        v___y_628_ = v___x_634_;
                        state = 2;
                        continue;
                    } else {
                        v___x_635_ = lean_ptr_addr(v_body_623_);
                        v___x_636_ = lean_ptr_addr(v_b_626_);
                        v___x_637_ = lean_usize_dec_eq(v___x_635_, v___x_636_);
                        v___y_628_ = v___x_637_;
                        state = 2;
                        continue;
                    }
                }
                10 => {
                    v_data_638_ = crate::leanh::lean_ctor_get(v_x_603_, 0);
                    v_expr_639_ = crate::leanh::lean_ctor_get(v_x_603_, 1);
                    crate::leanh::lean_inc_ref(v_expr_639_);
                    v_b_640_ =
                        l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_602_, v_expr_639_);
                    v___x_641_ = lean_ptr_addr(v_expr_639_);
                    v___x_642_ = lean_ptr_addr(v_b_640_);
                    v___x_643_ = lean_usize_dec_eq(v___x_641_, v___x_642_);
                    if v___x_643_ == 0 {
                        crate::leanh::lean_inc(v_data_638_);
                        crate::leanh::lean_dec_ref_known(v_x_603_, 2);
                        v___x_644_ = l_Lean_Expr_mdata___override(v_data_638_, v_b_640_);
                        return v___x_644_;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_640_);
                        return v_x_603_;
                    }
                }
                8 => {
                    v_declName_645_ = crate::leanh::lean_ctor_get(v_x_603_, 0);
                    v_type_646_ = crate::leanh::lean_ctor_get(v_x_603_, 1);
                    v_value_647_ = crate::leanh::lean_ctor_get(v_x_603_, 2);
                    v_body_648_ = crate::leanh::lean_ctor_get(v_x_603_, 3);
                    v_nondep_649_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_603_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_type_646_);
                    crate::leanh::lean_inc_ref_n(v_f_x3f_602_, 2);
                    v_t_650_ =
                        l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_602_, v_type_646_);
                    crate::leanh::lean_inc_ref(v_value_647_);
                    v_v_651_ =
                        l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_602_, v_value_647_);
                    crate::leanh::lean_inc_ref(v_body_648_);
                    v_b_652_ =
                        l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_602_, v_body_648_);
                    v___x_660_ = lean_ptr_addr(v_type_646_);
                    v___x_661_ = lean_ptr_addr(v_t_650_);
                    v___x_662_ = lean_usize_dec_eq(v___x_660_, v___x_661_);
                    if v___x_662_ == 0 {
                        v___y_654_ = v___x_662_;
                        state = 3;
                        continue;
                    } else {
                        v___x_663_ = lean_ptr_addr(v_value_647_);
                        v___x_664_ = lean_ptr_addr(v_v_651_);
                        v___x_665_ = lean_usize_dec_eq(v___x_663_, v___x_664_);
                        v___y_654_ = v___x_665_;
                        state = 3;
                        continue;
                    }
                }
                5 => {
                    v_fn_666_ = crate::leanh::lean_ctor_get(v_x_603_, 0);
                    v_arg_667_ = crate::leanh::lean_ctor_get(v_x_603_, 1);
                    crate::leanh::lean_inc_ref(v_fn_666_);
                    crate::leanh::lean_inc_ref(v_f_x3f_602_);
                    v_f_668_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_602_, v_fn_666_);
                    crate::leanh::lean_inc_ref(v_arg_667_);
                    v_a_669_ = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_602_, v_arg_667_);
                    v___x_673_ = lean_ptr_addr(v_fn_666_);
                    v___x_674_ = lean_ptr_addr(v_f_668_);
                    v___x_675_ = lean_usize_dec_eq(v___x_673_, v___x_674_);
                    if v___x_675_ == 0 {
                        v___y_671_ = v___x_675_;
                        state = 4;
                        continue;
                    } else {
                        v___x_676_ = lean_ptr_addr(v_arg_667_);
                        v___x_677_ = lean_ptr_addr(v_a_669_);
                        v___x_678_ = lean_usize_dec_eq(v___x_676_, v___x_677_);
                        v___y_671_ = v___x_678_;
                        state = 4;
                        continue;
                    }
                }
                11 => {
                    v_typeName_679_ = crate::leanh::lean_ctor_get(v_x_603_, 0);
                    v_idx_680_ = crate::leanh::lean_ctor_get(v_x_603_, 1);
                    v_struct_681_ = crate::leanh::lean_ctor_get(v_x_603_, 2);
                    crate::leanh::lean_inc_ref(v_struct_681_);
                    v_b_682_ =
                        l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(v_f_x3f_602_, v_struct_681_);
                    v___x_683_ = lean_ptr_addr(v_struct_681_);
                    v___x_684_ = lean_ptr_addr(v_b_682_);
                    v___x_685_ = lean_usize_dec_eq(v___x_683_, v___x_684_);
                    if v___x_685_ == 0 {
                        crate::leanh::lean_inc(v_idx_680_);
                        crate::leanh::lean_inc(v_typeName_679_);
                        crate::leanh::lean_dec_ref_known(v_x_603_, 3);
                        v___x_686_ =
                            l_Lean_Expr_proj___override(v_typeName_679_, v_idx_680_, v_b_682_);
                        return v___x_686_;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_682_);
                        return v_x_603_;
                    }
                }
                3 => {
                    v_u_687_ = crate::leanh::lean_ctor_get(v_x_603_, 0);
                    crate::leanh::lean_inc(v_u_687_);
                    v___x_688_ = l_Lean_Level_replace(v_f_x3f_602_, v_u_687_);
                    v___x_689_ = lean_ptr_addr(v_u_687_);
                    v___x_690_ = lean_ptr_addr(v___x_688_);
                    v___x_691_ = lean_usize_dec_eq(v___x_689_, v___x_690_);
                    if v___x_691_ == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_603_, 1);
                        v___x_692_ = l_Lean_Expr_sort___override(v___x_688_);
                        return v___x_692_;
                    } else {
                        crate::leanh::lean_dec(v___x_688_);
                        return v_x_603_;
                    }
                }
                4 => {
                    v_declName_693_ = crate::leanh::lean_ctor_get(v_x_603_, 0);
                    v_us_694_ = crate::leanh::lean_ctor_get(v_x_603_, 1);
                    v___x_695_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_us_694_);
                    v___x_696_ = l_List_mapTR_loop___at___00__private_Lean_Util_ReplaceLevel_0__Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(v_f_x3f_602_, v_us_694_, v___x_695_);
                    v___x_697_ = l_ptrEqList___redArg(v_us_694_, v___x_696_);
                    if v___x_697_ == 0 {
                        crate::leanh::lean_inc(v_declName_693_);
                        crate::leanh::lean_dec_ref_known(v_x_603_, 2);
                        v___x_698_ = l_Lean_Expr_const___override(v_declName_693_, v___x_696_);
                        return v___x_698_;
                    } else {
                        crate::leanh::lean_dec(v___x_696_);
                        return v_x_603_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_f_x3f_602_);
                    return v_x_603_;
                }
            },
            1 => {
                if v___y_611_ == 0 {
                    crate::leanh::lean_inc(v_binderName_604_);
                    crate::leanh::lean_dec_ref_known(v_x_603_, 3);
                    v___x_612_ = l_Lean_Expr_forallE___override(
                        v_binderName_604_,
                        v_d_608_,
                        v_b_609_,
                        v_binderInfo_607_,
                    );
                    return v___x_612_;
                } else {
                    v___x_613_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_607_, v_binderInfo_607_);
                    if v___x_613_ == 0 {
                        crate::leanh::lean_inc(v_binderName_604_);
                        crate::leanh::lean_dec_ref_known(v_x_603_, 3);
                        v___x_614_ = l_Lean_Expr_forallE___override(
                            v_binderName_604_,
                            v_d_608_,
                            v_b_609_,
                            v_binderInfo_607_,
                        );
                        return v___x_614_;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_609_);
                        crate::leanh::lean_dec_ref(v_d_608_);
                        return v_x_603_;
                    }
                }
            }
            2 => {
                if v___y_628_ == 0 {
                    crate::leanh::lean_inc(v_binderName_621_);
                    crate::leanh::lean_dec_ref_known(v_x_603_, 3);
                    v___x_629_ = l_Lean_Expr_lam___override(
                        v_binderName_621_,
                        v_d_625_,
                        v_b_626_,
                        v_binderInfo_624_,
                    );
                    return v___x_629_;
                } else {
                    v___x_630_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_624_, v_binderInfo_624_);
                    if v___x_630_ == 0 {
                        crate::leanh::lean_inc(v_binderName_621_);
                        crate::leanh::lean_dec_ref_known(v_x_603_, 3);
                        v___x_631_ = l_Lean_Expr_lam___override(
                            v_binderName_621_,
                            v_d_625_,
                            v_b_626_,
                            v_binderInfo_624_,
                        );
                        return v___x_631_;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_626_);
                        crate::leanh::lean_dec_ref(v_d_625_);
                        return v_x_603_;
                    }
                }
            }
            3 => {
                if v___y_654_ == 0 {
                    crate::leanh::lean_inc(v_declName_645_);
                    crate::leanh::lean_dec_ref_known(v_x_603_, 4);
                    v___x_655_ = l_Lean_Expr_letE___override(
                        v_declName_645_,
                        v_t_650_,
                        v_v_651_,
                        v_b_652_,
                        v_nondep_649_,
                    );
                    return v___x_655_;
                } else {
                    v___x_656_ = lean_ptr_addr(v_body_648_);
                    v___x_657_ = lean_ptr_addr(v_b_652_);
                    v___x_658_ = lean_usize_dec_eq(v___x_656_, v___x_657_);
                    if v___x_658_ == 0 {
                        crate::leanh::lean_inc(v_declName_645_);
                        crate::leanh::lean_dec_ref_known(v_x_603_, 4);
                        v___x_659_ = l_Lean_Expr_letE___override(
                            v_declName_645_,
                            v_t_650_,
                            v_v_651_,
                            v_b_652_,
                            v_nondep_649_,
                        );
                        return v___x_659_;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_652_);
                        crate::leanh::lean_dec_ref(v_v_651_);
                        crate::leanh::lean_dec_ref(v_t_650_);
                        return v_x_603_;
                    }
                }
            }
            4 => {
                if v___y_671_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_x_603_, 2);
                    v___x_672_ = l_Lean_Expr_app___override(v_f_668_, v_a_669_);
                    return v___x_672_;
                } else {
                    crate::leanh::lean_dec_ref(v_a_669_);
                    crate::leanh::lean_dec_ref(v_f_668_);
                    return v_x_603_;
                }
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_ReplaceLevel(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Expr_ReplaceLevelImpl_cacheSize = _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize();
    l_Lean_Expr_ReplaceLevelImpl_initCache = _init_l_Lean_Expr_ReplaceLevelImpl_initCache();
    crate::leanh::lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_ReplaceLevel(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_ReplaceLevel(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ReplaceLevel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_ReplaceLevel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_ReplaceLevel(builtin);
}
