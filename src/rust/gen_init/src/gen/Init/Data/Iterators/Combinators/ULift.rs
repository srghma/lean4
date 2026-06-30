// Lean compiler output
// Module: Init.Data.Iterators.Combinators.ULift
// Imports: Init.Data.Iterators.Combinators.Monadic.ULift
use crate::r#gen::Init::Data::Iterators::Combinators::Monadic::ULift::{
    initialize_Init_Data_Iterators_Combinators_Monadic_ULift,
    runtime_initialize_Init_Data_Iterators_Combinators_Monadic_ULift,
};
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_modifyStep___redArg(
    mut v_step_51_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_52_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_53_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_55_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_56_: u8 = 0;
    let mut v___x_58_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_60_: u8 = 0;
    let mut v_it_61_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_64_: u8 = 0;
    let mut v___x_66_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_67_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_68_: u8 = 0;
    let mut v___x_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_step_51_) {
                0 => {
                    v_it_52_ = leanh::lean_ctor_get(v_step_51_, 0);
                    v_out_53_ = leanh::lean_ctor_get(v_step_51_, 1);
                    v_isSharedCheck_60_ = (!leanh::lean_is_exclusive(v_step_51_)) as u8;
                    if v_isSharedCheck_60_ == 0 {
                        v___x_55_ = v_step_51_;
                        v_isShared_56_ = v_isSharedCheck_60_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_out_53_);
                        leanh::lean_inc(v_it_52_);
                        leanh::lean_dec(v_step_51_);
                        v___x_55_ = leanh::lean_box(0);
                        v_isShared_56_ = v_isSharedCheck_60_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_61_ = leanh::lean_ctor_get(v_step_51_, 0);
                    v_isSharedCheck_68_ = (!leanh::lean_is_exclusive(v_step_51_)) as u8;
                    if v_isSharedCheck_68_ == 0 {
                        v___x_63_ = v_step_51_;
                        v_isShared_64_ = v_isSharedCheck_68_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_61_);
                        leanh::lean_dec(v_step_51_);
                        v___x_63_ = leanh::lean_box(0);
                        v_isShared_64_ = v_isSharedCheck_68_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_69_ = leanh::lean_box(2);
                    return v___x_69_;
                }
            },
            1 => {
                if v_isShared_56_ == 0 {
                    v___x_58_ = v___x_55_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_59_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_59_, 0, v_it_52_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_59_, 1, v_out_53_);
                    v___x_58_ = v_reuseFailAlloc_59_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_58_;
            }
            3 => {
                if v_isShared_64_ == 0 {
                    v___x_66_ = v___x_63_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_67_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_67_, 0, v_it_61_);
                    v___x_66_ = v_reuseFailAlloc_67_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_66_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_modifyStep(
    mut v_00_u03b1_70_: *mut leanh::LeanObject,
    mut v_00_u03b2_71_: *mut leanh::LeanObject,
    mut v_step_72_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_73_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_74_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_76_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_77_: u8 = 0;
    let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_80_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_81_: u8 = 0;
    let mut v_it_82_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_84_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_85_: u8 = 0;
    let mut v___x_87_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_88_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_89_: u8 = 0;
    let mut v___x_90_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_step_72_) {
                0 => {
                    v_it_73_ = leanh::lean_ctor_get(v_step_72_, 0);
                    v_out_74_ = leanh::lean_ctor_get(v_step_72_, 1);
                    v_isSharedCheck_81_ = (!leanh::lean_is_exclusive(v_step_72_)) as u8;
                    if v_isSharedCheck_81_ == 0 {
                        v___x_76_ = v_step_72_;
                        v_isShared_77_ = v_isSharedCheck_81_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_out_74_);
                        leanh::lean_inc(v_it_73_);
                        leanh::lean_dec(v_step_72_);
                        v___x_76_ = leanh::lean_box(0);
                        v_isShared_77_ = v_isSharedCheck_81_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_82_ = leanh::lean_ctor_get(v_step_72_, 0);
                    v_isSharedCheck_89_ = (!leanh::lean_is_exclusive(v_step_72_)) as u8;
                    if v_isSharedCheck_89_ == 0 {
                        v___x_84_ = v_step_72_;
                        v_isShared_85_ = v_isSharedCheck_89_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_82_);
                        leanh::lean_dec(v_step_72_);
                        v___x_84_ = leanh::lean_box(0);
                        v_isShared_85_ = v_isSharedCheck_89_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_90_ = leanh::lean_box(2);
                    return v___x_90_;
                }
            },
            1 => {
                if v_isShared_77_ == 0 {
                    v___x_79_ = v___x_76_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_80_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_80_, 0, v_it_73_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_80_, 1, v_out_74_);
                    v___x_79_ = v_reuseFailAlloc_80_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_79_;
            }
            3 => {
                if v_isShared_85_ == 0 {
                    v___x_87_ = v___x_84_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_88_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_88_, 0, v_it_82_);
                    v___x_87_ = v_reuseFailAlloc_88_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_87_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iter_uLift___redArg(
    mut v_it_91_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_91_);
    return v_it_91_;
}
pub unsafe fn l_Std_Iter_uLift___redArg___boxed(
    mut v_it_92_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_93_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_93_ = l_Std_Iter_uLift___redArg(v_it_92_);
    leanh::lean_dec(v_it_92_);
    return v_res_93_;
}
pub unsafe fn l_Std_Iter_uLift(
    mut v_00_u03b1_94_: *mut leanh::LeanObject,
    mut v_00_u03b2_95_: *mut leanh::LeanObject,
    mut v_it_96_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_96_);
    return v_it_96_;
}
pub unsafe fn l_Std_Iter_uLift___boxed(
    mut v_00_u03b1_97_: *mut leanh::LeanObject,
    mut v_00_u03b2_98_: *mut leanh::LeanObject,
    mut v_it_99_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_100_ = l_Std_Iter_uLift(v_00_u03b1_97_, v_00_u03b2_98_, v_it_99_);
    leanh::lean_dec(v_it_99_);
    return v_res_100_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_ULift(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_ULift(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Combinators_ULift(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_ULift(builtin);
}