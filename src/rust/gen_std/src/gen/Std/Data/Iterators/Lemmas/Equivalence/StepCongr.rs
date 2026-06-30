// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Equivalence.StepCongr
// Imports: Std.Data.Iterators.Lemmas.Equivalence.Basic
use crate::r#gen::Std::Data::Iterators::Lemmas::Equivalence::Basic::{
    initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic,
    runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic,
};
pub unsafe fn l_Std_IterStep_bundledQuotient___redArg(
    mut v_inst_60_: *mut leanh::LeanObject,
    mut v_step_61_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_62_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_63_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_65_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_66_: u8 = 0;
    let mut v___x_67_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_71_: u8 = 0;
    let mut v_it_72_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_74_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_75_: u8 = 0;
    let mut v___x_76_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_80_: u8 = 0;
    let mut v___x_81_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_step_61_) {
                0 => {
                    v_it_62_ = leanh::lean_ctor_get(v_step_61_, 0);
                    v_out_63_ = leanh::lean_ctor_get(v_step_61_, 1);
                    v_isSharedCheck_71_ = (!leanh::lean_is_exclusive(v_step_61_)) as u8;
                    if v_isSharedCheck_71_ == 0 {
                        v___x_65_ = v_step_61_;
                        v_isShared_66_ = v_isSharedCheck_71_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_out_63_);
                        leanh::lean_inc(v_it_62_);
                        leanh::lean_dec(v_step_61_);
                        v___x_65_ = leanh::lean_box(0);
                        v_isShared_66_ = v_isSharedCheck_71_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_72_ = leanh::lean_ctor_get(v_step_61_, 0);
                    v_isSharedCheck_80_ = (!leanh::lean_is_exclusive(v_step_61_)) as u8;
                    if v_isSharedCheck_80_ == 0 {
                        v___x_74_ = v_step_61_;
                        v_isShared_75_ = v_isSharedCheck_80_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_72_);
                        leanh::lean_dec(v_step_61_);
                        v___x_74_ = leanh::lean_box(0);
                        v_isShared_75_ = v_isSharedCheck_80_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_inst_60_);
                    v___x_81_ = leanh::lean_box(2);
                    return v___x_81_;
                }
            },
            1 => {
                v___x_67_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_67_, 0, v_inst_60_);
                leanh::lean_ctor_set(v___x_67_, 1, v_it_62_);
                if v_isShared_66_ == 0 {
                    leanh::lean_ctor_set(v___x_65_, 0, v___x_67_);
                    v___x_69_ = v___x_65_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_70_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_67_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_70_, 1, v_out_63_);
                    v___x_69_ = v_reuseFailAlloc_70_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_69_;
            }
            3 => {
                v___x_76_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_76_, 0, v_inst_60_);
                leanh::lean_ctor_set(v___x_76_, 1, v_it_72_);
                if v_isShared_75_ == 0 {
                    leanh::lean_ctor_set(v___x_74_, 0, v___x_76_);
                    v___x_78_ = v___x_74_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_79_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
                    v___x_78_ = v_reuseFailAlloc_79_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_78_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IterStep_bundledQuotient(
    mut v_00_u03b1_82_: *mut leanh::LeanObject,
    mut v_m_83_: *mut leanh::LeanObject,
    mut v_00_u03b2_84_: *mut leanh::LeanObject,
    mut v_inst_85_: *mut leanh::LeanObject,
    mut v_inst_86_: *mut leanh::LeanObject,
    mut v_inst_87_: *mut leanh::LeanObject,
    mut v_step_88_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_89_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_89_ = l_Std_IterStep_bundledQuotient___redArg(v_inst_85_, v_step_88_);
    return v___x_89_;
}
pub unsafe fn l_Std_IterStep_bundledQuotient___boxed(
    mut v_00_u03b1_90_: *mut leanh::LeanObject,
    mut v_m_91_: *mut leanh::LeanObject,
    mut v_00_u03b2_92_: *mut leanh::LeanObject,
    mut v_inst_93_: *mut leanh::LeanObject,
    mut v_inst_94_: *mut leanh::LeanObject,
    mut v_inst_95_: *mut leanh::LeanObject,
    mut v_step_96_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_97_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_97_ = l_Std_IterStep_bundledQuotient(
        v_00_u03b1_90_,
        v_m_91_,
        v_00_u03b2_92_,
        v_inst_93_,
        v_inst_94_,
        v_inst_95_,
        v_step_96_,
    );
    leanh::lean_dec_ref(v_inst_94_);
    return v_res_97_;
}
pub unsafe fn l_Std_IterM_QuotStep_bundledQuotient___redArg(
    mut v_inst_98_: *mut leanh::LeanObject,
    mut v_a_99_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_100_ = l_Std_IterStep_bundledQuotient___redArg(v_inst_98_, v_a_99_);
    return v___x_100_;
}
pub unsafe fn l_Std_IterM_QuotStep_bundledQuotient(
    mut v_00_u03b1_101_: *mut leanh::LeanObject,
    mut v_m_102_: *mut leanh::LeanObject,
    mut v_00_u03b2_103_: *mut leanh::LeanObject,
    mut v_inst_104_: *mut leanh::LeanObject,
    mut v_inst_105_: *mut leanh::LeanObject,
    mut v_inst_106_: *mut leanh::LeanObject,
    mut v_it_107_: *mut leanh::LeanObject,
    mut v_a_108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_109_ = l_Std_IterStep_bundledQuotient___redArg(v_inst_104_, v_a_108_);
    return v___x_109_;
}
pub unsafe fn l_Std_IterM_QuotStep_bundledQuotient___boxed(
    mut v_00_u03b1_110_: *mut leanh::LeanObject,
    mut v_m_111_: *mut leanh::LeanObject,
    mut v_00_u03b2_112_: *mut leanh::LeanObject,
    mut v_inst_113_: *mut leanh::LeanObject,
    mut v_inst_114_: *mut leanh::LeanObject,
    mut v_inst_115_: *mut leanh::LeanObject,
    mut v_it_116_: *mut leanh::LeanObject,
    mut v_a_117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_118_ = l_Std_IterM_QuotStep_bundledQuotient(
        v_00_u03b1_110_,
        v_m_111_,
        v_00_u03b2_112_,
        v_inst_113_,
        v_inst_114_,
        v_inst_115_,
        v_it_116_,
        v_a_117_,
    );
    leanh::lean_dec(v_it_116_);
    leanh::lean_dec_ref(v_inst_114_);
    return v_res_118_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
}