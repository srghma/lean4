// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Equivalence.StepCongr
// Imports: Std.Data.Iterators.Lemmas.Equivalence.Basic
use crate::r#gen::Std::Data::Iterators::Lemmas::Equivalence::Basic::{
    initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic,
    runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_tag,
};
pub unsafe fn l_Std_IterStep_bundledQuotient___redArg(
    mut v_inst_60_: *mut LeanObject,
    mut v_step_61_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_62_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_63_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_65_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_66_: u8 = 0;
    let mut v___x_67_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_69_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_70_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_71_: u8 = 0;
    let mut v_it_72_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_74_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_75_: u8 = 0;
    let mut v___x_76_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_79_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_80_: u8 = 0;
    let mut v___x_81_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_step_61_) {
                0 => {
                    v_it_62_ = lean_ctor_get(v_step_61_, 0);
                    v_out_63_ = lean_ctor_get(v_step_61_, 1);
                    v_isSharedCheck_71_ = (!lean_is_exclusive(v_step_61_)) as u8;
                    if v_isSharedCheck_71_ == 0 {
                        v___x_65_ = v_step_61_;
                        v_isShared_66_ = v_isSharedCheck_71_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_out_63_);
                        lean_inc(v_it_62_);
                        lean_dec(v_step_61_);
                        v___x_65_ = lean_box(0);
                        v_isShared_66_ = v_isSharedCheck_71_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_72_ = lean_ctor_get(v_step_61_, 0);
                    v_isSharedCheck_80_ = (!lean_is_exclusive(v_step_61_)) as u8;
                    if v_isSharedCheck_80_ == 0 {
                        v___x_74_ = v_step_61_;
                        v_isShared_75_ = v_isSharedCheck_80_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_it_72_);
                        lean_dec(v_step_61_);
                        v___x_74_ = lean_box(0);
                        v_isShared_75_ = v_isSharedCheck_80_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_inst_60_);
                    v___x_81_ = lean_box(2);
                    return v___x_81_;
                }
            },
            1 => {
                v___x_67_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_67_, 0, v_inst_60_);
                lean_ctor_set(v___x_67_, 1, v_it_62_);
                if v_isShared_66_ == 0 {
                    lean_ctor_set(v___x_65_, 0, v___x_67_);
                    v___x_69_ = v___x_65_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_67_);
                    lean_ctor_set(v_reuseFailAlloc_70_, 1, v_out_63_);
                    v___x_69_ = v_reuseFailAlloc_70_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_69_;
            }
            3 => {
                v___x_76_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_76_, 0, v_inst_60_);
                lean_ctor_set(v___x_76_, 1, v_it_72_);
                if v_isShared_75_ == 0 {
                    lean_ctor_set(v___x_74_, 0, v___x_76_);
                    v___x_78_ = v___x_74_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
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
    mut v_00_u03b1_82_: *mut LeanObject,
    mut v_m_83_: *mut LeanObject,
    mut v_00_u03b2_84_: *mut LeanObject,
    mut v_inst_85_: *mut LeanObject,
    mut v_inst_86_: *mut LeanObject,
    mut v_inst_87_: *mut LeanObject,
    mut v_step_88_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
    v___x_89_ = l_Std_IterStep_bundledQuotient___redArg(v_inst_85_, v_step_88_);
    return v___x_89_;
}
pub unsafe fn l_Std_IterStep_bundledQuotient___boxed(
    mut v_00_u03b1_90_: *mut LeanObject,
    mut v_m_91_: *mut LeanObject,
    mut v_00_u03b2_92_: *mut LeanObject,
    mut v_inst_93_: *mut LeanObject,
    mut v_inst_94_: *mut LeanObject,
    mut v_inst_95_: *mut LeanObject,
    mut v_step_96_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_97_: *mut LeanObject = core::ptr::null_mut();
    v_res_97_ = l_Std_IterStep_bundledQuotient(
        v_00_u03b1_90_,
        v_m_91_,
        v_00_u03b2_92_,
        v_inst_93_,
        v_inst_94_,
        v_inst_95_,
        v_step_96_,
    );
    lean_dec_ref(v_inst_94_);
    return v_res_97_;
}
pub unsafe fn l_Std_IterM_QuotStep_bundledQuotient___redArg(
    mut v_inst_98_: *mut LeanObject,
    mut v_a_99_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
    v___x_100_ = l_Std_IterStep_bundledQuotient___redArg(v_inst_98_, v_a_99_);
    return v___x_100_;
}
pub unsafe fn l_Std_IterM_QuotStep_bundledQuotient(
    mut v_00_u03b1_101_: *mut LeanObject,
    mut v_m_102_: *mut LeanObject,
    mut v_00_u03b2_103_: *mut LeanObject,
    mut v_inst_104_: *mut LeanObject,
    mut v_inst_105_: *mut LeanObject,
    mut v_inst_106_: *mut LeanObject,
    mut v_it_107_: *mut LeanObject,
    mut v_a_108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
    v___x_109_ = l_Std_IterStep_bundledQuotient___redArg(v_inst_104_, v_a_108_);
    return v___x_109_;
}
pub unsafe fn l_Std_IterM_QuotStep_bundledQuotient___boxed(
    mut v_00_u03b1_110_: *mut LeanObject,
    mut v_m_111_: *mut LeanObject,
    mut v_00_u03b2_112_: *mut LeanObject,
    mut v_inst_113_: *mut LeanObject,
    mut v_inst_114_: *mut LeanObject,
    mut v_inst_115_: *mut LeanObject,
    mut v_it_116_: *mut LeanObject,
    mut v_a_117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_118_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_it_116_);
    lean_dec_ref(v_inst_114_);
    return v_res_118_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
}
