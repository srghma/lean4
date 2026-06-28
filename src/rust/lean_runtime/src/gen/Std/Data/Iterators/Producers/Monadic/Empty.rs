// Lean compiler output
// Module: Std.Data.Iterators.Producers.Monadic.Empty
// Imports: Init.Data.Iterators.Consumers.Loop
use crate::r#gen::Init::Data::Iterators::Consumers::Loop::{
    initialize_Init_Data_Iterators_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Loop,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_2, lean_apply_3, lean_apply_4,
    lean_box, lean_closure_set, lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l_Std_IterM_empty(
    mut v_m_83_: *mut LeanObject,
    mut v_00_u03b2_84_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_85_: *mut LeanObject = core::ptr::null_mut();
    v___x_85_ = lean_box(0);
    return v___x_85_;
}
pub unsafe fn l_Std_Iterators_Types_Empty_instIterator___redArg___lam__0(
    mut v_toPure_86_: *mut LeanObject,
    mut v_x_87_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
    v___x_88_ = lean_box(2);
    v___x_89_ = lean_apply_2(v_toPure_86_, lean_box(0), v___x_88_);
    return v___x_89_;
}
pub unsafe fn l_Std_Iterators_Types_Empty_instIterator___redArg(
    mut v_inst_90_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_91_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_92_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_93_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_91_ = lean_ctor_get(v_inst_90_, 0);
    lean_inc_ref(v_toApplicative_91_);
    lean_dec_ref(v_inst_90_);
    v_toPure_92_ = lean_ctor_get(v_toApplicative_91_, 1);
    lean_inc(v_toPure_92_);
    lean_dec_ref(v_toApplicative_91_);
    v___f_93_ = lean_alloc_closure(
        l_Std_Iterators_Types_Empty_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_93_, 0, v_toPure_92_);
    return v___f_93_;
}
pub unsafe fn l_Std_Iterators_Types_Empty_instIterator(
    mut v_m_94_: *mut LeanObject,
    mut v_00_u03b2_95_: *mut LeanObject,
    mut v_inst_96_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
    v___x_97_ = l_Std_Iterators_Types_Empty_instIterator___redArg(v_inst_96_);
    return v___x_97_;
}
pub unsafe fn l___private_Std_Data_Iterators_Producers_Monadic_Empty_0__Std_Iterators_Types_Empty_instFinitenessRelation(
    mut v_m_98_: *mut LeanObject,
    mut v_00_u03b2_99_: *mut LeanObject,
    mut v_inst_100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
    v___x_101_ = lean_box(0);
    return v___x_101_;
}
pub unsafe fn l___private_Std_Data_Iterators_Producers_Monadic_Empty_0__Std_Iterators_Types_Empty_instFinitenessRelation___boxed(
    mut v_m_102_: *mut LeanObject,
    mut v_00_u03b2_103_: *mut LeanObject,
    mut v_inst_104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_105_: *mut LeanObject = core::ptr::null_mut();
    v_res_105_ = l___private_Std_Data_Iterators_Producers_Monadic_Empty_0__Std_Iterators_Types_Empty_instFinitenessRelation(v_m_102_, v_00_u03b2_103_, v_inst_104_);
    lean_dec_ref(v_inst_104_);
    return v_res_105_;
}
pub unsafe fn l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__0(
    mut v_toPure_106_: *mut LeanObject,
    mut v_recur_107_: *mut LeanObject,
    mut v_it_108_: *mut LeanObject,
    mut v_____do__lift_109_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_109_) == 0 {
        let mut v_a_110_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_111_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_recur_107_);
        v_a_110_ = lean_ctor_get(v_____do__lift_109_, 0);
        lean_inc(v_a_110_);
        lean_dec_ref_known(v_____do__lift_109_, 1);
        v___x_111_ = lean_apply_2(v_toPure_106_, lean_box(0), v_a_110_);
        return v___x_111_;
    } else {
        let mut v_a_112_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_106_);
        v_a_112_ = lean_ctor_get(v_____do__lift_109_, 0);
        lean_inc(v_a_112_);
        lean_dec_ref_known(v_____do__lift_109_, 1);
        v___x_113_ = lean_apply_4(v_recur_107_, v_it_108_, v_a_112_, lean_box(0), lean_box(0));
        return v___x_113_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__1(
    mut v_toPure_114_: *mut LeanObject,
    mut v_recur_115_: *mut LeanObject,
    mut v___y_116_: *mut LeanObject,
    mut v_acc_117_: *mut LeanObject,
    mut v_toBind_118_: *mut LeanObject,
    mut v_s_119_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_119_) {
        0 => {
            let mut v_it_120_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_121_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_122_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
            v_it_120_ = lean_ctor_get(v_s_119_, 0);
            lean_inc(v_it_120_);
            v_out_121_ = lean_ctor_get(v_s_119_, 1);
            lean_inc(v_out_121_);
            lean_dec_ref_known(v_s_119_, 2);
            v___f_122_ = lean_alloc_closure(
                l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_122_, 0, v_toPure_114_);
            lean_closure_set(v___f_122_, 1, v_recur_115_);
            lean_closure_set(v___f_122_, 2, v_it_120_);
            v___x_123_ = lean_apply_3(v___y_116_, v_out_121_, lean_box(0), v_acc_117_);
            v___x_124_ = lean_apply_4(
                v_toBind_118_,
                lean_box(0),
                lean_box(0),
                v___x_123_,
                v___f_122_,
            );
            return v___x_124_;
        }
        1 => {
            let mut v_it_125_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_118_);
            lean_dec(v___y_116_);
            lean_dec(v_toPure_114_);
            v_it_125_ = lean_ctor_get(v_s_119_, 0);
            lean_inc(v_it_125_);
            lean_dec_ref_known(v_s_119_, 1);
            v___x_126_ = lean_apply_4(
                v_recur_115_,
                v_it_125_,
                v_acc_117_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_126_;
        }
        _ => {
            let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_118_);
            lean_dec(v___y_116_);
            lean_dec(v_recur_115_);
            v___x_127_ = lean_apply_2(v_toPure_114_, lean_box(0), v_acc_117_);
            return v___x_127_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__2(
    mut v_inst_128_: *mut LeanObject,
    mut v_toPure_129_: *mut LeanObject,
    mut v___y_130_: *mut LeanObject,
    mut v_toBind_131_: *mut LeanObject,
    mut v_lift_132_: *mut LeanObject,
    mut v_it_133_: *mut LeanObject,
    mut v_acc_134_: *mut LeanObject,
    mut v_hP_135_: *mut LeanObject,
    mut v_recur_136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_142_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_137_ = lean_ctor_get(v_inst_128_, 0);
    lean_inc_ref(v_toApplicative_137_);
    lean_dec_ref(v_inst_128_);
    v_toPure_138_ = lean_ctor_get(v_toApplicative_137_, 1);
    lean_inc(v_toPure_138_);
    lean_dec_ref(v_toApplicative_137_);
    v___f_139_ = lean_alloc_closure(
        l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_139_, 0, v_toPure_129_);
    lean_closure_set(v___f_139_, 1, v_recur_136_);
    lean_closure_set(v___f_139_, 2, v___y_130_);
    lean_closure_set(v___f_139_, 3, v_acc_134_);
    lean_closure_set(v___f_139_, 4, v_toBind_131_);
    v___x_140_ = lean_box(2);
    v___x_141_ = lean_apply_2(v_toPure_138_, lean_box(0), v___x_140_);
    v___x_142_ = lean_apply_4(
        v_lift_132_,
        lean_box(0),
        lean_box(0),
        v___f_139_,
        v___x_141_,
    );
    return v___x_142_;
}
pub unsafe fn l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__3(
    mut v_inst_143_: *mut LeanObject,
    mut v_inst_144_: *mut LeanObject,
    mut v_lift_145_: *mut LeanObject,
    mut v_00_u03b3_146_: *mut LeanObject,
    mut v_Pl_147_: *mut LeanObject,
    mut v_it_148_: *mut LeanObject,
    mut v_init_149_: *mut LeanObject,
    mut v___y_150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_151_ = lean_ctor_get(v_inst_143_, 0);
    lean_inc_ref(v_toApplicative_151_);
    v_toBind_152_ = lean_ctor_get(v_inst_143_, 1);
    lean_inc(v_toBind_152_);
    lean_dec_ref(v_inst_143_);
    v_toPure_153_ = lean_ctor_get(v_toApplicative_151_, 1);
    lean_inc(v_toPure_153_);
    lean_dec_ref(v_toApplicative_151_);
    v___f_154_ = lean_alloc_closure(
        l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        5,
    );
    lean_closure_set(v___f_154_, 0, v_inst_144_);
    lean_closure_set(v___f_154_, 1, v_toPure_153_);
    lean_closure_set(v___f_154_, 2, v___y_150_);
    lean_closure_set(v___f_154_, 3, v_toBind_152_);
    lean_closure_set(v___f_154_, 4, v_lift_145_);
    v___x_155_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_154_, v_it_148_, v_init_149_, lean_box(0));
    return v___x_155_;
}
pub unsafe fn l_Std_Iterators_Types_Empty_instIteratorLoop___redArg(
    mut v_inst_156_: *mut LeanObject,
    mut v_inst_157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_158_: *mut LeanObject = core::ptr::null_mut();
    v___f_158_ = lean_alloc_closure(
        l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        2,
    );
    lean_closure_set(v___f_158_, 0, v_inst_157_);
    lean_closure_set(v___f_158_, 1, v_inst_156_);
    return v___f_158_;
}
pub unsafe fn l_Std_Iterators_Types_Empty_instIteratorLoop(
    mut v_m_159_: *mut LeanObject,
    mut v_00_u03b2_160_: *mut LeanObject,
    mut v_n_161_: *mut LeanObject,
    mut v_inst_162_: *mut LeanObject,
    mut v_inst_163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_164_: *mut LeanObject = core::ptr::null_mut();
    v___f_164_ = lean_alloc_closure(
        l_Std_Iterators_Types_Empty_instIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        2,
    );
    lean_closure_set(v___f_164_, 0, v_inst_163_);
    lean_closure_set(v___f_164_, 1, v_inst_162_);
    return v___f_164_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Producers_Monadic_Empty(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Producers_Monadic_Empty(
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
pub unsafe fn initialize_Std_Data_Iterators_Producers_Monadic_Empty(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Empty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Producers_Monadic_Empty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Producers_Monadic_Empty(builtin);
}
