// Lean compiler output
// Module: Std.Data.Iterators.Producers.Repeat
// Imports: Init.Data.Iterators.Consumers.Monadic
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::{
    initialize_Init_Data_Iterators_Consumers_Monadic,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIterator___redArg___lam__0(
    mut v_f_82_: *mut crate::leanh::LeanObject,
    mut v_it_83_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_it_83_);
    v___x_84_ = crate::leanh::lean_apply_1(v_f_82_, v_it_83_);
    v___x_85_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_85_, 0, v___x_84_);
    crate::leanh::lean_ctor_set(v___x_85_, 1, v_it_83_);
    return v___x_85_;
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIterator___redArg(
    mut v_f_86_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_87_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_RepeatIterator_instIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_87_, 0, v_f_86_);
    return v___f_87_;
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIterator(
    mut v_00_u03b1_88_: *mut crate::leanh::LeanObject,
    mut v_f_89_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_90_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_RepeatIterator_instIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_90_, 0, v_f_89_);
    return v___f_90_;
}
pub unsafe fn l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_Types_RepeatIterator_instProductivenessRelation(
    mut v_00_u03b1_91_: *mut crate::leanh::LeanObject,
    mut v_f_92_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_93_ = crate::leanh::lean_box(0);
    return v___x_93_;
}
pub unsafe fn l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_Types_RepeatIterator_instProductivenessRelation___boxed(
    mut v_00_u03b1_94_: *mut crate::leanh::LeanObject,
    mut v_f_95_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_96_ = l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_Types_RepeatIterator_instProductivenessRelation(v_00_u03b1_94_, v_f_95_);
    crate::leanh::lean_dec(v_f_95_);
    return v_res_96_;
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__0(
    mut v_toPure_97_: *mut crate::leanh::LeanObject,
    mut v_recur_98_: *mut crate::leanh::LeanObject,
    mut v_it_99_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_100_) == 0 {
        let mut v_a_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_it_99_);
        crate::leanh::lean_dec(v_recur_98_);
        v_a_101_ = crate::leanh::lean_ctor_get(v_____do__lift_100_, 0);
        crate::leanh::lean_inc(v_a_101_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_100_, 1);
        v___x_102_ = crate::leanh::lean_apply_2(v_toPure_97_, crate::leanh::lean_box(0), v_a_101_);
        return v___x_102_;
    } else {
        let mut v_a_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_97_);
        v_a_103_ = crate::leanh::lean_ctor_get(v_____do__lift_100_, 0);
        crate::leanh::lean_inc(v_a_103_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_100_, 1);
        v___x_104_ = crate::leanh::lean_apply_4(
            v_recur_98_,
            v_it_99_,
            v_a_103_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_104_;
    }
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__1(
    mut v_toPure_105_: *mut crate::leanh::LeanObject,
    mut v_recur_106_: *mut crate::leanh::LeanObject,
    mut v___y_107_: *mut crate::leanh::LeanObject,
    mut v_acc_108_: *mut crate::leanh::LeanObject,
    mut v_toBind_109_: *mut crate::leanh::LeanObject,
    mut v_s_110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_110_) {
        0 => {
            let mut v_it_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_111_ = crate::leanh::lean_ctor_get(v_s_110_, 0);
            crate::leanh::lean_inc(v_it_111_);
            v_out_112_ = crate::leanh::lean_ctor_get(v_s_110_, 1);
            crate::leanh::lean_inc(v_out_112_);
            crate::leanh::lean_dec_ref_known(v_s_110_, 2);
            v___f_113_ = crate::leanh::lean_alloc_closure(
                l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_113_, 0, v_toPure_105_);
            crate::leanh::lean_closure_set(v___f_113_, 1, v_recur_106_);
            crate::leanh::lean_closure_set(v___f_113_, 2, v_it_111_);
            v___x_114_ = crate::leanh::lean_apply_3(
                v___y_107_,
                v_out_112_,
                crate::leanh::lean_box(0),
                v_acc_108_,
            );
            v___x_115_ = crate::leanh::lean_apply_4(
                v_toBind_109_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_114_,
                v___f_113_,
            );
            return v___x_115_;
        }
        1 => {
            let mut v_it_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_109_);
            crate::leanh::lean_dec(v___y_107_);
            crate::leanh::lean_dec(v_toPure_105_);
            v_it_116_ = crate::leanh::lean_ctor_get(v_s_110_, 0);
            crate::leanh::lean_inc(v_it_116_);
            crate::leanh::lean_dec_ref_known(v_s_110_, 1);
            v___x_117_ = crate::leanh::lean_apply_4(
                v_recur_106_,
                v_it_116_,
                v_acc_108_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_117_;
        }
        _ => {
            let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_109_);
            crate::leanh::lean_dec(v___y_107_);
            crate::leanh::lean_dec(v_recur_106_);
            v___x_118_ =
                crate::leanh::lean_apply_2(v_toPure_105_, crate::leanh::lean_box(0), v_acc_108_);
            return v___x_118_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__2(
    mut v_toPure_119_: *mut crate::leanh::LeanObject,
    mut v___y_120_: *mut crate::leanh::LeanObject,
    mut v_toBind_121_: *mut crate::leanh::LeanObject,
    mut v_f_122_: *mut crate::leanh::LeanObject,
    mut v_lift_123_: *mut crate::leanh::LeanObject,
    mut v_it_124_: *mut crate::leanh::LeanObject,
    mut v_acc_125_: *mut crate::leanh::LeanObject,
    mut v_hP_126_: *mut crate::leanh::LeanObject,
    mut v_recur_127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_128_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_128_, 0, v_toPure_119_);
    crate::leanh::lean_closure_set(v___f_128_, 1, v_recur_127_);
    crate::leanh::lean_closure_set(v___f_128_, 2, v___y_120_);
    crate::leanh::lean_closure_set(v___f_128_, 3, v_acc_125_);
    crate::leanh::lean_closure_set(v___f_128_, 4, v_toBind_121_);
    crate::leanh::lean_inc(v_it_124_);
    v___x_129_ = crate::leanh::lean_apply_1(v_f_122_, v_it_124_);
    v___x_130_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_130_, 0, v___x_129_);
    crate::leanh::lean_ctor_set(v___x_130_, 1, v_it_124_);
    v___x_131_ = crate::leanh::lean_apply_4(
        v_lift_123_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_128_,
        v___x_130_,
    );
    return v___x_131_;
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__3(
    mut v_inst_132_: *mut crate::leanh::LeanObject,
    mut v_f_133_: *mut crate::leanh::LeanObject,
    mut v_lift_134_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_135_: *mut crate::leanh::LeanObject,
    mut v_Pl_136_: *mut crate::leanh::LeanObject,
    mut v_it_137_: *mut crate::leanh::LeanObject,
    mut v_init_138_: *mut crate::leanh::LeanObject,
    mut v___y_139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_140_ = crate::leanh::lean_ctor_get(v_inst_132_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_140_);
    v_toBind_141_ = crate::leanh::lean_ctor_get(v_inst_132_, 1);
    crate::leanh::lean_inc(v_toBind_141_);
    crate::leanh::lean_dec_ref(v_inst_132_);
    v_toPure_142_ = crate::leanh::lean_ctor_get(v_toApplicative_140_, 1);
    crate::leanh::lean_inc(v_toPure_142_);
    crate::leanh::lean_dec_ref(v_toApplicative_140_);
    v___f_143_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        5,
    );
    crate::leanh::lean_closure_set(v___f_143_, 0, v_toPure_142_);
    crate::leanh::lean_closure_set(v___f_143_, 1, v___y_139_);
    crate::leanh::lean_closure_set(v___f_143_, 2, v_toBind_141_);
    crate::leanh::lean_closure_set(v___f_143_, 3, v_f_133_);
    crate::leanh::lean_closure_set(v___f_143_, 4, v_lift_134_);
    v___x_144_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_143_,
        v_it_137_,
        v_init_138_,
        crate::leanh::lean_box(0),
    );
    return v___x_144_;
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg(
    mut v_f_145_: *mut crate::leanh::LeanObject,
    mut v_inst_146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_147_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___f_147_, 0, v_inst_146_);
    crate::leanh::lean_closure_set(v___f_147_, 1, v_f_145_);
    return v___f_147_;
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIteratorLoop(
    mut v_00_u03b1_148_: *mut crate::leanh::LeanObject,
    mut v_f_149_: *mut crate::leanh::LeanObject,
    mut v_n_150_: *mut crate::leanh::LeanObject,
    mut v_inst_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_152_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___f_152_, 0, v_inst_151_);
    crate::leanh::lean_closure_set(v___f_152_, 1, v_f_149_);
    return v___f_152_;
}
pub unsafe fn l_Std_Iter_repeat___redArg(
    mut v_init_153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_init_153_);
    return v_init_153_;
}
pub unsafe fn l_Std_Iter_repeat___redArg___boxed(
    mut v_init_154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_155_ = l_Std_Iter_repeat___redArg(v_init_154_);
    crate::leanh::lean_dec(v_init_154_);
    return v_res_155_;
}
pub unsafe fn l_Std_Iter_repeat(
    mut v_00_u03b1_156_: *mut crate::leanh::LeanObject,
    mut v_f_157_: *mut crate::leanh::LeanObject,
    mut v_init_158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_init_158_);
    return v_init_158_;
}
pub unsafe fn l_Std_Iter_repeat___boxed(
    mut v_00_u03b1_159_: *mut crate::leanh::LeanObject,
    mut v_f_160_: *mut crate::leanh::LeanObject,
    mut v_init_161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_162_ = l_Std_Iter_repeat(v_00_u03b1_159_, v_f_160_, v_init_161_);
    crate::leanh::lean_dec(v_init_161_);
    crate::leanh::lean_dec(v_f_160_);
    return v_res_162_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Producers_Repeat(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Producers_Repeat(
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
pub unsafe fn initialize_Std_Data_Iterators_Producers_Repeat(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Repeat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Producers_Repeat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Producers_Repeat(builtin);
}
