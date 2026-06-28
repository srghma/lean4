// Lean compiler output
// Module: Std.Data.Iterators.Producers.Repeat
// Imports: Init.Data.Iterators.Consumers.Monadic
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::{
    initialize_Init_Data_Iterators_Consumers_Monadic,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIterator___redArg___lam__0(
    mut v_f_82_: *mut LeanObject,
    mut v_it_83_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_85_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_it_83_);
    v___x_84_ = lean_apply_1(v_f_82_, v_it_83_);
    v___x_85_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_85_, 0, v___x_84_);
    lean_ctor_set(v___x_85_, 1, v_it_83_);
    return v___x_85_;
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIterator___redArg(
    mut v_f_86_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_87_: *mut LeanObject = core::ptr::null_mut();
    v___f_87_ = lean_alloc_closure(
        l_Std_Iterators_Types_RepeatIterator_instIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_87_, 0, v_f_86_);
    return v___f_87_;
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIterator(
    mut v_00_u03b1_88_: *mut LeanObject,
    mut v_f_89_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_90_: *mut LeanObject = core::ptr::null_mut();
    v___f_90_ = lean_alloc_closure(
        l_Std_Iterators_Types_RepeatIterator_instIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_90_, 0, v_f_89_);
    return v___f_90_;
}
pub unsafe fn l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_Types_RepeatIterator_instProductivenessRelation(
    mut v_00_u03b1_91_: *mut LeanObject,
    mut v_f_92_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
    v___x_93_ = lean_box(0);
    return v___x_93_;
}
pub unsafe fn l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_Types_RepeatIterator_instProductivenessRelation___boxed(
    mut v_00_u03b1_94_: *mut LeanObject,
    mut v_f_95_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_96_: *mut LeanObject = core::ptr::null_mut();
    v_res_96_ = l___private_Std_Data_Iterators_Producers_Repeat_0__Std_Iterators_Types_RepeatIterator_instProductivenessRelation(v_00_u03b1_94_, v_f_95_);
    lean_dec(v_f_95_);
    return v_res_96_;
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__0(
    mut v_toPure_97_: *mut LeanObject,
    mut v_recur_98_: *mut LeanObject,
    mut v_it_99_: *mut LeanObject,
    mut v_____do__lift_100_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_100_) == 0 {
        let mut v_a_101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_it_99_);
        lean_dec(v_recur_98_);
        v_a_101_ = lean_ctor_get(v_____do__lift_100_, 0);
        lean_inc(v_a_101_);
        lean_dec_ref_known(v_____do__lift_100_, 1);
        v___x_102_ = lean_apply_2(v_toPure_97_, lean_box(0), v_a_101_);
        return v___x_102_;
    } else {
        let mut v_a_103_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_97_);
        v_a_103_ = lean_ctor_get(v_____do__lift_100_, 0);
        lean_inc(v_a_103_);
        lean_dec_ref_known(v_____do__lift_100_, 1);
        v___x_104_ = lean_apply_4(v_recur_98_, v_it_99_, v_a_103_, lean_box(0), lean_box(0));
        return v___x_104_;
    }
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__1(
    mut v_toPure_105_: *mut LeanObject,
    mut v_recur_106_: *mut LeanObject,
    mut v___y_107_: *mut LeanObject,
    mut v_acc_108_: *mut LeanObject,
    mut v_toBind_109_: *mut LeanObject,
    mut v_s_110_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_110_) {
        0 => {
            let mut v_it_111_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_112_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_113_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_115_: *mut LeanObject = core::ptr::null_mut();
            v_it_111_ = lean_ctor_get(v_s_110_, 0);
            lean_inc(v_it_111_);
            v_out_112_ = lean_ctor_get(v_s_110_, 1);
            lean_inc(v_out_112_);
            lean_dec_ref_known(v_s_110_, 2);
            v___f_113_ = lean_alloc_closure(
                l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_113_, 0, v_toPure_105_);
            lean_closure_set(v___f_113_, 1, v_recur_106_);
            lean_closure_set(v___f_113_, 2, v_it_111_);
            v___x_114_ = lean_apply_3(v___y_107_, v_out_112_, lean_box(0), v_acc_108_);
            v___x_115_ = lean_apply_4(
                v_toBind_109_,
                lean_box(0),
                lean_box(0),
                v___x_114_,
                v___f_113_,
            );
            return v___x_115_;
        }
        1 => {
            let mut v_it_116_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_109_);
            lean_dec(v___y_107_);
            lean_dec(v_toPure_105_);
            v_it_116_ = lean_ctor_get(v_s_110_, 0);
            lean_inc(v_it_116_);
            lean_dec_ref_known(v_s_110_, 1);
            v___x_117_ = lean_apply_4(
                v_recur_106_,
                v_it_116_,
                v_acc_108_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_117_;
        }
        _ => {
            let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_109_);
            lean_dec(v___y_107_);
            lean_dec(v_recur_106_);
            v___x_118_ = lean_apply_2(v_toPure_105_, lean_box(0), v_acc_108_);
            return v___x_118_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__2(
    mut v_toPure_119_: *mut LeanObject,
    mut v___y_120_: *mut LeanObject,
    mut v_toBind_121_: *mut LeanObject,
    mut v_f_122_: *mut LeanObject,
    mut v_lift_123_: *mut LeanObject,
    mut v_it_124_: *mut LeanObject,
    mut v_acc_125_: *mut LeanObject,
    mut v_hP_126_: *mut LeanObject,
    mut v_recur_127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
    v___f_128_ = lean_alloc_closure(
        l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_128_, 0, v_toPure_119_);
    lean_closure_set(v___f_128_, 1, v_recur_127_);
    lean_closure_set(v___f_128_, 2, v___y_120_);
    lean_closure_set(v___f_128_, 3, v_acc_125_);
    lean_closure_set(v___f_128_, 4, v_toBind_121_);
    lean_inc(v_it_124_);
    v___x_129_ = lean_apply_1(v_f_122_, v_it_124_);
    v___x_130_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_130_, 0, v___x_129_);
    lean_ctor_set(v___x_130_, 1, v_it_124_);
    v___x_131_ = lean_apply_4(
        v_lift_123_,
        lean_box(0),
        lean_box(0),
        v___f_128_,
        v___x_130_,
    );
    return v___x_131_;
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__3(
    mut v_inst_132_: *mut LeanObject,
    mut v_f_133_: *mut LeanObject,
    mut v_lift_134_: *mut LeanObject,
    mut v_00_u03b3_135_: *mut LeanObject,
    mut v_Pl_136_: *mut LeanObject,
    mut v_it_137_: *mut LeanObject,
    mut v_init_138_: *mut LeanObject,
    mut v___y_139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_144_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_140_ = lean_ctor_get(v_inst_132_, 0);
    lean_inc_ref(v_toApplicative_140_);
    v_toBind_141_ = lean_ctor_get(v_inst_132_, 1);
    lean_inc(v_toBind_141_);
    lean_dec_ref(v_inst_132_);
    v_toPure_142_ = lean_ctor_get(v_toApplicative_140_, 1);
    lean_inc(v_toPure_142_);
    lean_dec_ref(v_toApplicative_140_);
    v___f_143_ = lean_alloc_closure(
        l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        5,
    );
    lean_closure_set(v___f_143_, 0, v_toPure_142_);
    lean_closure_set(v___f_143_, 1, v___y_139_);
    lean_closure_set(v___f_143_, 2, v_toBind_141_);
    lean_closure_set(v___f_143_, 3, v_f_133_);
    lean_closure_set(v___f_143_, 4, v_lift_134_);
    v___x_144_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_143_, v_it_137_, v_init_138_, lean_box(0));
    return v___x_144_;
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg(
    mut v_f_145_: *mut LeanObject,
    mut v_inst_146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_147_: *mut LeanObject = core::ptr::null_mut();
    v___f_147_ = lean_alloc_closure(
        l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        2,
    );
    lean_closure_set(v___f_147_, 0, v_inst_146_);
    lean_closure_set(v___f_147_, 1, v_f_145_);
    return v___f_147_;
}
pub unsafe fn l_Std_Iterators_Types_RepeatIterator_instIteratorLoop(
    mut v_00_u03b1_148_: *mut LeanObject,
    mut v_f_149_: *mut LeanObject,
    mut v_n_150_: *mut LeanObject,
    mut v_inst_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_152_: *mut LeanObject = core::ptr::null_mut();
    v___f_152_ = lean_alloc_closure(
        l_Std_Iterators_Types_RepeatIterator_instIteratorLoop___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        2,
    );
    lean_closure_set(v___f_152_, 0, v_inst_151_);
    lean_closure_set(v___f_152_, 1, v_f_149_);
    return v___f_152_;
}
pub unsafe fn l_Std_Iter_repeat___redArg(mut v_init_153_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_init_153_);
    return v_init_153_;
}
pub unsafe fn l_Std_Iter_repeat___redArg___boxed(
    mut v_init_154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_155_: *mut LeanObject = core::ptr::null_mut();
    v_res_155_ = l_Std_Iter_repeat___redArg(v_init_154_);
    lean_dec(v_init_154_);
    return v_res_155_;
}
pub unsafe fn l_Std_Iter_repeat(
    mut v_00_u03b1_156_: *mut LeanObject,
    mut v_f_157_: *mut LeanObject,
    mut v_init_158_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_init_158_);
    return v_init_158_;
}
pub unsafe fn l_Std_Iter_repeat___boxed(
    mut v_00_u03b1_159_: *mut LeanObject,
    mut v_f_160_: *mut LeanObject,
    mut v_init_161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_162_: *mut LeanObject = core::ptr::null_mut();
    v_res_162_ = l_Std_Iter_repeat(v_00_u03b1_159_, v_f_160_, v_init_161_);
    lean_dec(v_init_161_);
    lean_dec(v_f_160_);
    return v_res_162_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Producers_Repeat(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Producers_Repeat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_Iterators_Producers_Repeat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Repeat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Producers_Repeat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Producers_Repeat(builtin);
}
