// Lean compiler output
// Module: Init.Data.String.Iter.Intercalate
// Imports: Init.Data.Iterators.Combinators.Monadic.FilterMap Init.Data.String.Basic Init.Data.String.Slice
use crate::r#gen::Init::Data::Iterators::Combinators::Monadic::FilterMap::{
    initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap,
    runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::ffi::lean_string_utf8_extract;
use crate::ffi::lean_string_append;
pub static l_Std_Iter_joinString___redArg___closed__0_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Std_Iter_joinString___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_joinString___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Iter_joinString___redArg___lam__0(
    mut v_inst_88_: *mut crate::leanh::LeanObject,
    mut v_inst_89_: *mut crate::leanh::LeanObject,
    mut v_it_90_: *mut crate::leanh::LeanObject,
    mut v_acc_91_: *mut crate::leanh::LeanObject,
    mut v_hP_92_: *mut crate::leanh::LeanObject,
    mut v_recur_93_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_94_ = crate::leanh::lean_apply_1(v_inst_88_, v_it_90_);
    match crate::leanh::lean_obj_tag(v_val_94_) {
        0 => {
            let mut v_it_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_95_ = crate::leanh::lean_ctor_get(v_val_94_, 0);
            crate::leanh::lean_inc(v_it_95_);
            v_out_96_ = crate::leanh::lean_ctor_get(v_val_94_, 1);
            crate::leanh::lean_inc(v_out_96_);
            crate::leanh::lean_dec_ref_known(v_val_94_, 2);
            v___x_97_ = crate::leanh::lean_apply_1(v_inst_89_, v_out_96_);
            v___x_98_ = lean_string_append(v_acc_91_, v___x_97_);
            crate::leanh::lean_dec_ref(v___x_97_);
            v___x_99_ = crate::leanh::lean_apply_4(
                v_recur_93_,
                v_it_95_,
                v___x_98_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_99_;
        }
        1 => {
            let mut v_it_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_inst_89_);
            v_it_100_ = crate::leanh::lean_ctor_get(v_val_94_, 0);
            crate::leanh::lean_inc(v_it_100_);
            crate::leanh::lean_dec_ref_known(v_val_94_, 1);
            v___x_101_ = crate::leanh::lean_apply_4(
                v_recur_93_,
                v_it_100_,
                v_acc_91_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_101_;
        }
        _ => {
            crate::leanh::lean_dec_ref(v_recur_93_);
            crate::leanh::lean_dec_ref(v_inst_89_);
            return v_acc_91_;
        }
    }
}
pub unsafe fn l_Std_Iter_joinString___redArg(
    mut v_inst_103_: *mut crate::leanh::LeanObject,
    mut v_inst_104_: *mut crate::leanh::LeanObject,
    mut v_it_105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_106_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_joinString___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_106_, 0, v_inst_103_);
    crate::leanh::lean_closure_set(v___f_106_, 1, v_inst_104_);
    v___x_107_ = l_Std_Iter_joinString___redArg___closed__0;
    v___x_108_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_106_,
        v_it_105_,
        v___x_107_,
        crate::leanh::lean_box(0),
    );
    return v___x_108_;
}
pub unsafe fn l_Std_Iter_joinString(
    mut v_00_u03b1_109_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_110_: *mut crate::leanh::LeanObject,
    mut v_inst_111_: *mut crate::leanh::LeanObject,
    mut v_inst_112_: *mut crate::leanh::LeanObject,
    mut v_it_113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_114_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_joinString___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_114_, 0, v_inst_111_);
    crate::leanh::lean_closure_set(v___f_114_, 1, v_inst_112_);
    v___x_115_ = l_Std_Iter_joinString___redArg___closed__0;
    v___x_116_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_114_,
        v_it_113_,
        v___x_115_,
        crate::leanh::lean_box(0),
    );
    return v___x_116_;
}
pub unsafe fn l_Std_Iter_intercalateString___redArg___lam__0(
    mut v_inst_117_: *mut crate::leanh::LeanObject,
    mut v_inst_118_: *mut crate::leanh::LeanObject,
    mut v_s_119_: *mut crate::leanh::LeanObject,
    mut v_it_120_: *mut crate::leanh::LeanObject,
    mut v_acc_121_: *mut crate::leanh::LeanObject,
    mut v_hP_122_: *mut crate::leanh::LeanObject,
    mut v_recur_123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_133_: u8 = 0;
    let mut v_str_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_144_: u8 = 0;
    let mut v_it_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_val_124_ = crate::leanh::lean_apply_1(v_inst_117_, v_it_120_);
                match crate::leanh::lean_obj_tag(v_val_124_) {
                    0 => {
                        v_it_125_ = crate::leanh::lean_ctor_get(v_val_124_, 0);
                        crate::leanh::lean_inc(v_it_125_);
                        v_out_126_ = crate::leanh::lean_ctor_get(v_val_124_, 1);
                        crate::leanh::lean_inc(v_out_126_);
                        crate::leanh::lean_dec_ref_known(v_val_124_, 2);
                        v___x_127_ = crate::leanh::lean_apply_1(v_inst_118_, v_out_126_);
                        if crate::leanh::lean_obj_tag(v_acc_121_) == 0 {
                            v___x_128_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_128_, 0, v___x_127_);
                            v___x_129_ = crate::leanh::lean_apply_4(
                                v_recur_123_,
                                v_it_125_,
                                v___x_128_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                            );
                            return v___x_129_;
                        } else {
                            v_val_130_ = crate::leanh::lean_ctor_get(v_acc_121_, 0);
                            v_isSharedCheck_144_ =
                                (!crate::leanh::lean_is_exclusive(v_acc_121_)) as u8;
                            if v_isSharedCheck_144_ == 0 {
                                v___x_132_ = v_acc_121_;
                                v_isShared_133_ = v_isSharedCheck_144_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_130_);
                                crate::leanh::lean_dec(v_acc_121_);
                                v___x_132_ = crate::leanh::lean_box(0);
                                v_isShared_133_ = v_isSharedCheck_144_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_inst_118_);
                        v_it_145_ = crate::leanh::lean_ctor_get(v_val_124_, 0);
                        crate::leanh::lean_inc(v_it_145_);
                        crate::leanh::lean_dec_ref_known(v_val_124_, 1);
                        v___x_146_ = crate::leanh::lean_apply_4(
                            v_recur_123_,
                            v_it_145_,
                            v_acc_121_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                        );
                        return v___x_146_;
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v_recur_123_);
                        crate::leanh::lean_dec_ref(v_inst_118_);
                        return v_acc_121_;
                    }
                }
            }
            1 => {
                v_str_134_ = crate::leanh::lean_ctor_get(v_s_119_, 0);
                v_startInclusive_135_ = crate::leanh::lean_ctor_get(v_s_119_, 1);
                v_endExclusive_136_ = crate::leanh::lean_ctor_get(v_s_119_, 2);
                v___x_137_ = lean_string_utf8_extract(
                    v_str_134_,
                    v_startInclusive_135_,
                    v_endExclusive_136_,
                );
                v___x_138_ = lean_string_append(v_val_130_, v___x_137_);
                crate::leanh::lean_dec_ref(v___x_137_);
                v___x_139_ = lean_string_append(v___x_138_, v___x_127_);
                crate::leanh::lean_dec_ref(v___x_127_);
                if v_isShared_133_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_132_, 0, v___x_139_);
                    v___x_141_ = v___x_132_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_143_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_139_);
                    v___x_141_ = v_reuseFailAlloc_143_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_142_ = crate::leanh::lean_apply_4(
                    v_recur_123_,
                    v_it_125_,
                    v___x_141_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_142_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iter_intercalateString___redArg___lam__0___boxed(
    mut v_inst_147_: *mut crate::leanh::LeanObject,
    mut v_inst_148_: *mut crate::leanh::LeanObject,
    mut v_s_149_: *mut crate::leanh::LeanObject,
    mut v_it_150_: *mut crate::leanh::LeanObject,
    mut v_acc_151_: *mut crate::leanh::LeanObject,
    mut v_hP_152_: *mut crate::leanh::LeanObject,
    mut v_recur_153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_154_ = l_Std_Iter_intercalateString___redArg___lam__0(
        v_inst_147_,
        v_inst_148_,
        v_s_149_,
        v_it_150_,
        v_acc_151_,
        v_hP_152_,
        v_recur_153_,
    );
    crate::leanh::lean_dec_ref(v_s_149_);
    return v_res_154_;
}
pub unsafe fn l_Std_Iter_intercalateString___redArg(
    mut v_inst_155_: *mut crate::leanh::LeanObject,
    mut v_inst_156_: *mut crate::leanh::LeanObject,
    mut v_s_157_: *mut crate::leanh::LeanObject,
    mut v_it_158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_159_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_intercalateString___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    crate::leanh::lean_closure_set(v___f_159_, 0, v_inst_155_);
    crate::leanh::lean_closure_set(v___f_159_, 1, v_inst_156_);
    crate::leanh::lean_closure_set(v___f_159_, 2, v_s_157_);
    v___x_160_ = crate::leanh::lean_box(0);
    v___x_161_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_159_,
        v_it_158_,
        v___x_160_,
        crate::leanh::lean_box(0),
    );
    if crate::leanh::lean_obj_tag(v___x_161_) == 0 {
        let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_162_ = l_Std_Iter_joinString___redArg___closed__0;
        return v___x_162_;
    } else {
        let mut v_val_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_163_ = crate::leanh::lean_ctor_get(v___x_161_, 0);
        crate::leanh::lean_inc(v_val_163_);
        crate::leanh::lean_dec_ref_known(v___x_161_, 1);
        return v_val_163_;
    }
}
pub unsafe fn l_Std_Iter_intercalateString(
    mut v_00_u03b1_164_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_165_: *mut crate::leanh::LeanObject,
    mut v_inst_166_: *mut crate::leanh::LeanObject,
    mut v_inst_167_: *mut crate::leanh::LeanObject,
    mut v_s_168_: *mut crate::leanh::LeanObject,
    mut v_it_169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_170_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_intercalateString___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    crate::leanh::lean_closure_set(v___f_170_, 0, v_inst_166_);
    crate::leanh::lean_closure_set(v___f_170_, 1, v_inst_167_);
    crate::leanh::lean_closure_set(v___f_170_, 2, v_s_168_);
    v___x_171_ = crate::leanh::lean_box(0);
    v___x_172_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_170_,
        v_it_169_,
        v___x_171_,
        crate::leanh::lean_box(0),
    );
    if crate::leanh::lean_obj_tag(v___x_172_) == 0 {
        let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_173_ = l_Std_Iter_joinString___redArg___closed__0;
        return v___x_173_;
    } else {
        let mut v_val_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_174_ = crate::leanh::lean_ctor_get(v___x_172_, 0);
        crate::leanh::lean_inc(v_val_174_);
        crate::leanh::lean_dec_ref_known(v___x_172_, 1);
        return v_val_174_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Iter_Intercalate(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Iter_Intercalate(
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
pub unsafe fn initialize_Init_Data_String_Iter_Intercalate(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iter_Intercalate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Iter_Intercalate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Iter_Intercalate(builtin);
}
