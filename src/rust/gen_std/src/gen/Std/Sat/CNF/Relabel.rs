// Lean compiler output
// Module: Std.Sat.CNF.Relabel
// Imports: Std.Sat.CNF.Basic
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uset, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Std::Sat::CNF::Basic::{
    initialize_Std_Sat_CNF_Basic, runtime_initialize_Std_Sat_CNF_Basic,
};
pub unsafe fn l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(
    mut v_r_86_: *mut crate::leanh::LeanObject,
    mut v_a_87_: *mut crate::leanh::LeanObject,
    mut v_a_88_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_94_: u8 = 0;
    let mut v_fst_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_99_: u8 = 0;
    let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_108_: u8 = 0;
    let mut v_isSharedCheck_109_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_87_) == 0 {
                    crate::leanh::lean_dec(v_r_86_);
                    v___x_89_ = l_List_reverse___redArg(v_a_88_);
                    return v___x_89_;
                } else {
                    v_head_90_ = crate::leanh::lean_ctor_get(v_a_87_, 0);
                    v_tail_91_ = crate::leanh::lean_ctor_get(v_a_87_, 1);
                    v_isSharedCheck_109_ = (!crate::leanh::lean_is_exclusive(v_a_87_)) as u8;
                    if v_isSharedCheck_109_ == 0 {
                        v___x_93_ = v_a_87_;
                        v_isShared_94_ = v_isSharedCheck_109_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_91_);
                        crate::leanh::lean_inc(v_head_90_);
                        crate::leanh::lean_dec(v_a_87_);
                        v___x_93_ = crate::leanh::lean_box(0);
                        v_isShared_94_ = v_isSharedCheck_109_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_95_ = crate::leanh::lean_ctor_get(v_head_90_, 0);
                v_snd_96_ = crate::leanh::lean_ctor_get(v_head_90_, 1);
                v_isSharedCheck_108_ = (!crate::leanh::lean_is_exclusive(v_head_90_)) as u8;
                if v_isSharedCheck_108_ == 0 {
                    v___x_98_ = v_head_90_;
                    v_isShared_99_ = v_isSharedCheck_108_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_96_);
                    crate::leanh::lean_inc(v_fst_95_);
                    crate::leanh::lean_dec(v_head_90_);
                    v___x_98_ = crate::leanh::lean_box(0);
                    v_isShared_99_ = v_isSharedCheck_108_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_r_86_);
                v___x_100_ = crate::leanh::lean_apply_1(v_r_86_, v_fst_95_);
                if v_isShared_99_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_98_, 0, v___x_100_);
                    v___x_102_ = v___x_98_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_107_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_107_, 1, v_snd_96_);
                    v___x_102_ = v_reuseFailAlloc_107_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_94_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_93_, 1, v_a_88_);
                    crate::leanh::lean_ctor_set(v___x_93_, 0, v___x_102_);
                    v___x_104_ = v___x_93_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_106_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_102_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_106_, 1, v_a_88_);
                    v___x_104_ = v_reuseFailAlloc_106_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_87_ = v_tail_91_;
                v_a_88_ = v___x_104_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_CNF_Clause_relabel___redArg(
    mut v_r_110_: *mut crate::leanh::LeanObject,
    mut v_c_111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_112_ = crate::leanh::lean_box(0);
    v___x_113_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(
        v_r_110_, v_c_111_, v___x_112_,
    );
    return v___x_113_;
}
pub unsafe fn l_Std_Sat_CNF_Clause_relabel(
    mut v_00_u03b1_114_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_115_: *mut crate::leanh::LeanObject,
    mut v_r_116_: *mut crate::leanh::LeanObject,
    mut v_c_117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_118_ = l_Std_Sat_CNF_Clause_relabel___redArg(v_r_116_, v_c_117_);
    return v___x_118_;
}
pub unsafe fn l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_relabel_spec__0(
    mut v_00_u03b1_119_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_120_: *mut crate::leanh::LeanObject,
    mut v_r_121_: *mut crate::leanh::LeanObject,
    mut v_a_122_: *mut crate::leanh::LeanObject,
    mut v_a_123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_124_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_relabel_spec__0___redArg(
        v_r_121_, v_a_122_, v_a_123_,
    );
    return v___x_124_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(
    mut v_r_125_: *mut crate::leanh::LeanObject,
    mut v_sz_126_: usize,
    mut v_i_127_: usize,
    mut v_bs_128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_129_: u8 = 0;
    let mut v_v_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_134_: usize = 0;
    let mut v___x_135_: usize = 0;
    let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_129_ = lean_usize_dec_lt(v_i_127_, v_sz_126_);
                if v___x_129_ == 0 {
                    crate::leanh::lean_dec(v_r_125_);
                    return v_bs_128_;
                } else {
                    v_v_130_ = lean_array_uget(v_bs_128_, v_i_127_);
                    v___x_131_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_132_ = lean_array_uset(v_bs_128_, v_i_127_, v___x_131_);
                    crate::leanh::lean_inc(v_r_125_);
                    v___x_133_ = l_Std_Sat_CNF_Clause_relabel___redArg(v_r_125_, v_v_130_);
                    v___x_134_ = 1usize;
                    v___x_135_ = lean_usize_add(v_i_127_, v___x_134_);
                    v___x_136_ = lean_array_uset(v_bs_x27_132_, v_i_127_, v___x_133_);
                    v_i_127_ = v___x_135_;
                    v_bs_128_ = v___x_136_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg___boxed(
    mut v_r_138_: *mut crate::leanh::LeanObject,
    mut v_sz_139_: *mut crate::leanh::LeanObject,
    mut v_i_140_: *mut crate::leanh::LeanObject,
    mut v_bs_141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_142_: usize = 0;
    let mut v_i_boxed_143_: usize = 0;
    let mut v_res_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_142_ = crate::leanh::lean_unbox_usize(v_sz_139_);
    crate::leanh::lean_dec(v_sz_139_);
    v_i_boxed_143_ = crate::leanh::lean_unbox_usize(v_i_140_);
    crate::leanh::lean_dec(v_i_140_);
    v_res_144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_138_, v_sz_boxed_142_, v_i_boxed_143_, v_bs_141_);
    return v_res_144_;
}
pub unsafe fn l_Std_Sat_CNF_relabel___redArg(
    mut v_r_145_: *mut crate::leanh::LeanObject,
    mut v_f_146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_147_: usize = 0;
    let mut v___x_148_: usize = 0;
    let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_147_ = lean_array_size(v_f_146_);
    v___x_148_ = 0usize;
    v___x_149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_145_, v_sz_147_, v___x_148_, v_f_146_);
    return v___x_149_;
}
pub unsafe fn l_Std_Sat_CNF_relabel(
    mut v_00_u03b1_150_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_151_: *mut crate::leanh::LeanObject,
    mut v_r_152_: *mut crate::leanh::LeanObject,
    mut v_f_153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_154_ = l_Std_Sat_CNF_relabel___redArg(v_r_152_, v_f_153_);
    return v___x_154_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0(
    mut v_00_u03b1_155_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_156_: *mut crate::leanh::LeanObject,
    mut v_r_157_: *mut crate::leanh::LeanObject,
    mut v_sz_158_: usize,
    mut v_i_159_: usize,
    mut v_bs_160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___redArg(v_r_157_, v_sz_158_, v_i_159_, v_bs_160_);
    return v___x_161_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0___boxed(
    mut v_00_u03b1_162_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_163_: *mut crate::leanh::LeanObject,
    mut v_r_164_: *mut crate::leanh::LeanObject,
    mut v_sz_165_: *mut crate::leanh::LeanObject,
    mut v_i_166_: *mut crate::leanh::LeanObject,
    mut v_bs_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_168_: usize = 0;
    let mut v_i_boxed_169_: usize = 0;
    let mut v_res_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_168_ = crate::leanh::lean_unbox_usize(v_sz_165_);
    crate::leanh::lean_dec(v_sz_165_);
    v_i_boxed_169_ = crate::leanh::lean_unbox_usize(v_i_166_);
    crate::leanh::lean_dec(v_i_166_);
    v_res_170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_CNF_relabel_spec__0(v_00_u03b1_162_, v_00_u03b2_163_, v_r_164_, v_sz_boxed_168_, v_i_boxed_169_, v_bs_167_);
    return v_res_170_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_CNF_Relabel(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_CNF_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_CNF_Relabel(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_CNF_Relabel(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_CNF_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_CNF_Relabel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sat_CNF_Relabel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Sat_CNF_Relabel(builtin);
}
