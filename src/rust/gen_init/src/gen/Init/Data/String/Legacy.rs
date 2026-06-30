// Lean compiler output
// Module: Init.Data.String.Legacy
// Imports: Init.Data.String.Basic
use crate::ffi::{
    lean_nat_sub, lean_string_dec_eq, lean_string_utf8_at_end, lean_string_utf8_extract,
    lean_string_utf8_get, lean_string_utf8_next, lean_uint32_dec_eq,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
pub static l_String_splitOn___closed__0_value: leanh::LeanStringObject<1> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_String_splitOn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_splitOn___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_String_splitAux(
    mut v_s_80_: *mut leanh::LeanObject,
    mut v_p_81_: *mut leanh::LeanObject,
    mut v_b_82_: *mut leanh::LeanObject,
    mut v_i_83_: *mut leanh::LeanObject,
    mut v_r_84_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_85_: u8 = 0;
    let mut v___x_86_: u32 = 0;
    let mut v___x_87_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_88_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_89_: u8 = 0;
    let mut v___x_90_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_x27_92_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_96_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_97_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_85_ = lean_string_utf8_at_end(v_s_80_, v_i_83_);
                if v___x_85_ == 0 {
                    v___x_86_ = lean_string_utf8_get(v_s_80_, v_i_83_);
                    v___x_87_ = leanh::lean_box_uint32(v___x_86_);
                    leanh::lean_inc_ref(v_p_81_);
                    v___x_88_ = leanh::lean_apply_1(v_p_81_, v___x_87_);
                    v___x_89_ = (leanh::lean_unbox(v___x_88_) as u8);
                    if v___x_89_ == 0 {
                        v___x_90_ = lean_string_utf8_next(v_s_80_, v_i_83_);
                        leanh::lean_dec(v_i_83_);
                        v_i_83_ = v___x_90_;
                        state = 0;
                        continue;
                    } else {
                        v_i_x27_92_ = lean_string_utf8_next(v_s_80_, v_i_83_);
                        v___x_93_ = lean_string_utf8_extract(v_s_80_, v_b_82_, v_i_83_);
                        leanh::lean_dec(v_i_83_);
                        leanh::lean_dec(v_b_82_);
                        v___x_94_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_94_, 0, v___x_93_);
                        leanh::lean_ctor_set(v___x_94_, 1, v_r_84_);
                        leanh::lean_inc(v_i_x27_92_);
                        v_b_82_ = v_i_x27_92_;
                        v_i_83_ = v_i_x27_92_;
                        v_r_84_ = v___x_94_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_p_81_);
                    v___x_96_ = lean_string_utf8_extract(v_s_80_, v_b_82_, v_i_83_);
                    leanh::lean_dec(v_i_83_);
                    leanh::lean_dec(v_b_82_);
                    v_r_97_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_r_97_, 0, v___x_96_);
                    leanh::lean_ctor_set(v_r_97_, 1, v_r_84_);
                    v___x_98_ = l_List_reverse___redArg(v_r_97_);
                    return v___x_98_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_splitAux___boxed(
    mut v_s_99_: *mut leanh::LeanObject,
    mut v_p_100_: *mut leanh::LeanObject,
    mut v_b_101_: *mut leanh::LeanObject,
    mut v_i_102_: *mut leanh::LeanObject,
    mut v_r_103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_104_ = l_String_splitAux(v_s_99_, v_p_100_, v_b_101_, v_i_102_, v_r_103_);
    leanh::lean_dec_ref(v_s_99_);
    return v_res_104_;
}
pub unsafe fn l_String_splitToList(
    mut v_s_105_: *mut leanh::LeanObject,
    mut v_p_106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_107_ = leanh::lean_unsigned_to_nat(0);
    v___x_108_ = leanh::lean_box(0);
    v___x_109_ = l_String_splitAux(v_s_105_, v_p_106_, v___x_107_, v___x_107_, v___x_108_);
    return v___x_109_;
}
pub unsafe fn l_String_splitToList___boxed(
    mut v_s_110_: *mut leanh::LeanObject,
    mut v_p_111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_112_ = l_String_splitToList(v_s_110_, v_p_111_);
    leanh::lean_dec_ref(v_s_110_);
    return v_res_112_;
}
pub unsafe fn l_String_splitOnAux(
    mut v_s_113_: *mut leanh::LeanObject,
    mut v_sep_114_: *mut leanh::LeanObject,
    mut v_b_115_: *mut leanh::LeanObject,
    mut v_i_116_: *mut leanh::LeanObject,
    mut v_j_117_: *mut leanh::LeanObject,
    mut v_r_118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_119_: u8 = 0;
    let mut v___x_120_: u32 = 0;
    let mut v___x_121_: u32 = 0;
    let mut v___x_122_: u8 = 0;
    let mut v___x_123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: u8 = 0;
    let mut v___x_131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_119_ = lean_string_utf8_at_end(v_s_113_, v_i_116_);
                if v___x_119_ == 0 {
                    v___x_120_ = lean_string_utf8_get(v_s_113_, v_i_116_);
                    v___x_121_ = lean_string_utf8_get(v_sep_114_, v_j_117_);
                    v___x_122_ = lean_uint32_dec_eq(v___x_120_, v___x_121_);
                    if v___x_122_ == 0 {
                        v___x_123_ = lean_nat_sub(v_i_116_, v_j_117_);
                        leanh::lean_dec(v_j_117_);
                        leanh::lean_dec(v_i_116_);
                        v___x_124_ = lean_string_utf8_next(v_s_113_, v___x_123_);
                        leanh::lean_dec(v___x_123_);
                        v___x_125_ = leanh::lean_unsigned_to_nat(0);
                        v_i_116_ = v___x_124_;
                        v_j_117_ = v___x_125_;
                        state = 0;
                        continue;
                    } else {
                        v_i_127_ = lean_string_utf8_next(v_s_113_, v_i_116_);
                        leanh::lean_dec(v_i_116_);
                        v_j_128_ = lean_string_utf8_next(v_sep_114_, v_j_117_);
                        leanh::lean_dec(v_j_117_);
                        v___x_129_ = lean_string_utf8_at_end(v_sep_114_, v_j_128_);
                        if v___x_129_ == 0 {
                            v_i_116_ = v_i_127_;
                            v_j_117_ = v_j_128_;
                            state = 0;
                            continue;
                        } else {
                            v___x_131_ = leanh::lean_unsigned_to_nat(0);
                            v___x_132_ = lean_nat_sub(v_i_127_, v_j_128_);
                            leanh::lean_dec(v_j_128_);
                            v___x_133_ = lean_string_utf8_extract(v_s_113_, v_b_115_, v___x_132_);
                            leanh::lean_dec(v___x_132_);
                            leanh::lean_dec(v_b_115_);
                            v___x_134_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_134_, 0, v___x_133_);
                            leanh::lean_ctor_set(v___x_134_, 1, v_r_118_);
                            leanh::lean_inc(v_i_127_);
                            v_b_115_ = v_i_127_;
                            v_i_116_ = v_i_127_;
                            v_j_117_ = v___x_131_;
                            v_r_118_ = v___x_134_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_j_117_);
                    v___x_136_ = lean_string_utf8_extract(v_s_113_, v_b_115_, v_i_116_);
                    leanh::lean_dec(v_i_116_);
                    leanh::lean_dec(v_b_115_);
                    v_r_137_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_r_137_, 0, v___x_136_);
                    leanh::lean_ctor_set(v_r_137_, 1, v_r_118_);
                    v___x_138_ = l_List_reverse___redArg(v_r_137_);
                    return v___x_138_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_splitOnAux___boxed(
    mut v_s_139_: *mut leanh::LeanObject,
    mut v_sep_140_: *mut leanh::LeanObject,
    mut v_b_141_: *mut leanh::LeanObject,
    mut v_i_142_: *mut leanh::LeanObject,
    mut v_j_143_: *mut leanh::LeanObject,
    mut v_r_144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_145_ = l_String_splitOnAux(v_s_139_, v_sep_140_, v_b_141_, v_i_142_, v_j_143_, v_r_144_);
    leanh::lean_dec_ref(v_sep_140_);
    leanh::lean_dec_ref(v_s_139_);
    return v_res_145_;
}
pub unsafe fn l_String_splitOn(
    mut v_s_147_: *mut leanh::LeanObject,
    mut v_sep_148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_150_: u8 = 0;
    v___x_149_ = l_String_splitOn___closed__0;
    v___x_150_ = lean_string_dec_eq(v_sep_148_, v___x_149_);
    if v___x_150_ == 0 {
        let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_153_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_151_ = leanh::lean_unsigned_to_nat(0);
        v___x_152_ = leanh::lean_box(0);
        v___x_153_ = l_String_splitOnAux(
            v_s_147_, v_sep_148_, v___x_151_, v___x_151_, v___x_151_, v___x_152_,
        );
        leanh::lean_dec_ref(v_s_147_);
        return v___x_153_;
    } else {
        let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_154_ = leanh::lean_box(0);
        v___x_155_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_155_, 0, v_s_147_);
        leanh::lean_ctor_set(v___x_155_, 1, v___x_154_);
        return v___x_155_;
    }
}
pub unsafe fn l_String_splitOn___boxed(
    mut v_s_156_: *mut leanh::LeanObject,
    mut v_sep_157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_158_ = l_String_splitOn(v_s_156_, v_sep_157_);
    leanh::lean_dec_ref(v_sep_157_);
    return v_res_158_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Legacy(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Legacy(
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
pub unsafe fn initialize_Init_Data_String_Legacy(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Legacy(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Legacy(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Legacy(builtin);
}