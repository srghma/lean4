// Lean compiler output
// Module: Init.Data.String.Legacy
// Imports: Init.Data.String.Basic
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::ffi::{
    lean_string_utf8_at_end, lean_string_utf8_extract, lean_string_utf8_get, lean_string_utf8_next,
};
use crate::ffi::{lean_nat_sub, lean_string_dec_eq, lean_uint32_dec_eq};
pub static l_String_splitOn___closed__0_value: crate::leanh::LeanStringObject<1> =
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
static mut l_String_splitOn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_splitOn___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_String_splitAux(
    mut v_s_80_: *mut crate::leanh::LeanObject,
    mut v_p_81_: *mut crate::leanh::LeanObject,
    mut v_b_82_: *mut crate::leanh::LeanObject,
    mut v_i_83_: *mut crate::leanh::LeanObject,
    mut v_r_84_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_85_: u8 = 0;
    let mut v___x_86_: u32 = 0;
    let mut v___x_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_89_: u8 = 0;
    let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_x27_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_85_ = lean_string_utf8_at_end(v_s_80_, v_i_83_);
                if v___x_85_ == 0 {
                    v___x_86_ = lean_string_utf8_get(v_s_80_, v_i_83_);
                    v___x_87_ = crate::leanh::lean_box_uint32(v___x_86_);
                    crate::leanh::lean_inc_ref(v_p_81_);
                    v___x_88_ = crate::leanh::lean_apply_1(v_p_81_, v___x_87_);
                    v___x_89_ = (crate::leanh::lean_unbox(v___x_88_) as u8);
                    if v___x_89_ == 0 {
                        v___x_90_ = lean_string_utf8_next(v_s_80_, v_i_83_);
                        crate::leanh::lean_dec(v_i_83_);
                        v_i_83_ = v___x_90_;
                        state = 0;
                        continue;
                    } else {
                        v_i_x27_92_ = lean_string_utf8_next(v_s_80_, v_i_83_);
                        v___x_93_ = lean_string_utf8_extract(v_s_80_, v_b_82_, v_i_83_);
                        crate::leanh::lean_dec(v_i_83_);
                        crate::leanh::lean_dec(v_b_82_);
                        v___x_94_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_94_, 0, v___x_93_);
                        crate::leanh::lean_ctor_set(v___x_94_, 1, v_r_84_);
                        crate::leanh::lean_inc(v_i_x27_92_);
                        v_b_82_ = v_i_x27_92_;
                        v_i_83_ = v_i_x27_92_;
                        v_r_84_ = v___x_94_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_81_);
                    v___x_96_ = lean_string_utf8_extract(v_s_80_, v_b_82_, v_i_83_);
                    crate::leanh::lean_dec(v_i_83_);
                    crate::leanh::lean_dec(v_b_82_);
                    v_r_97_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_r_97_, 0, v___x_96_);
                    crate::leanh::lean_ctor_set(v_r_97_, 1, v_r_84_);
                    v___x_98_ = l_List_reverse___redArg(v_r_97_);
                    return v___x_98_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_splitAux___boxed(
    mut v_s_99_: *mut crate::leanh::LeanObject,
    mut v_p_100_: *mut crate::leanh::LeanObject,
    mut v_b_101_: *mut crate::leanh::LeanObject,
    mut v_i_102_: *mut crate::leanh::LeanObject,
    mut v_r_103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_104_ = l_String_splitAux(v_s_99_, v_p_100_, v_b_101_, v_i_102_, v_r_103_);
    crate::leanh::lean_dec_ref(v_s_99_);
    return v_res_104_;
}
pub unsafe fn l_String_splitToList(
    mut v_s_105_: *mut crate::leanh::LeanObject,
    mut v_p_106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_107_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_108_ = crate::leanh::lean_box(0);
    v___x_109_ = l_String_splitAux(v_s_105_, v_p_106_, v___x_107_, v___x_107_, v___x_108_);
    return v___x_109_;
}
pub unsafe fn l_String_splitToList___boxed(
    mut v_s_110_: *mut crate::leanh::LeanObject,
    mut v_p_111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_112_ = l_String_splitToList(v_s_110_, v_p_111_);
    crate::leanh::lean_dec_ref(v_s_110_);
    return v_res_112_;
}
pub unsafe fn l_String_splitOnAux(
    mut v_s_113_: *mut crate::leanh::LeanObject,
    mut v_sep_114_: *mut crate::leanh::LeanObject,
    mut v_b_115_: *mut crate::leanh::LeanObject,
    mut v_i_116_: *mut crate::leanh::LeanObject,
    mut v_j_117_: *mut crate::leanh::LeanObject,
    mut v_r_118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_119_: u8 = 0;
    let mut v___x_120_: u32 = 0;
    let mut v___x_121_: u32 = 0;
    let mut v___x_122_: u8 = 0;
    let mut v___x_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: u8 = 0;
    let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                        crate::leanh::lean_dec(v_j_117_);
                        crate::leanh::lean_dec(v_i_116_);
                        v___x_124_ = lean_string_utf8_next(v_s_113_, v___x_123_);
                        crate::leanh::lean_dec(v___x_123_);
                        v___x_125_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_i_116_ = v___x_124_;
                        v_j_117_ = v___x_125_;
                        state = 0;
                        continue;
                    } else {
                        v_i_127_ = lean_string_utf8_next(v_s_113_, v_i_116_);
                        crate::leanh::lean_dec(v_i_116_);
                        v_j_128_ = lean_string_utf8_next(v_sep_114_, v_j_117_);
                        crate::leanh::lean_dec(v_j_117_);
                        v___x_129_ = lean_string_utf8_at_end(v_sep_114_, v_j_128_);
                        if v___x_129_ == 0 {
                            v_i_116_ = v_i_127_;
                            v_j_117_ = v_j_128_;
                            state = 0;
                            continue;
                        } else {
                            v___x_131_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_132_ = lean_nat_sub(v_i_127_, v_j_128_);
                            crate::leanh::lean_dec(v_j_128_);
                            v___x_133_ = lean_string_utf8_extract(v_s_113_, v_b_115_, v___x_132_);
                            crate::leanh::lean_dec(v___x_132_);
                            crate::leanh::lean_dec(v_b_115_);
                            v___x_134_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_134_, 0, v___x_133_);
                            crate::leanh::lean_ctor_set(v___x_134_, 1, v_r_118_);
                            crate::leanh::lean_inc(v_i_127_);
                            v_b_115_ = v_i_127_;
                            v_i_116_ = v_i_127_;
                            v_j_117_ = v___x_131_;
                            v_r_118_ = v___x_134_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_j_117_);
                    v___x_136_ = lean_string_utf8_extract(v_s_113_, v_b_115_, v_i_116_);
                    crate::leanh::lean_dec(v_i_116_);
                    crate::leanh::lean_dec(v_b_115_);
                    v_r_137_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_r_137_, 0, v___x_136_);
                    crate::leanh::lean_ctor_set(v_r_137_, 1, v_r_118_);
                    v___x_138_ = l_List_reverse___redArg(v_r_137_);
                    return v___x_138_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_splitOnAux___boxed(
    mut v_s_139_: *mut crate::leanh::LeanObject,
    mut v_sep_140_: *mut crate::leanh::LeanObject,
    mut v_b_141_: *mut crate::leanh::LeanObject,
    mut v_i_142_: *mut crate::leanh::LeanObject,
    mut v_j_143_: *mut crate::leanh::LeanObject,
    mut v_r_144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_145_ = l_String_splitOnAux(v_s_139_, v_sep_140_, v_b_141_, v_i_142_, v_j_143_, v_r_144_);
    crate::leanh::lean_dec_ref(v_sep_140_);
    crate::leanh::lean_dec_ref(v_s_139_);
    return v_res_145_;
}
pub unsafe fn l_String_splitOn(
    mut v_s_147_: *mut crate::leanh::LeanObject,
    mut v_sep_148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_150_: u8 = 0;
    v___x_149_ = l_String_splitOn___closed__0;
    v___x_150_ = lean_string_dec_eq(v_sep_148_, v___x_149_);
    if v___x_150_ == 0 {
        let mut v___x_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_151_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_152_ = crate::leanh::lean_box(0);
        v___x_153_ = l_String_splitOnAux(
            v_s_147_, v_sep_148_, v___x_151_, v___x_151_, v___x_151_, v___x_152_,
        );
        crate::leanh::lean_dec_ref(v_s_147_);
        return v___x_153_;
    } else {
        let mut v___x_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_154_ = crate::leanh::lean_box(0);
        v___x_155_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_155_, 0, v_s_147_);
        crate::leanh::lean_ctor_set(v___x_155_, 1, v___x_154_);
        return v___x_155_;
    }
}
pub unsafe fn l_String_splitOn___boxed(
    mut v_s_156_: *mut crate::leanh::LeanObject,
    mut v_sep_157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_158_ = l_String_splitOn(v_s_156_, v_sep_157_);
    crate::leanh::lean_dec_ref(v_sep_157_);
    return v_res_158_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Legacy(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Legacy(
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
pub unsafe fn initialize_Init_Data_String_Legacy(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Legacy(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Legacy(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Legacy(builtin);
}
