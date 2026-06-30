// Lean compiler output
// Module: Lake.Util.Casing
// Imports: Init.Data.String.Basic Init.Data.String.Modify Init.Data.String.Search Init.Data.Iterators.Consumers.Collect
use crate::ffi::{
    lean_array_push, lean_array_to_list, lean_nat_add, lean_nat_dec_eq, lean_nat_sub,
    lean_string_append, lean_string_utf8_byte_size, lean_string_utf8_extract, lean_string_utf8_get,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_string_utf8_set, lean_uint32_add,
    lean_uint32_dec_eq, lean_uint32_dec_le,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::Modify::{
    initialize_Init_Data_String_Modify, runtime_initialize_Init_Data_String_Modify,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Prelude::l_Lean_Name_str___override;
pub static l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_toUpperCamelCaseString___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_toUpperCamelCaseString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_toUpperCamelCaseString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_toUpperCamelCaseString___closed__1_value: leanh::LeanStringObject<1> =
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
static mut l_Lake_toUpperCamelCaseString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_toUpperCamelCaseString___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(
    mut v_s_117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_118_ =
        l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0;
    return v___x_118_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___boxed(
    mut v_s_119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_120_ =
        l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(v_s_119_);
    leanh::lean_dec_ref(v_s_119_);
    return v_res_120_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(
    mut v_str_121_: *mut leanh::LeanObject,
    mut v___x_122_: *mut leanh::LeanObject,
    mut v___x_123_: *mut leanh::LeanObject,
    mut v_a_124_: *mut leanh::LeanObject,
    mut v_b_125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: u32 = 0;
    let mut v___x_138_: u32 = 0;
    let mut v___x_139_: u8 = 0;
    let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_141_: u32 = 0;
    let mut v___x_142_: u8 = 0;
    let mut v___x_143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_144_: u32 = 0;
    let mut v___x_145_: u32 = 0;
    let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_151_: u8 = 0;
    let mut v___y_153_: u8 = 0;
    let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: u8 = 0;
    let mut v___x_172_: u32 = 0;
    let mut v___x_173_: u32 = 0;
    let mut v___x_174_: u8 = 0;
    let mut v___x_175_: u32 = 0;
    let mut v___x_176_: u8 = 0;
    let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_178_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_124_) == 0 {
                    v_currPos_147_ = leanh::lean_ctor_get(v_a_124_, 0);
                    v_searcher_148_ = leanh::lean_ctor_get(v_a_124_, 1);
                    v_isSharedCheck_178_ = (!leanh::lean_is_exclusive(v_a_124_)) as u8;
                    if v_isSharedCheck_178_ == 0 {
                        v___x_150_ = v_a_124_;
                        v_isShared_151_ = v_isSharedCheck_178_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_148_);
                        leanh::lean_inc(v_currPos_147_);
                        leanh::lean_dec(v_a_124_);
                        v___x_150_ = leanh::lean_box(0);
                        v_isShared_151_ = v_isSharedCheck_178_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_123_);
                    return v_b_125_;
                }
            }
            1 => {
                v___x_129_ = lean_array_push(v_b_125_, v_out_128_);
                v_a_124_ = v_it_127_;
                v_b_125_ = v___x_129_;
                state = 0;
                continue;
            }
            2 => {
                v___x_135_ = lean_string_utf8_extract(
                    v_str_121_,
                    v_startInclusive_133_,
                    v_endExclusive_134_,
                );
                leanh::lean_dec(v_endExclusive_134_);
                leanh::lean_dec(v_startInclusive_133_);
                v___x_136_ = leanh::lean_unsigned_to_nat(0);
                v___x_137_ = lean_string_utf8_get(v___x_135_, v___x_136_);
                v___x_138_ = 97;
                v___x_139_ = lean_uint32_dec_le(v___x_138_, v___x_137_);
                if v___x_139_ == 0 {
                    v___x_140_ = lean_string_utf8_set(v___x_135_, v___x_136_, v___x_137_);
                    v_it_127_ = v_it_132_;
                    v_out_128_ = v___x_140_;
                    state = 1;
                    continue;
                } else {
                    v___x_141_ = 122;
                    v___x_142_ = lean_uint32_dec_le(v___x_137_, v___x_141_);
                    if v___x_142_ == 0 {
                        v___x_143_ = lean_string_utf8_set(v___x_135_, v___x_136_, v___x_137_);
                        v_it_127_ = v_it_132_;
                        v_out_128_ = v___x_143_;
                        state = 1;
                        continue;
                    } else {
                        v___x_144_ = 4294967264;
                        v___x_145_ = lean_uint32_add(v___x_137_, v___x_144_);
                        v___x_146_ = lean_string_utf8_set(v___x_135_, v___x_136_, v___x_145_);
                        v_it_127_ = v_it_132_;
                        v_out_128_ = v___x_146_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v_startInclusive_168_ = leanh::lean_ctor_get(v___x_122_, 1);
                v_endExclusive_169_ = leanh::lean_ctor_get(v___x_122_, 2);
                v___x_170_ = lean_nat_sub(v_endExclusive_169_, v_startInclusive_168_);
                v___x_171_ = lean_nat_dec_eq(v_searcher_148_, v___x_170_);
                leanh::lean_dec(v___x_170_);
                if v___x_171_ == 0 {
                    v___x_172_ = lean_string_utf8_get_fast(v_str_121_, v_searcher_148_);
                    v___x_173_ = 95;
                    v___x_174_ = lean_uint32_dec_eq(v___x_172_, v___x_173_);
                    if v___x_174_ == 0 {
                        v___x_175_ = 45;
                        v___x_176_ = lean_uint32_dec_eq(v___x_172_, v___x_175_);
                        v___y_153_ = v___x_176_;
                        state = 4;
                        continue;
                    } else {
                        v___y_153_ = v___x_174_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_150_);
                    leanh::lean_dec(v_searcher_148_);
                    v___x_177_ = leanh::lean_box(1);
                    leanh::lean_inc(v___x_123_);
                    v_it_132_ = v___x_177_;
                    v_startInclusive_133_ = v_currPos_147_;
                    v_endExclusive_134_ = v___x_123_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v___y_153_ == 0 {
                    v___x_154_ = lean_string_utf8_next_fast(v_str_121_, v_searcher_148_);
                    leanh::lean_dec(v_searcher_148_);
                    if v_isShared_151_ == 0 {
                        leanh::lean_ctor_set(v___x_150_, 1, v___x_154_);
                        v___x_156_ = v___x_150_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_158_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_158_, 0, v_currPos_147_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_154_);
                        v___x_156_ = v_reuseFailAlloc_158_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_159_ = lean_string_utf8_next_fast(v_str_121_, v_searcher_148_);
                    v___x_160_ = lean_nat_sub(v___x_159_, v_searcher_148_);
                    v___x_161_ = lean_nat_add(v_searcher_148_, v___x_160_);
                    leanh::lean_dec(v___x_160_);
                    v_slice_162_ =
                        l_String_Slice_subslice_x21(v___x_122_, v_currPos_147_, v_searcher_148_);
                    leanh::lean_inc(v___x_161_);
                    if v_isShared_151_ == 0 {
                        leanh::lean_ctor_set(v___x_150_, 1, v___x_161_);
                        leanh::lean_ctor_set(v___x_150_, 0, v___x_161_);
                        v_nextIt_164_ = v___x_150_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_167_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_161_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_161_);
                        v_nextIt_164_ = v_reuseFailAlloc_167_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_a_124_ = v___x_156_;
                state = 0;
                continue;
            }
            6 => {
                v_startInclusive_165_ = leanh::lean_ctor_get(v_slice_162_, 0);
                leanh::lean_inc(v_startInclusive_165_);
                v_endExclusive_166_ = leanh::lean_ctor_get(v_slice_162_, 1);
                leanh::lean_inc(v_endExclusive_166_);
                leanh::lean_dec_ref(v_slice_162_);
                v_it_132_ = v_nextIt_164_;
                v_startInclusive_133_ = v_startInclusive_165_;
                v_endExclusive_134_ = v_endExclusive_166_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg___boxed(
    mut v_str_179_: *mut leanh::LeanObject,
    mut v___x_180_: *mut leanh::LeanObject,
    mut v___x_181_: *mut leanh::LeanObject,
    mut v_a_182_: *mut leanh::LeanObject,
    mut v_b_183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_184_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_179_, v___x_180_, v___x_181_, v_a_182_, v_b_183_);
    leanh::lean_dec_ref(v___x_180_);
    leanh::lean_dec_ref(v_str_179_);
    return v_res_184_;
}
pub unsafe fn l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(
    mut v_x_185_: *mut leanh::LeanObject,
    mut v_x_186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_186_) == 0 {
                    return v_x_185_;
                } else {
                    v_head_187_ = leanh::lean_ctor_get(v_x_186_, 0);
                    v_tail_188_ = leanh::lean_ctor_get(v_x_186_, 1);
                    v___x_189_ = lean_string_append(v_x_185_, v_head_187_);
                    v_x_185_ = v___x_189_;
                    v_x_186_ = v_tail_188_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2___boxed(
    mut v_x_191_: *mut leanh::LeanObject,
    mut v_x_192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_193_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v_x_191_, v_x_192_);
    leanh::lean_dec(v_x_192_);
    return v_res_193_;
}
pub unsafe fn l_Lake_toUpperCamelCaseString(
    mut v_str_197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parts_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_198_ = leanh::lean_unsigned_to_nat(0);
    v___x_199_ = lean_string_utf8_byte_size(v_str_197_);
    leanh::lean_inc_ref(v_str_197_);
    v___x_200_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_200_, 0, v_str_197_);
    leanh::lean_ctor_set(v___x_200_, 1, v___x_198_);
    leanh::lean_ctor_set(v___x_200_, 2, v___x_199_);
    v_parts_201_ =
        l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(v___x_200_);
    v___x_202_ = l_Lake_toUpperCamelCaseString___closed__0;
    v___x_203_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_197_, v___x_200_, v___x_199_, v_parts_201_, v___x_202_);
    leanh::lean_dec_ref_known(v___x_200_, 3);
    leanh::lean_dec_ref(v_str_197_);
    v___x_204_ = lean_array_to_list(v___x_203_);
    v___x_205_ = l_Lake_toUpperCamelCaseString___closed__1;
    v___x_206_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v___x_205_, v___x_204_);
    leanh::lean_dec(v___x_204_);
    return v___x_206_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(
    mut v_str_207_: *mut leanh::LeanObject,
    mut v___x_208_: *mut leanh::LeanObject,
    mut v___x_209_: *mut leanh::LeanObject,
    mut v_inst_210_: *mut leanh::LeanObject,
    mut v_R_211_: *mut leanh::LeanObject,
    mut v_a_212_: *mut leanh::LeanObject,
    mut v_b_213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_214_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_207_, v___x_208_, v___x_209_, v_a_212_, v_b_213_);
    return v___x_214_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___boxed(
    mut v_str_215_: *mut leanh::LeanObject,
    mut v___x_216_: *mut leanh::LeanObject,
    mut v___x_217_: *mut leanh::LeanObject,
    mut v_inst_218_: *mut leanh::LeanObject,
    mut v_R_219_: *mut leanh::LeanObject,
    mut v_a_220_: *mut leanh::LeanObject,
    mut v_b_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_222_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(v_str_215_, v___x_216_, v___x_217_, v_inst_218_, v_R_219_, v_a_220_, v_b_221_);
    leanh::lean_dec_ref(v___x_216_);
    leanh::lean_dec_ref(v_str_215_);
    return v_res_222_;
}
pub unsafe fn l_Lake_toUpperCamelCase(
    mut v_name_223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_name_223_) == 1 {
        let mut v_pre_224_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_225_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_224_ = leanh::lean_ctor_get(v_name_223_, 0);
        leanh::lean_inc(v_pre_224_);
        v_str_225_ = leanh::lean_ctor_get(v_name_223_, 1);
        leanh::lean_inc_ref(v_str_225_);
        leanh::lean_dec_ref_known(v_name_223_, 2);
        v___x_226_ = l_Lake_toUpperCamelCase(v_pre_224_);
        v___x_227_ = l_Lake_toUpperCamelCaseString(v_str_225_);
        v___x_228_ = l_Lean_Name_str___override(v___x_226_, v___x_227_);
        return v___x_228_;
    } else {
        return v_name_223_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Casing(builtin: u8) -> *mut leanh::LeanObject {
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
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Casing(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Casing(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Casing(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Casing(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Casing(builtin);
}