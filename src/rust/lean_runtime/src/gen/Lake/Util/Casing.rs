// Lean compiler output
// Module: Lake.Util.Casing
// Imports: Init.Data.String.Basic Init.Data.String.Modify Init.Data.String.Search Init.Data.Iterators.Consumers.Collect
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
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint32_add;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_sub, lean_string_utf8_byte_size, lean_uint32_dec_eq,
    lean_uint32_dec_le,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_toUpperCamelCaseString___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lake_toUpperCamelCaseString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_toUpperCamelCaseString___closed__0_value) as *mut LeanObject;
pub static l_Lake_toUpperCamelCaseString___closed__1_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_toUpperCamelCaseString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_toUpperCamelCaseString___closed__1_value) as *mut LeanObject;
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(
    mut v_s_117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
    v___x_118_ =
        l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___closed__0;
    return v___x_118_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0___boxed(
    mut v_s_119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_120_: *mut LeanObject = core::ptr::null_mut();
    v_res_120_ =
        l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(v_s_119_);
    lean_dec_ref(v_s_119_);
    return v_res_120_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(
    mut v_str_121_: *mut LeanObject,
    mut v___x_122_: *mut LeanObject,
    mut v___x_123_: *mut LeanObject,
    mut v_a_124_: *mut LeanObject,
    mut v_b_125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_137_: u32 = 0;
    let mut v___x_138_: u32 = 0;
    let mut v___x_139_: u8 = 0;
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_141_: u32 = 0;
    let mut v___x_142_: u8 = 0;
    let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_144_: u32 = 0;
    let mut v___x_145_: u32 = 0;
    let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currPos_147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_151_: u8 = 0;
    let mut v___y_153_: u8 = 0;
    let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_171_: u8 = 0;
    let mut v___x_172_: u32 = 0;
    let mut v___x_173_: u32 = 0;
    let mut v___x_174_: u8 = 0;
    let mut v___x_175_: u32 = 0;
    let mut v___x_176_: u8 = 0;
    let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_178_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_124_) == 0 {
                    v_currPos_147_ = lean_ctor_get(v_a_124_, 0);
                    v_searcher_148_ = lean_ctor_get(v_a_124_, 1);
                    v_isSharedCheck_178_ = (!lean_is_exclusive(v_a_124_)) as u8;
                    if v_isSharedCheck_178_ == 0 {
                        v___x_150_ = v_a_124_;
                        v_isShared_151_ = v_isSharedCheck_178_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_searcher_148_);
                        lean_inc(v_currPos_147_);
                        lean_dec(v_a_124_);
                        v___x_150_ = lean_box(0);
                        v_isShared_151_ = v_isSharedCheck_178_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_123_);
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
                lean_dec(v_endExclusive_134_);
                lean_dec(v_startInclusive_133_);
                v___x_136_ = lean_unsigned_to_nat(0);
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
                v_startInclusive_168_ = lean_ctor_get(v___x_122_, 1);
                v_endExclusive_169_ = lean_ctor_get(v___x_122_, 2);
                v___x_170_ = lean_nat_sub(v_endExclusive_169_, v_startInclusive_168_);
                v___x_171_ = lean_nat_dec_eq(v_searcher_148_, v___x_170_);
                lean_dec(v___x_170_);
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
                    lean_del_object(v___x_150_);
                    lean_dec(v_searcher_148_);
                    v___x_177_ = lean_box(1);
                    lean_inc(v___x_123_);
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
                    lean_dec(v_searcher_148_);
                    if v_isShared_151_ == 0 {
                        lean_ctor_set(v___x_150_, 1, v___x_154_);
                        v___x_156_ = v___x_150_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_158_, 0, v_currPos_147_);
                        lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_154_);
                        v___x_156_ = v_reuseFailAlloc_158_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_159_ = lean_string_utf8_next_fast(v_str_121_, v_searcher_148_);
                    v___x_160_ = lean_nat_sub(v___x_159_, v_searcher_148_);
                    v___x_161_ = lean_nat_add(v_searcher_148_, v___x_160_);
                    lean_dec(v___x_160_);
                    v_slice_162_ =
                        l_String_Slice_subslice_x21(v___x_122_, v_currPos_147_, v_searcher_148_);
                    lean_inc(v___x_161_);
                    if v_isShared_151_ == 0 {
                        lean_ctor_set(v___x_150_, 1, v___x_161_);
                        lean_ctor_set(v___x_150_, 0, v___x_161_);
                        v_nextIt_164_ = v___x_150_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_161_);
                        lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_161_);
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
                v_startInclusive_165_ = lean_ctor_get(v_slice_162_, 0);
                lean_inc(v_startInclusive_165_);
                v_endExclusive_166_ = lean_ctor_get(v_slice_162_, 1);
                lean_inc(v_endExclusive_166_);
                lean_dec_ref(v_slice_162_);
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
    mut v_str_179_: *mut LeanObject,
    mut v___x_180_: *mut LeanObject,
    mut v___x_181_: *mut LeanObject,
    mut v_a_182_: *mut LeanObject,
    mut v_b_183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_184_: *mut LeanObject = core::ptr::null_mut();
    v_res_184_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_179_, v___x_180_, v___x_181_, v_a_182_, v_b_183_);
    lean_dec_ref(v___x_180_);
    lean_dec_ref(v_str_179_);
    return v_res_184_;
}
pub unsafe fn l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(
    mut v_x_185_: *mut LeanObject,
    mut v_x_186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_186_) == 0 {
                    return v_x_185_;
                } else {
                    v_head_187_ = lean_ctor_get(v_x_186_, 0);
                    v_tail_188_ = lean_ctor_get(v_x_186_, 1);
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
    mut v_x_191_: *mut LeanObject,
    mut v_x_192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_193_: *mut LeanObject = core::ptr::null_mut();
    v_res_193_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v_x_191_, v_x_192_);
    lean_dec(v_x_192_);
    return v_res_193_;
}
pub unsafe fn l_Lake_toUpperCamelCaseString(mut v_str_197_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parts_201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
    v___x_198_ = lean_unsigned_to_nat(0);
    v___x_199_ = lean_string_utf8_byte_size(v_str_197_);
    lean_inc_ref(v_str_197_);
    v___x_200_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_200_, 0, v_str_197_);
    lean_ctor_set(v___x_200_, 1, v___x_198_);
    lean_ctor_set(v___x_200_, 2, v___x_199_);
    v_parts_201_ =
        l_String_Slice_splitToSubslice___at___00Lake_toUpperCamelCaseString_spec__0(v___x_200_);
    v___x_202_ = l_Lake_toUpperCamelCaseString___closed__0;
    v___x_203_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_197_, v___x_200_, v___x_199_, v_parts_201_, v___x_202_);
    lean_dec_ref_known(v___x_200_, 3);
    lean_dec_ref(v_str_197_);
    v___x_204_ = lean_array_to_list(v___x_203_);
    v___x_205_ = l_Lake_toUpperCamelCaseString___closed__1;
    v___x_206_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v___x_205_, v___x_204_);
    lean_dec(v___x_204_);
    return v___x_206_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(
    mut v_str_207_: *mut LeanObject,
    mut v___x_208_: *mut LeanObject,
    mut v___x_209_: *mut LeanObject,
    mut v_inst_210_: *mut LeanObject,
    mut v_R_211_: *mut LeanObject,
    mut v_a_212_: *mut LeanObject,
    mut v_b_213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    v___x_214_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(v_str_207_, v___x_208_, v___x_209_, v_a_212_, v_b_213_);
    return v___x_214_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___boxed(
    mut v_str_215_: *mut LeanObject,
    mut v___x_216_: *mut LeanObject,
    mut v___x_217_: *mut LeanObject,
    mut v_inst_218_: *mut LeanObject,
    mut v_R_219_: *mut LeanObject,
    mut v_a_220_: *mut LeanObject,
    mut v_b_221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_222_: *mut LeanObject = core::ptr::null_mut();
    v_res_222_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(v_str_215_, v___x_216_, v___x_217_, v_inst_218_, v_R_219_, v_a_220_, v_b_221_);
    lean_dec_ref(v___x_216_);
    lean_dec_ref(v_str_215_);
    return v_res_222_;
}
pub unsafe fn l_Lake_toUpperCamelCase(mut v_name_223_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_name_223_) == 1 {
        let mut v_pre_224_: *mut LeanObject = core::ptr::null_mut();
        let mut v_str_225_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
        v_pre_224_ = lean_ctor_get(v_name_223_, 0);
        lean_inc(v_pre_224_);
        v_str_225_ = lean_ctor_get(v_name_223_, 1);
        lean_inc_ref(v_str_225_);
        lean_dec_ref_known(v_name_223_, 2);
        v___x_226_ = l_Lake_toUpperCamelCase(v_pre_224_);
        v___x_227_ = l_Lake_toUpperCamelCaseString(v_str_225_);
        v___x_228_ = l_Lean_Name_str___override(v___x_226_, v___x_227_);
        return v___x_228_;
    } else {
        return v_name_223_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Casing(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Casing(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Casing(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Casing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Casing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_Casing(builtin);
}
