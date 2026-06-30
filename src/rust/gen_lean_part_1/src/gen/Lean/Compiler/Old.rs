// Lean compiler output
// Module: Lean.Compiler.Old
// Imports: Lean.Environment Init.Data.String.TakeDrop
use crate::ffi::{
    lean_array_mk, lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_string_append, lean_string_dec_eq,
    lean_string_memcmp, lean_string_utf8_byte_size, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::l_Lean_Name_str___override;
use crate::r#gen::Lean::Environment::{
    initialize_Lean_Environment, l_Lean_Environment_findAsync_x3f,
    runtime_initialize_Lean_Environment,
};
pub static l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [95, 101, 108, 97, 109, 98, 100, 97, 95, 0],
};
static mut l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_isEagerLambdaLiftingName___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [95, 101, 108, 97, 109, 98, 100, 97, 0],
};
static mut l_Lean_Compiler_isEagerLambdaLiftingName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_isEagerLambdaLiftingName___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_isEagerLambdaLiftingName___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_isEagerLambdaLiftingName___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_getDeclNamesForCodeGen___closed__0_value: leanh::LeanArrayObject<
    0,
> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_getDeclNamesForCodeGen___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_getDeclNamesForCodeGen___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_Compiler_checkIsDefinition___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__1_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0],
    };
static mut l_Lean_Compiler_checkIsDefinition___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__2_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116,
            105, 111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_checkIsDefinition___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__3_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            85, 110, 107, 110, 111, 119, 110, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
            110, 32, 96, 0,
        ],
    };
static mut l_Lean_Compiler_checkIsDefinition___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__4_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [96, 0],
    };
static mut l_Lean_Compiler_checkIsDefinition___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_mkUnsafeRecName___closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [95, 117, 110, 115, 97, 102, 101, 95, 114, 101, 99, 0],
    };
static mut l_Lean_Compiler_mkUnsafeRecName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_mkUnsafeRecName___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_mkEagerLambdaLiftingName(
    mut v_n_123_: *mut leanh::LeanObject,
    mut v_idx_124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_125_ = l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0;
    v___x_126_ = l_Nat_reprFast(v_idx_124_);
    v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
    leanh::lean_dec_ref(v___x_126_);
    v___x_128_ = l_Lean_Name_str___override(v_n_123_, v___x_127_);
    return v___x_128_;
}
pub unsafe fn _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_130_ = l_Lean_Compiler_isEagerLambdaLiftingName___closed__0;
    v___x_131_ = lean_string_utf8_byte_size(v___x_130_);
    return v___x_131_;
}
pub unsafe fn l_Lean_Compiler_isEagerLambdaLiftingName(
    mut v_x_132_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_pre_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: u8 = 0;
    let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_141_: u8 = 0;
    let mut v_pre_143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_132_) {
                1 => {
                    v_pre_133_ = leanh::lean_ctor_get(v_x_132_, 0);
                    v_str_134_ = leanh::lean_ctor_get(v_x_132_, 1);
                    v___x_135_ = l_Lean_Compiler_isEagerLambdaLiftingName___closed__0;
                    v___x_136_ = lean_string_utf8_byte_size(v_str_134_);
                    v___x_137_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_isEagerLambdaLiftingName___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_isEagerLambdaLiftingName___closed__1_once
                        ),
                        _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__1,
                    );
                    v___x_138_ = lean_nat_dec_le(v___x_137_, v___x_136_);
                    if v___x_138_ == 0 {
                        v_x_132_ = v_pre_133_;
                        state = 0;
                        continue;
                    } else {
                        v___x_140_ = leanh::lean_unsigned_to_nat(0);
                        v___x_141_ = lean_string_memcmp(
                            v_str_134_, v___x_135_, v___x_140_, v___x_140_, v___x_137_,
                        );
                        if v___x_141_ == 0 {
                            v_x_132_ = v_pre_133_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_141_;
                        }
                    }
                }
                2 => {
                    v_pre_143_ = leanh::lean_ctor_get(v_x_132_, 0);
                    v_x_132_ = v_pre_143_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_145_ = 0;
                    return v___x_145_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_isEagerLambdaLiftingName___boxed(
    mut v_x_146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_147_: u8 = 0;
    let mut v_r_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_147_ = l_Lean_Compiler_isEagerLambdaLiftingName(v_x_146_);
    leanh::lean_dec(v_x_146_);
    v_r_148_ = leanh::lean_box((v_res_147_) as usize);
    return v_r_148_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(
    mut v_sz_149_: usize,
    mut v_i_150_: usize,
    mut v_bs_151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_152_: u8 = 0;
    let mut v_v_153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: usize = 0;
    let mut v___x_159_: usize = 0;
    let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_152_ = lean_usize_dec_lt(v_i_150_, v_sz_149_);
                if v___x_152_ == 0 {
                    return v_bs_151_;
                } else {
                    v_v_153_ = lean_array_uget_borrowed(v_bs_151_, v_i_150_);
                    v_toConstantVal_154_ = leanh::lean_ctor_get(v_v_153_, 0);
                    v_name_155_ = leanh::lean_ctor_get(v_toConstantVal_154_, 0);
                    leanh::lean_inc(v_name_155_);
                    v___x_156_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_157_ = lean_array_uset(v_bs_151_, v_i_150_, v___x_156_);
                    v___x_158_ = 1usize;
                    v___x_159_ = lean_usize_add(v_i_150_, v___x_158_);
                    v___x_160_ = lean_array_uset(v_bs_x27_157_, v_i_150_, v_name_155_);
                    v_i_150_ = v___x_159_;
                    v_bs_151_ = v___x_160_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0___boxed(
    mut v_sz_162_: *mut leanh::LeanObject,
    mut v_i_163_: *mut leanh::LeanObject,
    mut v_bs_164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_165_: usize = 0;
    let mut v_i_boxed_166_: usize = 0;
    let mut v_res_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_165_ = leanh::lean_unbox_usize(v_sz_162_);
    leanh::lean_dec(v_sz_162_);
    v_i_boxed_166_ = leanh::lean_unbox_usize(v_i_163_);
    leanh::lean_dec(v_i_163_);
    v_res_167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(v_sz_boxed_165_, v_i_boxed_166_, v_bs_164_);
    return v_res_167_;
}
pub unsafe fn l_Lean_Compiler_getDeclNamesForCodeGen(
    mut v_x_170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_170_) {
        1 => {
            let mut v_val_171_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_172_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_name_173_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_171_ = leanh::lean_ctor_get(v_x_170_, 0);
            leanh::lean_inc_ref(v_val_171_);
            leanh::lean_dec_ref_known(v_x_170_, 1);
            v_toConstantVal_172_ = leanh::lean_ctor_get(v_val_171_, 0);
            leanh::lean_inc_ref(v_toConstantVal_172_);
            leanh::lean_dec_ref(v_val_171_);
            v_name_173_ = leanh::lean_ctor_get(v_toConstantVal_172_, 0);
            leanh::lean_inc(v_name_173_);
            leanh::lean_dec_ref(v_toConstantVal_172_);
            v___x_174_ = leanh::lean_unsigned_to_nat(1);
            v___x_175_ = lean_mk_empty_array_with_capacity(v___x_174_);
            v___x_176_ = lean_array_push(v___x_175_, v_name_173_);
            return v___x_176_;
        }
        3 => {
            let mut v_val_177_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_178_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_name_179_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_177_ = leanh::lean_ctor_get(v_x_170_, 0);
            leanh::lean_inc_ref(v_val_177_);
            leanh::lean_dec_ref_known(v_x_170_, 1);
            v_toConstantVal_178_ = leanh::lean_ctor_get(v_val_177_, 0);
            leanh::lean_inc_ref(v_toConstantVal_178_);
            leanh::lean_dec_ref(v_val_177_);
            v_name_179_ = leanh::lean_ctor_get(v_toConstantVal_178_, 0);
            leanh::lean_inc(v_name_179_);
            leanh::lean_dec_ref(v_toConstantVal_178_);
            v___x_180_ = leanh::lean_unsigned_to_nat(1);
            v___x_181_ = lean_mk_empty_array_with_capacity(v___x_180_);
            v___x_182_ = lean_array_push(v___x_181_, v_name_179_);
            return v___x_182_;
        }
        0 => {
            let mut v_val_183_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_184_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_name_185_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_183_ = leanh::lean_ctor_get(v_x_170_, 0);
            leanh::lean_inc_ref(v_val_183_);
            leanh::lean_dec_ref_known(v_x_170_, 1);
            v_toConstantVal_184_ = leanh::lean_ctor_get(v_val_183_, 0);
            leanh::lean_inc_ref(v_toConstantVal_184_);
            leanh::lean_dec_ref(v_val_183_);
            v_name_185_ = leanh::lean_ctor_get(v_toConstantVal_184_, 0);
            leanh::lean_inc(v_name_185_);
            leanh::lean_dec_ref(v_toConstantVal_184_);
            v___x_186_ = leanh::lean_unsigned_to_nat(1);
            v___x_187_ = lean_mk_empty_array_with_capacity(v___x_186_);
            v___x_188_ = lean_array_push(v___x_187_, v_name_185_);
            return v___x_188_;
        }
        5 => {
            let mut v_defns_189_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_sz_191_: usize = 0;
            let mut v___x_192_: usize = 0;
            let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_defns_189_ = leanh::lean_ctor_get(v_x_170_, 0);
            leanh::lean_inc(v_defns_189_);
            leanh::lean_dec_ref_known(v_x_170_, 1);
            v___x_190_ = lean_array_mk(v_defns_189_);
            v_sz_191_ = lean_array_size(v___x_190_);
            v___x_192_ = 0usize;
            v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(v_sz_191_, v___x_192_, v___x_190_);
            return v___x_193_;
        }
        _ => {
            let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_170_);
            v___x_194_ = l_Lean_Compiler_getDeclNamesForCodeGen___closed__0;
            return v___x_194_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_checkIsDefinition(
    mut v_env_201_: *mut leanh::LeanObject,
    mut v_n_202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: u8 = 0;
    let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_210_: u8 = 0;
    let mut v_kind_211_: u8 = 0;
    let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: u8 = 0;
    let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_221_: u8 = 0;
    let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: u8 = 0;
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_205_ = 0;
                leanh::lean_inc(v_n_202_);
                v___x_206_ = l_Lean_Environment_findAsync_x3f(v_env_201_, v_n_202_, v___x_205_);
                if leanh::lean_obj_tag(v___x_206_) == 1 {
                    v_val_207_ = leanh::lean_ctor_get(v___x_206_, 0);
                    v_isSharedCheck_221_ = (!leanh::lean_is_exclusive(v___x_206_)) as u8;
                    if v_isSharedCheck_221_ == 0 {
                        v___x_209_ = v___x_206_;
                        v_isShared_210_ = v_isSharedCheck_221_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_207_);
                        leanh::lean_dec(v___x_206_);
                        v___x_209_ = leanh::lean_box(0);
                        v_isShared_210_ = v_isSharedCheck_221_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_206_);
                    v___x_222_ = l_Lean_Compiler_checkIsDefinition___closed__3;
                    v___x_223_ = 1;
                    v___x_224_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_n_202_, v___x_223_,
                    );
                    v___x_225_ = lean_string_append(v___x_222_, v___x_224_);
                    leanh::lean_dec_ref(v___x_224_);
                    v___x_226_ = l_Lean_Compiler_checkIsDefinition___closed__4;
                    v___x_227_ = lean_string_append(v___x_225_, v___x_226_);
                    v___x_228_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_228_, 0, v___x_227_);
                    return v___x_228_;
                }
            }
            1 => {
                v___x_204_ = l_Lean_Compiler_checkIsDefinition___closed__0;
                return v___x_204_;
            }
            2 => {
                v_kind_211_ = leanh::lean_ctor_get_uint8(
                    v_val_207_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec(v_val_207_);
                match v_kind_211_ {
                    0 => {
                        leanh::lean_del_object(v___x_209_);
                        leanh::lean_dec(v_n_202_);
                        state = 1;
                        continue;
                    }
                    3 => {
                        leanh::lean_del_object(v___x_209_);
                        leanh::lean_dec(v_n_202_);
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_212_ = l_Lean_Compiler_checkIsDefinition___closed__1;
                        v___x_213_ = 1;
                        v___x_214_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_n_202_, v___x_213_,
                            );
                        v___x_215_ = lean_string_append(v___x_212_, v___x_214_);
                        leanh::lean_dec_ref(v___x_214_);
                        v___x_216_ = l_Lean_Compiler_checkIsDefinition___closed__2;
                        v___x_217_ = lean_string_append(v___x_215_, v___x_216_);
                        if v_isShared_210_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_209_, 0);
                            leanh::lean_ctor_set(v___x_209_, 0, v___x_217_);
                            v___x_219_ = v___x_209_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_220_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
                            v___x_219_ = v_reuseFailAlloc_220_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_219_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_mkUnsafeRecName(
    mut v_declName_230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_231_ = l_Lean_Compiler_mkUnsafeRecName___closed__0;
    v___x_232_ = l_Lean_Name_str___override(v_declName_230_, v___x_231_);
    return v___x_232_;
}
pub unsafe fn l_Lean_Compiler_isUnsafeRecName_x3f(
    mut v_x_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_233_) == 1 {
        let mut v_pre_234_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_235_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_237_: u8 = 0;
        v_pre_234_ = leanh::lean_ctor_get(v_x_233_, 0);
        v_str_235_ = leanh::lean_ctor_get(v_x_233_, 1);
        v___x_236_ = l_Lean_Compiler_mkUnsafeRecName___closed__0;
        v___x_237_ = lean_string_dec_eq(v_str_235_, v___x_236_);
        if v___x_237_ == 0 {
            let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_238_ = leanh::lean_box(0);
            return v___x_238_;
        } else {
            let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_pre_234_);
            v___x_239_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_239_, 0, v_pre_234_);
            return v___x_239_;
        }
    } else {
        let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_240_ = leanh::lean_box(0);
        return v___x_240_;
    }
}
pub unsafe fn l_Lean_Compiler_isUnsafeRecName_x3f___boxed(
    mut v_x_241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_242_ = l_Lean_Compiler_isUnsafeRecName_x3f(v_x_241_);
    leanh::lean_dec(v_x_241_);
    return v_res_242_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_Old(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_Old(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_Old(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Old(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_Old(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_Old(builtin);
}