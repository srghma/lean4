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
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_isEagerLambdaLiftingName___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_isEagerLambdaLiftingName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_isEagerLambdaLiftingName___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_isEagerLambdaLiftingName___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_isEagerLambdaLiftingName___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_getDeclNamesForCodeGen___closed__0_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_getDeclNamesForCodeGen___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_getDeclNamesForCodeGen___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Compiler_checkIsDefinition___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__1_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_checkIsDefinition___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__2_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_checkIsDefinition___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__3_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_checkIsDefinition___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__4_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_checkIsDefinition___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_mkUnsafeRecName___closed__0_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_mkUnsafeRecName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_mkUnsafeRecName___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_mkEagerLambdaLiftingName(
    mut v_n_123_: *mut crate::leanh::LeanObject,
    mut v_idx_124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_125_ = l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0;
    v___x_126_ = l_Nat_reprFast(v_idx_124_);
    v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
    crate::leanh::lean_dec_ref(v___x_126_);
    v___x_128_ = l_Lean_Name_str___override(v_n_123_, v___x_127_);
    return v___x_128_;
}
pub unsafe fn _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_130_ = l_Lean_Compiler_isEagerLambdaLiftingName___closed__0;
    v___x_131_ = lean_string_utf8_byte_size(v___x_130_);
    return v___x_131_;
}
pub unsafe fn l_Lean_Compiler_isEagerLambdaLiftingName(
    mut v_x_132_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_pre_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: u8 = 0;
    let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_141_: u8 = 0;
    let mut v_pre_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_132_) {
                1 => {
                    v_pre_133_ = crate::leanh::lean_ctor_get(v_x_132_, 0);
                    v_str_134_ = crate::leanh::lean_ctor_get(v_x_132_, 1);
                    v___x_135_ = l_Lean_Compiler_isEagerLambdaLiftingName___closed__0;
                    v___x_136_ = lean_string_utf8_byte_size(v_str_134_);
                    v___x_137_ = crate::leanh::lean_obj_once(
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
                        v___x_140_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    v_pre_143_ = crate::leanh::lean_ctor_get(v_x_132_, 0);
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
    mut v_x_146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_147_: u8 = 0;
    let mut v_r_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_147_ = l_Lean_Compiler_isEagerLambdaLiftingName(v_x_146_);
    crate::leanh::lean_dec(v_x_146_);
    v_r_148_ = crate::leanh::lean_box((v_res_147_) as usize);
    return v_r_148_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(
    mut v_sz_149_: usize,
    mut v_i_150_: usize,
    mut v_bs_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_152_: u8 = 0;
    let mut v_v_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: usize = 0;
    let mut v___x_159_: usize = 0;
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_152_ = lean_usize_dec_lt(v_i_150_, v_sz_149_);
                if v___x_152_ == 0 {
                    return v_bs_151_;
                } else {
                    v_v_153_ = lean_array_uget_borrowed(v_bs_151_, v_i_150_);
                    v_toConstantVal_154_ = crate::leanh::lean_ctor_get(v_v_153_, 0);
                    v_name_155_ = crate::leanh::lean_ctor_get(v_toConstantVal_154_, 0);
                    crate::leanh::lean_inc(v_name_155_);
                    v___x_156_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_162_: *mut crate::leanh::LeanObject,
    mut v_i_163_: *mut crate::leanh::LeanObject,
    mut v_bs_164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_165_: usize = 0;
    let mut v_i_boxed_166_: usize = 0;
    let mut v_res_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_165_ = crate::leanh::lean_unbox_usize(v_sz_162_);
    crate::leanh::lean_dec(v_sz_162_);
    v_i_boxed_166_ = crate::leanh::lean_unbox_usize(v_i_163_);
    crate::leanh::lean_dec(v_i_163_);
    v_res_167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(v_sz_boxed_165_, v_i_boxed_166_, v_bs_164_);
    return v_res_167_;
}
pub unsafe fn l_Lean_Compiler_getDeclNamesForCodeGen(
    mut v_x_170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_170_) {
        1 => {
            let mut v_val_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_name_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_171_ = crate::leanh::lean_ctor_get(v_x_170_, 0);
            crate::leanh::lean_inc_ref(v_val_171_);
            crate::leanh::lean_dec_ref_known(v_x_170_, 1);
            v_toConstantVal_172_ = crate::leanh::lean_ctor_get(v_val_171_, 0);
            crate::leanh::lean_inc_ref(v_toConstantVal_172_);
            crate::leanh::lean_dec_ref(v_val_171_);
            v_name_173_ = crate::leanh::lean_ctor_get(v_toConstantVal_172_, 0);
            crate::leanh::lean_inc(v_name_173_);
            crate::leanh::lean_dec_ref(v_toConstantVal_172_);
            v___x_174_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_175_ = lean_mk_empty_array_with_capacity(v___x_174_);
            v___x_176_ = lean_array_push(v___x_175_, v_name_173_);
            return v___x_176_;
        }
        3 => {
            let mut v_val_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_name_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_177_ = crate::leanh::lean_ctor_get(v_x_170_, 0);
            crate::leanh::lean_inc_ref(v_val_177_);
            crate::leanh::lean_dec_ref_known(v_x_170_, 1);
            v_toConstantVal_178_ = crate::leanh::lean_ctor_get(v_val_177_, 0);
            crate::leanh::lean_inc_ref(v_toConstantVal_178_);
            crate::leanh::lean_dec_ref(v_val_177_);
            v_name_179_ = crate::leanh::lean_ctor_get(v_toConstantVal_178_, 0);
            crate::leanh::lean_inc(v_name_179_);
            crate::leanh::lean_dec_ref(v_toConstantVal_178_);
            v___x_180_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_181_ = lean_mk_empty_array_with_capacity(v___x_180_);
            v___x_182_ = lean_array_push(v___x_181_, v_name_179_);
            return v___x_182_;
        }
        0 => {
            let mut v_val_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_name_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_183_ = crate::leanh::lean_ctor_get(v_x_170_, 0);
            crate::leanh::lean_inc_ref(v_val_183_);
            crate::leanh::lean_dec_ref_known(v_x_170_, 1);
            v_toConstantVal_184_ = crate::leanh::lean_ctor_get(v_val_183_, 0);
            crate::leanh::lean_inc_ref(v_toConstantVal_184_);
            crate::leanh::lean_dec_ref(v_val_183_);
            v_name_185_ = crate::leanh::lean_ctor_get(v_toConstantVal_184_, 0);
            crate::leanh::lean_inc(v_name_185_);
            crate::leanh::lean_dec_ref(v_toConstantVal_184_);
            v___x_186_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_187_ = lean_mk_empty_array_with_capacity(v___x_186_);
            v___x_188_ = lean_array_push(v___x_187_, v_name_185_);
            return v___x_188_;
        }
        5 => {
            let mut v_defns_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_sz_191_: usize = 0;
            let mut v___x_192_: usize = 0;
            let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_defns_189_ = crate::leanh::lean_ctor_get(v_x_170_, 0);
            crate::leanh::lean_inc(v_defns_189_);
            crate::leanh::lean_dec_ref_known(v_x_170_, 1);
            v___x_190_ = lean_array_mk(v_defns_189_);
            v_sz_191_ = lean_array_size(v___x_190_);
            v___x_192_ = 0usize;
            v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(v_sz_191_, v___x_192_, v___x_190_);
            return v___x_193_;
        }
        _ => {
            let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_170_);
            v___x_194_ = l_Lean_Compiler_getDeclNamesForCodeGen___closed__0;
            return v___x_194_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_checkIsDefinition(
    mut v_env_201_: *mut crate::leanh::LeanObject,
    mut v_n_202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: u8 = 0;
    let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_210_: u8 = 0;
    let mut v_kind_211_: u8 = 0;
    let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: u8 = 0;
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_221_: u8 = 0;
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: u8 = 0;
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_205_ = 0;
                crate::leanh::lean_inc(v_n_202_);
                v___x_206_ = l_Lean_Environment_findAsync_x3f(v_env_201_, v_n_202_, v___x_205_);
                if crate::leanh::lean_obj_tag(v___x_206_) == 1 {
                    v_val_207_ = crate::leanh::lean_ctor_get(v___x_206_, 0);
                    v_isSharedCheck_221_ = (!crate::leanh::lean_is_exclusive(v___x_206_)) as u8;
                    if v_isSharedCheck_221_ == 0 {
                        v___x_209_ = v___x_206_;
                        v_isShared_210_ = v_isSharedCheck_221_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_207_);
                        crate::leanh::lean_dec(v___x_206_);
                        v___x_209_ = crate::leanh::lean_box(0);
                        v_isShared_210_ = v_isSharedCheck_221_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_206_);
                    v___x_222_ = l_Lean_Compiler_checkIsDefinition___closed__3;
                    v___x_223_ = 1;
                    v___x_224_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_n_202_, v___x_223_,
                    );
                    v___x_225_ = lean_string_append(v___x_222_, v___x_224_);
                    crate::leanh::lean_dec_ref(v___x_224_);
                    v___x_226_ = l_Lean_Compiler_checkIsDefinition___closed__4;
                    v___x_227_ = lean_string_append(v___x_225_, v___x_226_);
                    v___x_228_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_228_, 0, v___x_227_);
                    return v___x_228_;
                }
            }
            1 => {
                v___x_204_ = l_Lean_Compiler_checkIsDefinition___closed__0;
                return v___x_204_;
            }
            2 => {
                v_kind_211_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_207_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec(v_val_207_);
                match v_kind_211_ {
                    0 => {
                        crate::leanh::lean_del_object(v___x_209_);
                        crate::leanh::lean_dec(v_n_202_);
                        state = 1;
                        continue;
                    }
                    3 => {
                        crate::leanh::lean_del_object(v___x_209_);
                        crate::leanh::lean_dec(v_n_202_);
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
                        crate::leanh::lean_dec_ref(v___x_214_);
                        v___x_216_ = l_Lean_Compiler_checkIsDefinition___closed__2;
                        v___x_217_ = lean_string_append(v___x_215_, v___x_216_);
                        if v_isShared_210_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_209_, 0);
                            crate::leanh::lean_ctor_set(v___x_209_, 0, v___x_217_);
                            v___x_219_ = v___x_209_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_220_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
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
    mut v_declName_230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_231_ = l_Lean_Compiler_mkUnsafeRecName___closed__0;
    v___x_232_ = l_Lean_Name_str___override(v_declName_230_, v___x_231_);
    return v___x_232_;
}
pub unsafe fn l_Lean_Compiler_isUnsafeRecName_x3f(
    mut v_x_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_233_) == 1 {
        let mut v_pre_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_237_: u8 = 0;
        v_pre_234_ = crate::leanh::lean_ctor_get(v_x_233_, 0);
        v_str_235_ = crate::leanh::lean_ctor_get(v_x_233_, 1);
        v___x_236_ = l_Lean_Compiler_mkUnsafeRecName___closed__0;
        v___x_237_ = lean_string_dec_eq(v_str_235_, v___x_236_);
        if v___x_237_ == 0 {
            let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_238_ = crate::leanh::lean_box(0);
            return v___x_238_;
        } else {
            let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_pre_234_);
            v___x_239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_239_, 0, v_pre_234_);
            return v___x_239_;
        }
    } else {
        let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_240_ = crate::leanh::lean_box(0);
        return v___x_240_;
    }
}
pub unsafe fn l_Lean_Compiler_isUnsafeRecName_x3f___boxed(
    mut v_x_241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_242_ = l_Lean_Compiler_isUnsafeRecName_x3f(v_x_241_);
    crate::leanh::lean_dec(v_x_241_);
    return v_res_242_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_Old(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_Old(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_Old(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Old(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_Old(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_Old(builtin);
}
