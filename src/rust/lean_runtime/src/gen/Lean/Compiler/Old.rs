// Lean compiler output
// Module: Lean.Compiler.Old
// Imports: Lean.Environment Init.Data.String.TakeDrop
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_mk, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_string_dec_eq, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_isEagerLambdaLiftingName___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_isEagerLambdaLiftingName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_isEagerLambdaLiftingName___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_isEagerLambdaLiftingName___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_isEagerLambdaLiftingName___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_getDeclNamesForCodeGen___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Compiler_getDeclNamesForCodeGen___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_getDeclNamesForCodeGen___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Compiler_checkIsDefinition___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__1_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_checkIsDefinition___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__2_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_checkIsDefinition___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__2_value) as *mut LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__3_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_checkIsDefinition___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__3_value) as *mut LeanObject;
pub static l_Lean_Compiler_checkIsDefinition___closed__4_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_checkIsDefinition___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_checkIsDefinition___closed__4_value) as *mut LeanObject;
pub static l_Lean_Compiler_mkUnsafeRecName___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_mkUnsafeRecName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_mkUnsafeRecName___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_Compiler_mkEagerLambdaLiftingName(
    mut v_n_123_: *mut LeanObject,
    mut v_idx_124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
    v___x_125_ = l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0;
    v___x_126_ = l_Nat_reprFast(v_idx_124_);
    v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
    lean_dec_ref(v___x_126_);
    v___x_128_ = l_Lean_Name_str___override(v_n_123_, v___x_127_);
    return v___x_128_;
}
pub unsafe fn _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__1() -> *mut LeanObject {
    let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
    v___x_130_ = l_Lean_Compiler_isEagerLambdaLiftingName___closed__0;
    v___x_131_ = lean_string_utf8_byte_size(v___x_130_);
    return v___x_131_;
}
pub unsafe fn l_Lean_Compiler_isEagerLambdaLiftingName(mut v_x_132_: *mut LeanObject) -> u8 {
    let mut v_pre_133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_138_: u8 = 0;
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_141_: u8 = 0;
    let mut v_pre_143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_132_) {
                1 => {
                    v_pre_133_ = lean_ctor_get(v_x_132_, 0);
                    v_str_134_ = lean_ctor_get(v_x_132_, 1);
                    v___x_135_ = l_Lean_Compiler_isEagerLambdaLiftingName___closed__0;
                    v___x_136_ = lean_string_utf8_byte_size(v_str_134_);
                    v___x_137_ = lean_obj_once(
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
                        v___x_140_ = lean_unsigned_to_nat(0);
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
                    v_pre_143_ = lean_ctor_get(v_x_132_, 0);
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
    mut v_x_146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_147_: u8 = 0;
    let mut v_r_148_: *mut LeanObject = core::ptr::null_mut();
    v_res_147_ = l_Lean_Compiler_isEagerLambdaLiftingName(v_x_146_);
    lean_dec(v_x_146_);
    v_r_148_ = lean_box((v_res_147_) as usize);
    return v_r_148_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(
    mut v_sz_149_: usize,
    mut v_i_150_: usize,
    mut v_bs_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_152_: u8 = 0;
    let mut v_v_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_158_: usize = 0;
    let mut v___x_159_: usize = 0;
    let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_152_ = lean_usize_dec_lt(v_i_150_, v_sz_149_);
                if v___x_152_ == 0 {
                    return v_bs_151_;
                } else {
                    v_v_153_ = lean_array_uget_borrowed(v_bs_151_, v_i_150_);
                    v_toConstantVal_154_ = lean_ctor_get(v_v_153_, 0);
                    v_name_155_ = lean_ctor_get(v_toConstantVal_154_, 0);
                    lean_inc(v_name_155_);
                    v___x_156_ = lean_unsigned_to_nat(0);
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
    mut v_sz_162_: *mut LeanObject,
    mut v_i_163_: *mut LeanObject,
    mut v_bs_164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_165_: usize = 0;
    let mut v_i_boxed_166_: usize = 0;
    let mut v_res_167_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_165_ = lean_unbox_usize(v_sz_162_);
    lean_dec(v_sz_162_);
    v_i_boxed_166_ = lean_unbox_usize(v_i_163_);
    lean_dec(v_i_163_);
    v_res_167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(v_sz_boxed_165_, v_i_boxed_166_, v_bs_164_);
    return v_res_167_;
}
pub unsafe fn l_Lean_Compiler_getDeclNamesForCodeGen(
    mut v_x_170_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_170_) {
        1 => {
            let mut v_val_171_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_172_: *mut LeanObject = core::ptr::null_mut();
            let mut v_name_173_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
            v_val_171_ = lean_ctor_get(v_x_170_, 0);
            lean_inc_ref(v_val_171_);
            lean_dec_ref_known(v_x_170_, 1);
            v_toConstantVal_172_ = lean_ctor_get(v_val_171_, 0);
            lean_inc_ref(v_toConstantVal_172_);
            lean_dec_ref(v_val_171_);
            v_name_173_ = lean_ctor_get(v_toConstantVal_172_, 0);
            lean_inc(v_name_173_);
            lean_dec_ref(v_toConstantVal_172_);
            v___x_174_ = lean_unsigned_to_nat(1);
            v___x_175_ = lean_mk_empty_array_with_capacity(v___x_174_);
            v___x_176_ = lean_array_push(v___x_175_, v_name_173_);
            return v___x_176_;
        }
        3 => {
            let mut v_val_177_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_178_: *mut LeanObject = core::ptr::null_mut();
            let mut v_name_179_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
            v_val_177_ = lean_ctor_get(v_x_170_, 0);
            lean_inc_ref(v_val_177_);
            lean_dec_ref_known(v_x_170_, 1);
            v_toConstantVal_178_ = lean_ctor_get(v_val_177_, 0);
            lean_inc_ref(v_toConstantVal_178_);
            lean_dec_ref(v_val_177_);
            v_name_179_ = lean_ctor_get(v_toConstantVal_178_, 0);
            lean_inc(v_name_179_);
            lean_dec_ref(v_toConstantVal_178_);
            v___x_180_ = lean_unsigned_to_nat(1);
            v___x_181_ = lean_mk_empty_array_with_capacity(v___x_180_);
            v___x_182_ = lean_array_push(v___x_181_, v_name_179_);
            return v___x_182_;
        }
        0 => {
            let mut v_val_183_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_184_: *mut LeanObject = core::ptr::null_mut();
            let mut v_name_185_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
            v_val_183_ = lean_ctor_get(v_x_170_, 0);
            lean_inc_ref(v_val_183_);
            lean_dec_ref_known(v_x_170_, 1);
            v_toConstantVal_184_ = lean_ctor_get(v_val_183_, 0);
            lean_inc_ref(v_toConstantVal_184_);
            lean_dec_ref(v_val_183_);
            v_name_185_ = lean_ctor_get(v_toConstantVal_184_, 0);
            lean_inc(v_name_185_);
            lean_dec_ref(v_toConstantVal_184_);
            v___x_186_ = lean_unsigned_to_nat(1);
            v___x_187_ = lean_mk_empty_array_with_capacity(v___x_186_);
            v___x_188_ = lean_array_push(v___x_187_, v_name_185_);
            return v___x_188_;
        }
        5 => {
            let mut v_defns_189_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
            let mut v_sz_191_: usize = 0;
            let mut v___x_192_: usize = 0;
            let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
            v_defns_189_ = lean_ctor_get(v_x_170_, 0);
            lean_inc(v_defns_189_);
            lean_dec_ref_known(v_x_170_, 1);
            v___x_190_ = lean_array_mk(v_defns_189_);
            v_sz_191_ = lean_array_size(v___x_190_);
            v___x_192_ = 0usize;
            v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(v_sz_191_, v___x_192_, v___x_190_);
            return v___x_193_;
        }
        _ => {
            let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_170_);
            v___x_194_ = l_Lean_Compiler_getDeclNamesForCodeGen___closed__0;
            return v___x_194_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_checkIsDefinition(
    mut v_env_201_: *mut LeanObject,
    mut v_n_202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_205_: u8 = 0;
    let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_210_: u8 = 0;
    let mut v_kind_211_: u8 = 0;
    let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_213_: u8 = 0;
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_221_: u8 = 0;
    let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_223_: u8 = 0;
    let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_205_ = 0;
                lean_inc(v_n_202_);
                v___x_206_ = l_Lean_Environment_findAsync_x3f(v_env_201_, v_n_202_, v___x_205_);
                if lean_obj_tag(v___x_206_) == 1 {
                    v_val_207_ = lean_ctor_get(v___x_206_, 0);
                    v_isSharedCheck_221_ = (!lean_is_exclusive(v___x_206_)) as u8;
                    if v_isSharedCheck_221_ == 0 {
                        v___x_209_ = v___x_206_;
                        v_isShared_210_ = v_isSharedCheck_221_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_207_);
                        lean_dec(v___x_206_);
                        v___x_209_ = lean_box(0);
                        v_isShared_210_ = v_isSharedCheck_221_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_206_);
                    v___x_222_ = l_Lean_Compiler_checkIsDefinition___closed__3;
                    v___x_223_ = 1;
                    v___x_224_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_n_202_, v___x_223_,
                    );
                    v___x_225_ = lean_string_append(v___x_222_, v___x_224_);
                    lean_dec_ref(v___x_224_);
                    v___x_226_ = l_Lean_Compiler_checkIsDefinition___closed__4;
                    v___x_227_ = lean_string_append(v___x_225_, v___x_226_);
                    v___x_228_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_228_, 0, v___x_227_);
                    return v___x_228_;
                }
            }
            1 => {
                v___x_204_ = l_Lean_Compiler_checkIsDefinition___closed__0;
                return v___x_204_;
            }
            2 => {
                v_kind_211_ = lean_ctor_get_uint8(
                    v_val_207_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec(v_val_207_);
                match v_kind_211_ {
                    0 => {
                        lean_del_object(v___x_209_);
                        lean_dec(v_n_202_);
                        state = 1;
                        continue;
                    }
                    3 => {
                        lean_del_object(v___x_209_);
                        lean_dec(v_n_202_);
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
                        lean_dec_ref(v___x_214_);
                        v___x_216_ = l_Lean_Compiler_checkIsDefinition___closed__2;
                        v___x_217_ = lean_string_append(v___x_215_, v___x_216_);
                        if v_isShared_210_ == 0 {
                            lean_ctor_set_tag(v___x_209_, 0);
                            lean_ctor_set(v___x_209_, 0, v___x_217_);
                            v___x_219_ = v___x_209_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
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
    mut v_declName_230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    v___x_231_ = l_Lean_Compiler_mkUnsafeRecName___closed__0;
    v___x_232_ = l_Lean_Name_str___override(v_declName_230_, v___x_231_);
    return v___x_232_;
}
pub unsafe fn l_Lean_Compiler_isUnsafeRecName_x3f(
    mut v_x_233_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_233_) == 1 {
        let mut v_pre_234_: *mut LeanObject = core::ptr::null_mut();
        let mut v_str_235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_237_: u8 = 0;
        v_pre_234_ = lean_ctor_get(v_x_233_, 0);
        v_str_235_ = lean_ctor_get(v_x_233_, 1);
        v___x_236_ = l_Lean_Compiler_mkUnsafeRecName___closed__0;
        v___x_237_ = lean_string_dec_eq(v_str_235_, v___x_236_);
        if v___x_237_ == 0 {
            let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
            v___x_238_ = lean_box(0);
            return v___x_238_;
        } else {
            let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_pre_234_);
            v___x_239_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_239_, 0, v_pre_234_);
            return v___x_239_;
        }
    } else {
        let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
        v___x_240_ = lean_box(0);
        return v___x_240_;
    }
}
pub unsafe fn l_Lean_Compiler_isUnsafeRecName_x3f___boxed(
    mut v_x_241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_242_: *mut LeanObject = core::ptr::null_mut();
    v_res_242_ = l_Lean_Compiler_isUnsafeRecName_x3f(v_x_241_);
    lean_dec(v_x_241_);
    return v_res_242_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_Old(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_Old(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_Old(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Old(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_Old(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_Old(builtin);
}
