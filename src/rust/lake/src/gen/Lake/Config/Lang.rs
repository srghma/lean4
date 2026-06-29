// Lean compiler output
// Module: Lake.Config.Lang
// Imports: Init.Data.ToString.Basic
use crate::ffi::{lean_nat_dec_eq, lean_nat_dec_le, lean_nat_to_int, lean_string_dec_eq};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
pub static l_Lake_instReprConfigLang_repr___closed__0_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 67, 111, 110, 102, 105, 103, 76, 97, 110, 103, 46, 108, 101, 97,
            110, 0,
        ],
    };
static mut l_Lake_instReprConfigLang_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprConfigLang_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprConfigLang_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprConfigLang_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprConfigLang_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprConfigLang_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprConfigLang_repr___closed__2_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 67, 111, 110, 102, 105, 103, 76, 97, 110, 103, 46, 116, 111, 109,
            108, 0,
        ],
    };
static mut l_Lake_instReprConfigLang_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprConfigLang_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprConfigLang_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprConfigLang_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprConfigLang_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprConfigLang_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprConfigLang_repr___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprConfigLang_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprConfigLang_repr___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprConfigLang_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprConfigLang___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instReprConfigLang_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprConfigLang___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprConfigLang___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instReprConfigLang: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprConfigLang___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_ConfigLang_default: u8 = 0;
pub static mut l_Lake_instInhabitedConfigLang: u8 = 0;
pub static l_Lake_ConfigLang_ofString_x3f___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [108, 101, 97, 110, 0],
    };
static mut l_Lake_ConfigLang_ofString_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ConfigLang_ofString_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ConfigLang_ofString_x3f___closed__1_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 111, 109, 108, 0],
    };
static mut l_Lake_ConfigLang_ofString_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ConfigLang_ofString_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ConfigLang_ofString_x3f___closed__2_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_ConfigLang_ofString_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ConfigLang_ofString_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ConfigLang_ofString_x3f___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Lake_ConfigLang_ofString_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ConfigLang_ofString_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToStringConfigLang___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_ConfigLang_fileExtension___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToStringConfigLang___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToStringConfigLang___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToStringConfigLang: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToStringConfigLang___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_ConfigLang_ctorIdx(mut v_x_140_: u8) -> *mut crate::leanh::LeanObject {
    if v_x_140_ == 0 {
        let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_141_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_141_;
    } else {
        let mut v___x_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_142_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_142_;
    }
}
pub unsafe fn l_Lake_ConfigLang_ctorIdx___boxed(
    mut v_x_143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_144_: u8 = 0;
    let mut v_res_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_144_ = (crate::leanh::lean_unbox(v_x_143_) as u8);
    v_res_145_ = l_Lake_ConfigLang_ctorIdx(v_x_boxed_144_);
    return v_res_145_;
}
pub unsafe fn l_Lake_ConfigLang_toCtorIdx(mut v_x_146_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_147_ = l_Lake_ConfigLang_ctorIdx(v_x_146_);
    return v___x_147_;
}
pub unsafe fn l_Lake_ConfigLang_toCtorIdx___boxed(
    mut v_x_148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_149_: u8 = 0;
    let mut v_res_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_149_ = (crate::leanh::lean_unbox(v_x_148_) as u8);
    v_res_150_ = l_Lake_ConfigLang_toCtorIdx(v_x_4__boxed_149_);
    return v_res_150_;
}
pub unsafe fn l_Lake_ConfigLang_ctorElim___redArg(
    mut v_k_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_151_);
    return v_k_151_;
}
pub unsafe fn l_Lake_ConfigLang_ctorElim___redArg___boxed(
    mut v_k_152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_153_ = l_Lake_ConfigLang_ctorElim___redArg(v_k_152_);
    crate::leanh::lean_dec(v_k_152_);
    return v_res_153_;
}
pub unsafe fn l_Lake_ConfigLang_ctorElim(
    mut v_motive_154_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_155_: *mut crate::leanh::LeanObject,
    mut v_t_156_: u8,
    mut v_h_157_: *mut crate::leanh::LeanObject,
    mut v_k_158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_158_);
    return v_k_158_;
}
pub unsafe fn l_Lake_ConfigLang_ctorElim___boxed(
    mut v_motive_159_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_160_: *mut crate::leanh::LeanObject,
    mut v_t_161_: *mut crate::leanh::LeanObject,
    mut v_h_162_: *mut crate::leanh::LeanObject,
    mut v_k_163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_164_: u8 = 0;
    let mut v_res_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_164_ = (crate::leanh::lean_unbox(v_t_161_) as u8);
    v_res_165_ = l_Lake_ConfigLang_ctorElim(
        v_motive_159_,
        v_ctorIdx_160_,
        v_t_boxed_164_,
        v_h_162_,
        v_k_163_,
    );
    crate::leanh::lean_dec(v_k_163_);
    crate::leanh::lean_dec(v_ctorIdx_160_);
    return v_res_165_;
}
pub unsafe fn l_Lake_ConfigLang_lean_elim___redArg(
    mut v_lean_166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_lean_166_);
    return v_lean_166_;
}
pub unsafe fn l_Lake_ConfigLang_lean_elim___redArg___boxed(
    mut v_lean_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_168_ = l_Lake_ConfigLang_lean_elim___redArg(v_lean_167_);
    crate::leanh::lean_dec(v_lean_167_);
    return v_res_168_;
}
pub unsafe fn l_Lake_ConfigLang_lean_elim(
    mut v_motive_169_: *mut crate::leanh::LeanObject,
    mut v_t_170_: u8,
    mut v_h_171_: *mut crate::leanh::LeanObject,
    mut v_lean_172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_lean_172_);
    return v_lean_172_;
}
pub unsafe fn l_Lake_ConfigLang_lean_elim___boxed(
    mut v_motive_173_: *mut crate::leanh::LeanObject,
    mut v_t_174_: *mut crate::leanh::LeanObject,
    mut v_h_175_: *mut crate::leanh::LeanObject,
    mut v_lean_176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_177_: u8 = 0;
    let mut v_res_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_177_ = (crate::leanh::lean_unbox(v_t_174_) as u8);
    v_res_178_ = l_Lake_ConfigLang_lean_elim(v_motive_173_, v_t_boxed_177_, v_h_175_, v_lean_176_);
    crate::leanh::lean_dec(v_lean_176_);
    return v_res_178_;
}
pub unsafe fn l_Lake_ConfigLang_toml_elim___redArg(
    mut v_toml_179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_toml_179_);
    return v_toml_179_;
}
pub unsafe fn l_Lake_ConfigLang_toml_elim___redArg___boxed(
    mut v_toml_180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_181_ = l_Lake_ConfigLang_toml_elim___redArg(v_toml_180_);
    crate::leanh::lean_dec(v_toml_180_);
    return v_res_181_;
}
pub unsafe fn l_Lake_ConfigLang_toml_elim(
    mut v_motive_182_: *mut crate::leanh::LeanObject,
    mut v_t_183_: u8,
    mut v_h_184_: *mut crate::leanh::LeanObject,
    mut v_toml_185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_toml_185_);
    return v_toml_185_;
}
pub unsafe fn l_Lake_ConfigLang_toml_elim___boxed(
    mut v_motive_186_: *mut crate::leanh::LeanObject,
    mut v_t_187_: *mut crate::leanh::LeanObject,
    mut v_h_188_: *mut crate::leanh::LeanObject,
    mut v_toml_189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_190_: u8 = 0;
    let mut v_res_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_190_ = (crate::leanh::lean_unbox(v_t_187_) as u8);
    v_res_191_ = l_Lake_ConfigLang_toml_elim(v_motive_186_, v_t_boxed_190_, v_h_188_, v_toml_189_);
    crate::leanh::lean_dec(v_toml_189_);
    return v_res_191_;
}
pub unsafe fn _init_l_Lake_instReprConfigLang_repr___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_198_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_199_ = lean_nat_to_int(v___x_198_);
    return v___x_199_;
}
pub unsafe fn _init_l_Lake_instReprConfigLang_repr___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_200_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_201_ = lean_nat_to_int(v___x_200_);
    return v___x_201_;
}
pub unsafe fn l_Lake_instReprConfigLang_repr(
    mut v_x_202_: u8,
    mut v_prec_203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_208_: u8 = 0;
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: u8 = 0;
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: u8 = 0;
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: u8 = 0;
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_x_202_ == 0 {
                    v___x_218_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_219_ = lean_nat_dec_le(v___x_218_, v_prec_203_);
                    if v___x_219_ == 0 {
                        v___x_220_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprConfigLang_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprConfigLang_repr___closed__4_once
                            ),
                            _init_l_Lake_instReprConfigLang_repr___closed__4,
                        );
                        v___y_205_ = v___x_220_;
                        state = 1;
                        continue;
                    } else {
                        v___x_221_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprConfigLang_repr___closed__5),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprConfigLang_repr___closed__5_once
                            ),
                            _init_l_Lake_instReprConfigLang_repr___closed__5,
                        );
                        v___y_205_ = v___x_221_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_222_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_223_ = lean_nat_dec_le(v___x_222_, v_prec_203_);
                    if v___x_223_ == 0 {
                        v___x_224_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprConfigLang_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprConfigLang_repr___closed__4_once
                            ),
                            _init_l_Lake_instReprConfigLang_repr___closed__4,
                        );
                        v___y_212_ = v___x_224_;
                        state = 2;
                        continue;
                    } else {
                        v___x_225_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprConfigLang_repr___closed__5),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprConfigLang_repr___closed__5_once
                            ),
                            _init_l_Lake_instReprConfigLang_repr___closed__5,
                        );
                        v___y_212_ = v___x_225_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_206_ = l_Lake_instReprConfigLang_repr___closed__1;
                crate::leanh::lean_inc(v___y_205_);
                v___x_207_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_207_, 0, v___y_205_);
                crate::leanh::lean_ctor_set(v___x_207_, 1, v___x_206_);
                v___x_208_ = 0;
                v___x_209_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_209_, 0, v___x_207_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_209_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_208_,
                );
                v___x_210_ = l_Repr_addAppParen(v___x_209_, v_prec_203_);
                return v___x_210_;
            }
            2 => {
                v___x_213_ = l_Lake_instReprConfigLang_repr___closed__3;
                crate::leanh::lean_inc(v___y_212_);
                v___x_214_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_214_, 0, v___y_212_);
                crate::leanh::lean_ctor_set(v___x_214_, 1, v___x_213_);
                v___x_215_ = 0;
                v___x_216_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_216_, 0, v___x_214_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_216_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_215_,
                );
                v___x_217_ = l_Repr_addAppParen(v___x_216_, v_prec_203_);
                return v___x_217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprConfigLang_repr___boxed(
    mut v_x_226_: *mut crate::leanh::LeanObject,
    mut v_prec_227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_121__boxed_228_: u8 = 0;
    let mut v_res_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_121__boxed_228_ = (crate::leanh::lean_unbox(v_x_226_) as u8);
    v_res_229_ = l_Lake_instReprConfigLang_repr(v_x_121__boxed_228_, v_prec_227_);
    crate::leanh::lean_dec(v_prec_227_);
    return v_res_229_;
}
pub unsafe fn l_Lake_ConfigLang_ofNat(mut v_n_232_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: u8 = 0;
    v___x_233_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_234_ = lean_nat_dec_le(v_n_232_, v___x_233_);
    if v___x_234_ == 0 {
        let mut v___x_235_: u8 = 0;
        v___x_235_ = 1;
        return v___x_235_;
    } else {
        let mut v___x_236_: u8 = 0;
        v___x_236_ = 0;
        return v___x_236_;
    }
}
pub unsafe fn l_Lake_ConfigLang_ofNat___boxed(
    mut v_n_237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_238_: u8 = 0;
    let mut v_r_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_238_ = l_Lake_ConfigLang_ofNat(v_n_237_);
    crate::leanh::lean_dec(v_n_237_);
    v_r_239_ = crate::leanh::lean_box((v_res_238_) as usize);
    return v_r_239_;
}
pub unsafe fn l_Lake_instDecidableEqConfigLang(mut v_x_240_: u8, mut v_y_241_: u8) -> u8 {
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: u8 = 0;
    v___x_242_ = l_Lake_ConfigLang_ctorIdx(v_x_240_);
    v___x_243_ = l_Lake_ConfigLang_ctorIdx(v_y_241_);
    v___x_244_ = lean_nat_dec_eq(v___x_242_, v___x_243_);
    crate::leanh::lean_dec(v___x_243_);
    crate::leanh::lean_dec(v___x_242_);
    return v___x_244_;
}
pub unsafe fn l_Lake_instDecidableEqConfigLang___boxed(
    mut v_x_245_: *mut crate::leanh::LeanObject,
    mut v_y_246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_247_: u8 = 0;
    let mut v_y_14__boxed_248_: u8 = 0;
    let mut v_res_249_: u8 = 0;
    let mut v_r_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_247_ = (crate::leanh::lean_unbox(v_x_245_) as u8);
    v_y_14__boxed_248_ = (crate::leanh::lean_unbox(v_y_246_) as u8);
    v_res_249_ = l_Lake_instDecidableEqConfigLang(v_x_13__boxed_247_, v_y_14__boxed_248_);
    v_r_250_ = crate::leanh::lean_box((v_res_249_) as usize);
    return v_r_250_;
}
pub unsafe fn _init_l_Lake_ConfigLang_default() -> u8 {
    let mut v___x_251_: u8 = 0;
    v___x_251_ = 1;
    return v___x_251_;
}
pub unsafe fn _init_l_Lake_instInhabitedConfigLang() -> u8 {
    let mut v___x_252_: u8 = 0;
    v___x_252_ = 1;
    return v___x_252_;
}
pub unsafe fn l_Lake_ConfigLang_ofString_x3f(
    mut v_x_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: u8 = 0;
    v___x_262_ = l_Lake_ConfigLang_ofString_x3f___closed__0;
    v___x_263_ = lean_string_dec_eq(v_x_261_, v___x_262_);
    if v___x_263_ == 0 {
        let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_265_: u8 = 0;
        v___x_264_ = l_Lake_ConfigLang_ofString_x3f___closed__1;
        v___x_265_ = lean_string_dec_eq(v_x_261_, v___x_264_);
        if v___x_265_ == 0 {
            let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_266_ = crate::leanh::lean_box(0);
            return v___x_266_;
        } else {
            let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_267_ = l_Lake_ConfigLang_ofString_x3f___closed__2;
            return v___x_267_;
        }
    } else {
        let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_268_ = l_Lake_ConfigLang_ofString_x3f___closed__3;
        return v___x_268_;
    }
}
pub unsafe fn l_Lake_ConfigLang_ofString_x3f___boxed(
    mut v_x_269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_270_ = l_Lake_ConfigLang_ofString_x3f(v_x_269_);
    crate::leanh::lean_dec_ref(v_x_269_);
    return v_res_270_;
}
pub unsafe fn l_Lake_ConfigLang_fileExtension(mut v_x_271_: u8) -> *mut crate::leanh::LeanObject {
    if v_x_271_ == 0 {
        let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_272_ = l_Lake_ConfigLang_ofString_x3f___closed__0;
        return v___x_272_;
    } else {
        let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_273_ = l_Lake_ConfigLang_ofString_x3f___closed__1;
        return v___x_273_;
    }
}
pub unsafe fn l_Lake_ConfigLang_fileExtension___boxed(
    mut v_x_274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_20__boxed_275_: u8 = 0;
    let mut v_res_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_20__boxed_275_ = (crate::leanh::lean_unbox(v_x_274_) as u8);
    v_res_276_ = l_Lake_ConfigLang_fileExtension(v_x_20__boxed_275_);
    return v_res_276_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Lang(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_ConfigLang_default = _init_l_Lake_ConfigLang_default();
    l_Lake_instInhabitedConfigLang = _init_l_Lake_instInhabitedConfigLang();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Lang(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Lang(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Lang(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Lang(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Lang(builtin);
}
