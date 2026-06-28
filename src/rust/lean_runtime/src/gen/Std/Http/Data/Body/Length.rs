// Lean compiler output
// Module: Std.Http.Data.Body.Length
// Imports: Init.Data.Repr
use crate::r#gen::Init::Data::Repr::{
    initialize_Init_Data_Repr, l_Nat_reprFast, l_Repr_addAppParen,
    runtime_initialize_Init_Data_Repr,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_dec_le};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Std_Http_Body_instReprLength_repr___closed__0_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 66, 111, 100, 121, 46, 76, 101, 110, 103, 116,
            104, 46, 99, 104, 117, 110, 107, 101, 100, 0,
        ],
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_instReprLength_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__1_value) as *mut LeanObject;
static mut l_Std_Http_Body_instReprLength_repr___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Body_instReprLength_repr___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Body_instReprLength_repr___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Body_instReprLength_repr___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Body_instReprLength_repr___closed__4_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 66, 111, 100, 121, 46, 76, 101, 110, 103, 116,
            104, 46, 102, 105, 120, 101, 100, 0,
        ],
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__4_value) as *mut LeanObject;
pub static l_Std_Http_Body_instReprLength_repr___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__5_value) as *mut LeanObject;
pub static l_Std_Http_Body_instReprLength_repr___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__5_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__6_value) as *mut LeanObject;
pub static l_Std_Http_Body_instReprLength___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Body_instReprLength_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instReprLength___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Body_instReprLength: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_instBEqLength___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Body_instBEqLength_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instBEqLength___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instBEqLength___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Body_instBEqLength: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instBEqLength___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Std_Http_Body_Length_ctorIdx(mut v_x_116_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_116_) == 0 {
        let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
        v___x_117_ = lean_unsigned_to_nat(0);
        return v___x_117_;
    } else {
        let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
        v___x_118_ = lean_unsigned_to_nat(1);
        return v___x_118_;
    }
}
pub unsafe fn l_Std_Http_Body_Length_ctorIdx___boxed(
    mut v_x_119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_120_: *mut LeanObject = core::ptr::null_mut();
    v_res_120_ = l_Std_Http_Body_Length_ctorIdx(v_x_119_);
    lean_dec(v_x_119_);
    return v_res_120_;
}
pub unsafe fn l_Std_Http_Body_Length_ctorElim___redArg(
    mut v_t_121_: *mut LeanObject,
    mut v_k_122_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_121_) == 0 {
        return v_k_122_;
    } else {
        let mut v_n_123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
        v_n_123_ = lean_ctor_get(v_t_121_, 0);
        lean_inc(v_n_123_);
        lean_dec_ref_known(v_t_121_, 1);
        v___x_124_ = lean_apply_1(v_k_122_, v_n_123_);
        return v___x_124_;
    }
}
pub unsafe fn l_Std_Http_Body_Length_ctorElim(
    mut v_motive_125_: *mut LeanObject,
    mut v_ctorIdx_126_: *mut LeanObject,
    mut v_t_127_: *mut LeanObject,
    mut v_h_128_: *mut LeanObject,
    mut v_k_129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
    v___x_130_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_127_, v_k_129_);
    return v___x_130_;
}
pub unsafe fn l_Std_Http_Body_Length_ctorElim___boxed(
    mut v_motive_131_: *mut LeanObject,
    mut v_ctorIdx_132_: *mut LeanObject,
    mut v_t_133_: *mut LeanObject,
    mut v_h_134_: *mut LeanObject,
    mut v_k_135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_136_: *mut LeanObject = core::ptr::null_mut();
    v_res_136_ = l_Std_Http_Body_Length_ctorElim(
        v_motive_131_,
        v_ctorIdx_132_,
        v_t_133_,
        v_h_134_,
        v_k_135_,
    );
    lean_dec(v_ctorIdx_132_);
    return v_res_136_;
}
pub unsafe fn l_Std_Http_Body_Length_chunked_elim___redArg(
    mut v_t_137_: *mut LeanObject,
    mut v_chunked_138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
    v___x_139_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_137_, v_chunked_138_);
    return v___x_139_;
}
pub unsafe fn l_Std_Http_Body_Length_chunked_elim(
    mut v_motive_140_: *mut LeanObject,
    mut v_t_141_: *mut LeanObject,
    mut v_h_142_: *mut LeanObject,
    mut v_chunked_143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_144_: *mut LeanObject = core::ptr::null_mut();
    v___x_144_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_141_, v_chunked_143_);
    return v___x_144_;
}
pub unsafe fn l_Std_Http_Body_Length_fixed_elim___redArg(
    mut v_t_145_: *mut LeanObject,
    mut v_fixed_146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
    v___x_147_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_145_, v_fixed_146_);
    return v___x_147_;
}
pub unsafe fn l_Std_Http_Body_Length_fixed_elim(
    mut v_motive_148_: *mut LeanObject,
    mut v_t_149_: *mut LeanObject,
    mut v_h_150_: *mut LeanObject,
    mut v_fixed_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_152_: *mut LeanObject = core::ptr::null_mut();
    v___x_152_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_149_, v_fixed_151_);
    return v___x_152_;
}
pub unsafe fn _init_l_Std_Http_Body_instReprLength_repr___closed__2() -> *mut LeanObject {
    let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
    v___x_156_ = lean_unsigned_to_nat(2);
    v___x_157_ = lean_nat_to_int(v___x_156_);
    return v___x_157_;
}
pub unsafe fn _init_l_Std_Http_Body_instReprLength_repr___closed__3() -> *mut LeanObject {
    let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut LeanObject = core::ptr::null_mut();
    v___x_158_ = lean_unsigned_to_nat(1);
    v___x_159_ = lean_nat_to_int(v___x_158_);
    return v___x_159_;
}
pub unsafe fn l_Std_Http_Body_instReprLength_repr(
    mut v_x_166_: *mut LeanObject,
    mut v_prec_167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_172_: u8 = 0;
    let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_176_: u8 = 0;
    let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_182_: u8 = 0;
    let mut v___y_184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_191_: u8 = 0;
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_196_: u8 = 0;
    let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_166_) == 0 {
                    v___x_175_ = lean_unsigned_to_nat(1024);
                    v___x_176_ = lean_nat_dec_le(v___x_175_, v_prec_167_);
                    if v___x_176_ == 0 {
                        v___x_177_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Body_instReprLength_repr___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Body_instReprLength_repr___closed__2_once
                            ),
                            _init_l_Std_Http_Body_instReprLength_repr___closed__2,
                        );
                        v___y_169_ = v___x_177_;
                        state = 1;
                        continue;
                    } else {
                        v___x_178_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Body_instReprLength_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Body_instReprLength_repr___closed__3_once
                            ),
                            _init_l_Std_Http_Body_instReprLength_repr___closed__3,
                        );
                        v___y_169_ = v___x_178_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_n_179_ = lean_ctor_get(v_x_166_, 0);
                    v_isSharedCheck_199_ = (!lean_is_exclusive(v_x_166_)) as u8;
                    if v_isSharedCheck_199_ == 0 {
                        v___x_181_ = v_x_166_;
                        v_isShared_182_ = v_isSharedCheck_199_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_n_179_);
                        lean_dec(v_x_166_);
                        v___x_181_ = lean_box(0);
                        v_isShared_182_ = v_isSharedCheck_199_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_170_ = l_Std_Http_Body_instReprLength_repr___closed__1;
                lean_inc(v___y_169_);
                v___x_171_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_171_, 0, v___y_169_);
                lean_ctor_set(v___x_171_, 1, v___x_170_);
                v___x_172_ = 0;
                v___x_173_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_173_, 0, v___x_171_);
                lean_ctor_set_uint8(
                    v___x_173_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_172_,
                );
                v___x_174_ = l_Repr_addAppParen(v___x_173_, v_prec_167_);
                return v___x_174_;
            }
            2 => {
                v___x_195_ = lean_unsigned_to_nat(1024);
                v___x_196_ = lean_nat_dec_le(v___x_195_, v_prec_167_);
                if v___x_196_ == 0 {
                    v___x_197_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Body_instReprLength_repr___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Body_instReprLength_repr___closed__2_once
                        ),
                        _init_l_Std_Http_Body_instReprLength_repr___closed__2,
                    );
                    v___y_184_ = v___x_197_;
                    state = 3;
                    continue;
                } else {
                    v___x_198_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Body_instReprLength_repr___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Body_instReprLength_repr___closed__3_once
                        ),
                        _init_l_Std_Http_Body_instReprLength_repr___closed__3,
                    );
                    v___y_184_ = v___x_198_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_185_ = l_Std_Http_Body_instReprLength_repr___closed__6;
                v___x_186_ = l_Nat_reprFast(v_n_179_);
                if v_isShared_182_ == 0 {
                    lean_ctor_set_tag(v___x_181_, 3);
                    lean_ctor_set(v___x_181_, 0, v___x_186_);
                    v___x_188_ = v___x_181_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_194_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_186_);
                    v___x_188_ = v_reuseFailAlloc_194_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_189_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_189_, 0, v___x_185_);
                lean_ctor_set(v___x_189_, 1, v___x_188_);
                lean_inc(v___y_184_);
                v___x_190_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_190_, 0, v___y_184_);
                lean_ctor_set(v___x_190_, 1, v___x_189_);
                v___x_191_ = 0;
                v___x_192_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_192_, 0, v___x_190_);
                lean_ctor_set_uint8(
                    v___x_192_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_191_,
                );
                v___x_193_ = l_Repr_addAppParen(v___x_192_, v_prec_167_);
                return v___x_193_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_instReprLength_repr___boxed(
    mut v_x_200_: *mut LeanObject,
    mut v_prec_201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_202_: *mut LeanObject = core::ptr::null_mut();
    v_res_202_ = l_Std_Http_Body_instReprLength_repr(v_x_200_, v_prec_201_);
    lean_dec(v_prec_201_);
    return v_res_202_;
}
pub unsafe fn l_Std_Http_Body_instBEqLength_beq(
    mut v_x_205_: *mut LeanObject,
    mut v_x_206_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_205_) == 0 {
        if lean_obj_tag(v_x_206_) == 0 {
            let mut v___x_207_: u8 = 0;
            v___x_207_ = 1;
            return v___x_207_;
        } else {
            let mut v___x_208_: u8 = 0;
            v___x_208_ = 0;
            return v___x_208_;
        }
    } else {
        if lean_obj_tag(v_x_206_) == 1 {
            let mut v_n_209_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_210_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_211_: u8 = 0;
            v_n_209_ = lean_ctor_get(v_x_205_, 0);
            v_n_210_ = lean_ctor_get(v_x_206_, 0);
            v___x_211_ = lean_nat_dec_eq(v_n_209_, v_n_210_);
            return v___x_211_;
        } else {
            let mut v___x_212_: u8 = 0;
            v___x_212_ = 0;
            return v___x_212_;
        }
    }
}
pub unsafe fn l_Std_Http_Body_instBEqLength_beq___boxed(
    mut v_x_213_: *mut LeanObject,
    mut v_x_214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_215_: u8 = 0;
    let mut v_r_216_: *mut LeanObject = core::ptr::null_mut();
    v_res_215_ = l_Std_Http_Body_instBEqLength_beq(v_x_213_, v_x_214_);
    lean_dec(v_x_214_);
    lean_dec(v_x_213_);
    v_r_216_ = lean_box((v_res_215_) as usize);
    return v_r_216_;
}
pub unsafe fn l_Std_Http_Body_Length_isChunked(mut v_x_219_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_219_) == 0 {
        let mut v___x_220_: u8 = 0;
        v___x_220_ = 1;
        return v___x_220_;
    } else {
        let mut v___x_221_: u8 = 0;
        v___x_221_ = 0;
        return v___x_221_;
    }
}
pub unsafe fn l_Std_Http_Body_Length_isChunked___boxed(
    mut v_x_222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_223_: u8 = 0;
    let mut v_r_224_: *mut LeanObject = core::ptr::null_mut();
    v_res_223_ = l_Std_Http_Body_Length_isChunked(v_x_222_);
    lean_dec(v_x_222_);
    v_r_224_ = lean_box((v_res_223_) as usize);
    return v_r_224_;
}
pub unsafe fn l_Std_Http_Body_Length_isFixed(mut v_x_225_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_225_) == 1 {
        let mut v___x_226_: u8 = 0;
        v___x_226_ = 1;
        return v___x_226_;
    } else {
        let mut v___x_227_: u8 = 0;
        v___x_227_ = 0;
        return v___x_227_;
    }
}
pub unsafe fn l_Std_Http_Body_Length_isFixed___boxed(
    mut v_x_228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_229_: u8 = 0;
    let mut v_r_230_: *mut LeanObject = core::ptr::null_mut();
    v_res_229_ = l_Std_Http_Body_Length_isFixed(v_x_228_);
    lean_dec(v_x_228_);
    v_r_230_ = lean_box((v_res_229_) as usize);
    return v_r_230_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Body_Length(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Repr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Body_Length(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_Body_Length(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Repr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Body_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Body_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Http_Data_Body_Length(builtin);
}
