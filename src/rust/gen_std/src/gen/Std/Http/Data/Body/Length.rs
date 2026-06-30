// Lean compiler output
// Module: Std.Http.Data.Body.Length
// Imports: Init.Data.Repr
use crate::ffi::{lean_nat_dec_eq, lean_nat_dec_le, lean_nat_to_int};
use crate::r#gen::Init::Data::Repr::{
    initialize_Init_Data_Repr, l_Nat_reprFast, l_Repr_addAppParen,
    runtime_initialize_Init_Data_Repr,
};
pub static l_Std_Http_Body_instReprLength_repr___closed__0_value: leanh::LeanStringObject<
    29,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Body_instReprLength_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instReprLength_repr___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Body_instReprLength_repr___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Body_instReprLength_repr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Body_instReprLength_repr___closed__4_value: leanh::LeanStringObject<
    27,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Http_Body_instReprLength_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instReprLength_repr___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instReprLength_repr___closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__5_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instReprLength___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Body_instReprLength_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instReprLength___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instReprLength: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instBEqLength___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Body_instBEqLength_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instBEqLength___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instBEqLength___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instBEqLength: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instBEqLength___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Http_Body_Length_ctorIdx(
    mut v_x_116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_116_) == 0 {
        let mut v___x_117_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_117_ = leanh::lean_unsigned_to_nat(0);
        return v___x_117_;
    } else {
        let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_118_ = leanh::lean_unsigned_to_nat(1);
        return v___x_118_;
    }
}
pub unsafe fn l_Std_Http_Body_Length_ctorIdx___boxed(
    mut v_x_119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_120_ = l_Std_Http_Body_Length_ctorIdx(v_x_119_);
    leanh::lean_dec(v_x_119_);
    return v_res_120_;
}
pub unsafe fn l_Std_Http_Body_Length_ctorElim___redArg(
    mut v_t_121_: *mut leanh::LeanObject,
    mut v_k_122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_121_) == 0 {
        return v_k_122_;
    } else {
        let mut v_n_123_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_124_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_n_123_ = leanh::lean_ctor_get(v_t_121_, 0);
        leanh::lean_inc(v_n_123_);
        leanh::lean_dec_ref_known(v_t_121_, 1);
        v___x_124_ = leanh::lean_apply_1(v_k_122_, v_n_123_);
        return v___x_124_;
    }
}
pub unsafe fn l_Std_Http_Body_Length_ctorElim(
    mut v_motive_125_: *mut leanh::LeanObject,
    mut v_ctorIdx_126_: *mut leanh::LeanObject,
    mut v_t_127_: *mut leanh::LeanObject,
    mut v_h_128_: *mut leanh::LeanObject,
    mut v_k_129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_130_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_127_, v_k_129_);
    return v___x_130_;
}
pub unsafe fn l_Std_Http_Body_Length_ctorElim___boxed(
    mut v_motive_131_: *mut leanh::LeanObject,
    mut v_ctorIdx_132_: *mut leanh::LeanObject,
    mut v_t_133_: *mut leanh::LeanObject,
    mut v_h_134_: *mut leanh::LeanObject,
    mut v_k_135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_136_ = l_Std_Http_Body_Length_ctorElim(
        v_motive_131_,
        v_ctorIdx_132_,
        v_t_133_,
        v_h_134_,
        v_k_135_,
    );
    leanh::lean_dec(v_ctorIdx_132_);
    return v_res_136_;
}
pub unsafe fn l_Std_Http_Body_Length_chunked_elim___redArg(
    mut v_t_137_: *mut leanh::LeanObject,
    mut v_chunked_138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_139_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_137_, v_chunked_138_);
    return v___x_139_;
}
pub unsafe fn l_Std_Http_Body_Length_chunked_elim(
    mut v_motive_140_: *mut leanh::LeanObject,
    mut v_t_141_: *mut leanh::LeanObject,
    mut v_h_142_: *mut leanh::LeanObject,
    mut v_chunked_143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_144_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_141_, v_chunked_143_);
    return v___x_144_;
}
pub unsafe fn l_Std_Http_Body_Length_fixed_elim___redArg(
    mut v_t_145_: *mut leanh::LeanObject,
    mut v_fixed_146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_147_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_145_, v_fixed_146_);
    return v___x_147_;
}
pub unsafe fn l_Std_Http_Body_Length_fixed_elim(
    mut v_motive_148_: *mut leanh::LeanObject,
    mut v_t_149_: *mut leanh::LeanObject,
    mut v_h_150_: *mut leanh::LeanObject,
    mut v_fixed_151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_152_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_149_, v_fixed_151_);
    return v___x_152_;
}
pub unsafe fn _init_l_Std_Http_Body_instReprLength_repr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_156_ = leanh::lean_unsigned_to_nat(2);
    v___x_157_ = lean_nat_to_int(v___x_156_);
    return v___x_157_;
}
pub unsafe fn _init_l_Std_Http_Body_instReprLength_repr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_158_ = leanh::lean_unsigned_to_nat(1);
    v___x_159_ = lean_nat_to_int(v___x_158_);
    return v___x_159_;
}
pub unsafe fn l_Std_Http_Body_instReprLength_repr(
    mut v_x_166_: *mut leanh::LeanObject,
    mut v_prec_167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: u8 = 0;
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: u8 = 0;
    let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_182_: u8 = 0;
    let mut v___y_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: u8 = 0;
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: u8 = 0;
    let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_166_) == 0 {
                    v___x_175_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_176_ = lean_nat_dec_le(v___x_175_, v_prec_167_);
                    if v___x_176_ == 0 {
                        v___x_177_ = leanh::lean_obj_once(
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
                        v___x_178_ = leanh::lean_obj_once(
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
                    v_n_179_ = leanh::lean_ctor_get(v_x_166_, 0);
                    v_isSharedCheck_199_ = (!leanh::lean_is_exclusive(v_x_166_)) as u8;
                    if v_isSharedCheck_199_ == 0 {
                        v___x_181_ = v_x_166_;
                        v_isShared_182_ = v_isSharedCheck_199_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_n_179_);
                        leanh::lean_dec(v_x_166_);
                        v___x_181_ = leanh::lean_box(0);
                        v_isShared_182_ = v_isSharedCheck_199_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_170_ = l_Std_Http_Body_instReprLength_repr___closed__1;
                leanh::lean_inc(v___y_169_);
                v___x_171_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_171_, 0, v___y_169_);
                leanh::lean_ctor_set(v___x_171_, 1, v___x_170_);
                v___x_172_ = 0;
                v___x_173_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_173_, 0, v___x_171_);
                leanh::lean_ctor_set_uint8(
                    v___x_173_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_172_,
                );
                v___x_174_ = l_Repr_addAppParen(v___x_173_, v_prec_167_);
                return v___x_174_;
            }
            2 => {
                v___x_195_ = leanh::lean_unsigned_to_nat(1024);
                v___x_196_ = lean_nat_dec_le(v___x_195_, v_prec_167_);
                if v___x_196_ == 0 {
                    v___x_197_ = leanh::lean_obj_once(
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
                    v___x_198_ = leanh::lean_obj_once(
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
                    leanh::lean_ctor_set_tag(v___x_181_, 3);
                    leanh::lean_ctor_set(v___x_181_, 0, v___x_186_);
                    v___x_188_ = v___x_181_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_194_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_186_);
                    v___x_188_ = v_reuseFailAlloc_194_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_189_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_189_, 0, v___x_185_);
                leanh::lean_ctor_set(v___x_189_, 1, v___x_188_);
                leanh::lean_inc(v___y_184_);
                v___x_190_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_190_, 0, v___y_184_);
                leanh::lean_ctor_set(v___x_190_, 1, v___x_189_);
                v___x_191_ = 0;
                v___x_192_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_192_, 0, v___x_190_);
                leanh::lean_ctor_set_uint8(
                    v___x_192_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_x_200_: *mut leanh::LeanObject,
    mut v_prec_201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_202_ = l_Std_Http_Body_instReprLength_repr(v_x_200_, v_prec_201_);
    leanh::lean_dec(v_prec_201_);
    return v_res_202_;
}
pub unsafe fn l_Std_Http_Body_instBEqLength_beq(
    mut v_x_205_: *mut leanh::LeanObject,
    mut v_x_206_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_205_) == 0 {
        if leanh::lean_obj_tag(v_x_206_) == 0 {
            let mut v___x_207_: u8 = 0;
            v___x_207_ = 1;
            return v___x_207_;
        } else {
            let mut v___x_208_: u8 = 0;
            v___x_208_ = 0;
            return v___x_208_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_206_) == 1 {
            let mut v_n_209_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_210_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_211_: u8 = 0;
            v_n_209_ = leanh::lean_ctor_get(v_x_205_, 0);
            v_n_210_ = leanh::lean_ctor_get(v_x_206_, 0);
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
    mut v_x_213_: *mut leanh::LeanObject,
    mut v_x_214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_215_: u8 = 0;
    let mut v_r_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_215_ = l_Std_Http_Body_instBEqLength_beq(v_x_213_, v_x_214_);
    leanh::lean_dec(v_x_214_);
    leanh::lean_dec(v_x_213_);
    v_r_216_ = leanh::lean_box((v_res_215_) as usize);
    return v_r_216_;
}
pub unsafe fn l_Std_Http_Body_Length_isChunked(mut v_x_219_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_219_) == 0 {
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
    mut v_x_222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_223_: u8 = 0;
    let mut v_r_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_223_ = l_Std_Http_Body_Length_isChunked(v_x_222_);
    leanh::lean_dec(v_x_222_);
    v_r_224_ = leanh::lean_box((v_res_223_) as usize);
    return v_r_224_;
}
pub unsafe fn l_Std_Http_Body_Length_isFixed(mut v_x_225_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_225_) == 1 {
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
    mut v_x_228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_229_: u8 = 0;
    let mut v_r_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_229_ = l_Std_Http_Body_Length_isFixed(v_x_228_);
    leanh::lean_dec(v_x_228_);
    v_r_230_ = leanh::lean_box((v_res_229_) as usize);
    return v_r_230_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Body_Length(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Repr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Body_Length(
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
pub unsafe fn initialize_Std_Http_Data_Body_Length(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Repr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Body_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Body_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_Body_Length(builtin);
}