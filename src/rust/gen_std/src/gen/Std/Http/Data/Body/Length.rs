// Lean compiler output
// Module: Std.Http.Data.Body.Length
// Imports: Init.Data.Repr
use crate::r#gen::Init::Data::Repr::{
    initialize_Init_Data_Repr, l_Nat_reprFast, l_Repr_addAppParen,
    runtime_initialize_Init_Data_Repr,
};
use crate::ffi::lean_nat_to_int;
use crate::ffi::{lean_nat_dec_eq, lean_nat_dec_le};
pub static l_Std_Http_Body_instReprLength_repr___closed__0_value: crate::leanh::LeanStringObject<
    29,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Http_Body_instReprLength_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Body_instReprLength_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Body_instReprLength_repr___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Body_instReprLength_repr___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Body_instReprLength_repr___closed__4_value: crate::leanh::LeanStringObject<
    27,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Http_Body_instReprLength_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Body_instReprLength_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Body_instReprLength_repr___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__5_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_instReprLength_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Body_instReprLength___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_instReprLength_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instReprLength___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Body_instReprLength: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instReprLength___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Body_instBEqLength___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_instBEqLength_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instBEqLength___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instBEqLength___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Body_instBEqLength: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instBEqLength___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Http_Body_Length_ctorIdx(
    mut v_x_116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_116_) == 0 {
        let mut v___x_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_117_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_117_;
    } else {
        let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_118_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_118_;
    }
}
pub unsafe fn l_Std_Http_Body_Length_ctorIdx___boxed(
    mut v_x_119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_120_ = l_Std_Http_Body_Length_ctorIdx(v_x_119_);
    crate::leanh::lean_dec(v_x_119_);
    return v_res_120_;
}
pub unsafe fn l_Std_Http_Body_Length_ctorElim___redArg(
    mut v_t_121_: *mut crate::leanh::LeanObject,
    mut v_k_122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_121_) == 0 {
        return v_k_122_;
    } else {
        let mut v_n_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_n_123_ = crate::leanh::lean_ctor_get(v_t_121_, 0);
        crate::leanh::lean_inc(v_n_123_);
        crate::leanh::lean_dec_ref_known(v_t_121_, 1);
        v___x_124_ = crate::leanh::lean_apply_1(v_k_122_, v_n_123_);
        return v___x_124_;
    }
}
pub unsafe fn l_Std_Http_Body_Length_ctorElim(
    mut v_motive_125_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_126_: *mut crate::leanh::LeanObject,
    mut v_t_127_: *mut crate::leanh::LeanObject,
    mut v_h_128_: *mut crate::leanh::LeanObject,
    mut v_k_129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_130_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_127_, v_k_129_);
    return v___x_130_;
}
pub unsafe fn l_Std_Http_Body_Length_ctorElim___boxed(
    mut v_motive_131_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_132_: *mut crate::leanh::LeanObject,
    mut v_t_133_: *mut crate::leanh::LeanObject,
    mut v_h_134_: *mut crate::leanh::LeanObject,
    mut v_k_135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_136_ = l_Std_Http_Body_Length_ctorElim(
        v_motive_131_,
        v_ctorIdx_132_,
        v_t_133_,
        v_h_134_,
        v_k_135_,
    );
    crate::leanh::lean_dec(v_ctorIdx_132_);
    return v_res_136_;
}
pub unsafe fn l_Std_Http_Body_Length_chunked_elim___redArg(
    mut v_t_137_: *mut crate::leanh::LeanObject,
    mut v_chunked_138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_139_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_137_, v_chunked_138_);
    return v___x_139_;
}
pub unsafe fn l_Std_Http_Body_Length_chunked_elim(
    mut v_motive_140_: *mut crate::leanh::LeanObject,
    mut v_t_141_: *mut crate::leanh::LeanObject,
    mut v_h_142_: *mut crate::leanh::LeanObject,
    mut v_chunked_143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_144_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_141_, v_chunked_143_);
    return v___x_144_;
}
pub unsafe fn l_Std_Http_Body_Length_fixed_elim___redArg(
    mut v_t_145_: *mut crate::leanh::LeanObject,
    mut v_fixed_146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_147_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_145_, v_fixed_146_);
    return v___x_147_;
}
pub unsafe fn l_Std_Http_Body_Length_fixed_elim(
    mut v_motive_148_: *mut crate::leanh::LeanObject,
    mut v_t_149_: *mut crate::leanh::LeanObject,
    mut v_h_150_: *mut crate::leanh::LeanObject,
    mut v_fixed_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_152_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_149_, v_fixed_151_);
    return v___x_152_;
}
pub unsafe fn _init_l_Std_Http_Body_instReprLength_repr___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_156_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_157_ = lean_nat_to_int(v___x_156_);
    return v___x_157_;
}
pub unsafe fn _init_l_Std_Http_Body_instReprLength_repr___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_158_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_159_ = lean_nat_to_int(v___x_158_);
    return v___x_159_;
}
pub unsafe fn l_Std_Http_Body_instReprLength_repr(
    mut v_x_166_: *mut crate::leanh::LeanObject,
    mut v_prec_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: u8 = 0;
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: u8 = 0;
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_182_: u8 = 0;
    let mut v___y_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: u8 = 0;
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: u8 = 0;
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_166_) == 0 {
                    v___x_175_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_176_ = lean_nat_dec_le(v___x_175_, v_prec_167_);
                    if v___x_176_ == 0 {
                        v___x_177_ = crate::leanh::lean_obj_once(
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
                        v___x_178_ = crate::leanh::lean_obj_once(
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
                    v_n_179_ = crate::leanh::lean_ctor_get(v_x_166_, 0);
                    v_isSharedCheck_199_ = (!crate::leanh::lean_is_exclusive(v_x_166_)) as u8;
                    if v_isSharedCheck_199_ == 0 {
                        v___x_181_ = v_x_166_;
                        v_isShared_182_ = v_isSharedCheck_199_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_n_179_);
                        crate::leanh::lean_dec(v_x_166_);
                        v___x_181_ = crate::leanh::lean_box(0);
                        v_isShared_182_ = v_isSharedCheck_199_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_170_ = l_Std_Http_Body_instReprLength_repr___closed__1;
                crate::leanh::lean_inc(v___y_169_);
                v___x_171_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_171_, 0, v___y_169_);
                crate::leanh::lean_ctor_set(v___x_171_, 1, v___x_170_);
                v___x_172_ = 0;
                v___x_173_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_173_, 0, v___x_171_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_173_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_172_,
                );
                v___x_174_ = l_Repr_addAppParen(v___x_173_, v_prec_167_);
                return v___x_174_;
            }
            2 => {
                v___x_195_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_196_ = lean_nat_dec_le(v___x_195_, v_prec_167_);
                if v___x_196_ == 0 {
                    v___x_197_ = crate::leanh::lean_obj_once(
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
                    v___x_198_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_ctor_set_tag(v___x_181_, 3);
                    crate::leanh::lean_ctor_set(v___x_181_, 0, v___x_186_);
                    v___x_188_ = v___x_181_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_194_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_186_);
                    v___x_188_ = v_reuseFailAlloc_194_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_189_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_189_, 0, v___x_185_);
                crate::leanh::lean_ctor_set(v___x_189_, 1, v___x_188_);
                crate::leanh::lean_inc(v___y_184_);
                v___x_190_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_190_, 0, v___y_184_);
                crate::leanh::lean_ctor_set(v___x_190_, 1, v___x_189_);
                v___x_191_ = 0;
                v___x_192_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_192_, 0, v___x_190_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_192_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_x_200_: *mut crate::leanh::LeanObject,
    mut v_prec_201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_202_ = l_Std_Http_Body_instReprLength_repr(v_x_200_, v_prec_201_);
    crate::leanh::lean_dec(v_prec_201_);
    return v_res_202_;
}
pub unsafe fn l_Std_Http_Body_instBEqLength_beq(
    mut v_x_205_: *mut crate::leanh::LeanObject,
    mut v_x_206_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_205_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_206_) == 0 {
            let mut v___x_207_: u8 = 0;
            v___x_207_ = 1;
            return v___x_207_;
        } else {
            let mut v___x_208_: u8 = 0;
            v___x_208_ = 0;
            return v___x_208_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_206_) == 1 {
            let mut v_n_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_211_: u8 = 0;
            v_n_209_ = crate::leanh::lean_ctor_get(v_x_205_, 0);
            v_n_210_ = crate::leanh::lean_ctor_get(v_x_206_, 0);
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
    mut v_x_213_: *mut crate::leanh::LeanObject,
    mut v_x_214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_215_: u8 = 0;
    let mut v_r_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_215_ = l_Std_Http_Body_instBEqLength_beq(v_x_213_, v_x_214_);
    crate::leanh::lean_dec(v_x_214_);
    crate::leanh::lean_dec(v_x_213_);
    v_r_216_ = crate::leanh::lean_box((v_res_215_) as usize);
    return v_r_216_;
}
pub unsafe fn l_Std_Http_Body_Length_isChunked(mut v_x_219_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_219_) == 0 {
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
    mut v_x_222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_223_: u8 = 0;
    let mut v_r_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_223_ = l_Std_Http_Body_Length_isChunked(v_x_222_);
    crate::leanh::lean_dec(v_x_222_);
    v_r_224_ = crate::leanh::lean_box((v_res_223_) as usize);
    return v_r_224_;
}
pub unsafe fn l_Std_Http_Body_Length_isFixed(mut v_x_225_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_225_) == 1 {
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
    mut v_x_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_229_: u8 = 0;
    let mut v_r_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_229_ = l_Std_Http_Body_Length_isFixed(v_x_228_);
    crate::leanh::lean_dec(v_x_228_);
    v_r_230_ = crate::leanh::lean_box((v_res_229_) as usize);
    return v_r_230_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Body_Length(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Body_Length(
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
pub unsafe fn initialize_Std_Http_Data_Body_Length(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Body_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Body_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_Body_Length(builtin);
}
