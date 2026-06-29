// Lean compiler output
// Module: Lean.Compiler.IR.ToIRType
// Imports: Lean.Compiler.IR.Format Lean.Compiler.LCNF.MonoTypes
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::IR::Format::{
    initialize_Lean_Compiler_IR_Format, runtime_initialize_Lean_Compiler_IR_Format,
};
use crate::r#gen::Lean::Compiler::LCNF::MonoTypes::{
    initialize_Lean_Compiler_LCNF_MonoTypes, runtime_initialize_Lean_Compiler_LCNF_MonoTypes,
};
use crate::ffi::{lean_panic_fn_borrowed, lean_string_dec_eq};
pub static l_Lean_IR_nameToIRType___closed__0_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 73, 82, 46, 84, 111,
            73, 82, 84, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_IR_nameToIRType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_nameToIRType___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_nameToIRType___closed__1_value: crate::leanh::LeanStringObject<21> =
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
            76, 101, 97, 110, 46, 73, 82, 46, 110, 97, 109, 101, 84, 111, 73, 82, 84, 121, 112,
            101, 0,
        ],
    };
static mut l_Lean_IR_nameToIRType___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_nameToIRType___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_nameToIRType___closed__2_value: crate::leanh::LeanStringObject<34> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_IR_nameToIRType___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_nameToIRType___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_nameToIRType___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_nameToIRType___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_nameToIRType___closed__4_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [70, 108, 111, 97, 116, 0],
    };
static mut l_Lean_IR_nameToIRType___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_nameToIRType___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_nameToIRType___closed__5_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [70, 108, 111, 97, 116, 51, 50, 0],
    };
static mut l_Lean_IR_nameToIRType___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_nameToIRType___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_nameToIRType___closed__6_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [85, 73, 110, 116, 56, 0],
    };
static mut l_Lean_IR_nameToIRType___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_nameToIRType___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_nameToIRType___closed__7_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [85, 73, 110, 116, 49, 54, 0],
    };
static mut l_Lean_IR_nameToIRType___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_nameToIRType___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_nameToIRType___closed__8_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [85, 73, 110, 116, 51, 50, 0],
    };
static mut l_Lean_IR_nameToIRType___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_nameToIRType___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_nameToIRType___closed__9_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [85, 73, 110, 116, 54, 52, 0],
    };
static mut l_Lean_IR_nameToIRType___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_nameToIRType___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_nameToIRType___closed__10_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [108, 99, 69, 114, 97, 115, 101, 100, 0],
    };
static mut l_Lean_IR_nameToIRType___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_nameToIRType___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_nameToIRType___closed__11_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [111, 98, 106, 0],
    };
static mut l_Lean_IR_nameToIRType___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_nameToIRType___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_nameToIRType___closed__12_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 111, 98, 106, 0],
    };
static mut l_Lean_IR_nameToIRType___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_nameToIRType___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_nameToIRType___closed__13_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [116, 97, 103, 103, 101, 100, 0],
    };
static mut l_Lean_IR_nameToIRType___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_nameToIRType___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_nameToIRType___closed__14_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [108, 99, 86, 111, 105, 100, 0],
    };
static mut l_Lean_IR_nameToIRType___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_nameToIRType___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_toIRType___closed__0_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            76, 101, 97, 110, 46, 73, 82, 46, 116, 111, 73, 82, 84, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_IR_toIRType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_toIRType___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_toIRType___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_toIRType___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_toIRType___closed__2_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [85, 83, 105, 122, 101, 0],
    };
static mut l_Lean_IR_toIRType___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_toIRType___closed__2_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_panic___at___00Lean_IR_nameToIRType_spec__0(
    mut v_msg_119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_120_ = crate::leanh::lean_box(0);
    v___x_121_ = lean_panic_fn_borrowed(v___x_120_, v_msg_119_);
    return v___x_121_;
}
pub unsafe fn _init_l_Lean_IR_nameToIRType___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_125_ = l_Lean_IR_nameToIRType___closed__2;
    v___x_126_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_127_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_128_ = l_Lean_IR_nameToIRType___closed__1;
    v___x_129_ = l_Lean_IR_nameToIRType___closed__0;
    v___x_130_ =
        l_mkPanicMessageWithDecl(v___x_129_, v___x_128_, v___x_127_, v___x_126_, v___x_125_);
    return v___x_130_;
}
pub unsafe fn l_Lean_IR_nameToIRType(
    mut v_n_142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_149_: u8 = 0;
    let mut v___x_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_151_: u8 = 0;
    let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: u8 = 0;
    let mut v___x_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: u8 = 0;
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: u8 = 0;
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: u8 = 0;
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: u8 = 0;
    let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_163_: u8 = 0;
    let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: u8 = 0;
    let mut v___x_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_167_: u8 = 0;
    let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: u8 = 0;
    let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_142_) == 1 {
                    v_pre_146_ = crate::leanh::lean_ctor_get(v_n_142_, 0);
                    if crate::leanh::lean_obj_tag(v_pre_146_) == 0 {
                        v_str_147_ = crate::leanh::lean_ctor_get(v_n_142_, 1);
                        v___x_148_ = l_Lean_IR_nameToIRType___closed__4;
                        v___x_149_ = lean_string_dec_eq(v_str_147_, v___x_148_);
                        if v___x_149_ == 0 {
                            v___x_150_ = l_Lean_IR_nameToIRType___closed__5;
                            v___x_151_ = lean_string_dec_eq(v_str_147_, v___x_150_);
                            if v___x_151_ == 0 {
                                v___x_152_ = l_Lean_IR_nameToIRType___closed__6;
                                v___x_153_ = lean_string_dec_eq(v_str_147_, v___x_152_);
                                if v___x_153_ == 0 {
                                    v___x_154_ = l_Lean_IR_nameToIRType___closed__7;
                                    v___x_155_ = lean_string_dec_eq(v_str_147_, v___x_154_);
                                    if v___x_155_ == 0 {
                                        v___x_156_ = l_Lean_IR_nameToIRType___closed__8;
                                        v___x_157_ = lean_string_dec_eq(v_str_147_, v___x_156_);
                                        if v___x_157_ == 0 {
                                            v___x_158_ = l_Lean_IR_nameToIRType___closed__9;
                                            v___x_159_ = lean_string_dec_eq(v_str_147_, v___x_158_);
                                            if v___x_159_ == 0 {
                                                v___x_160_ = l_Lean_IR_nameToIRType___closed__10;
                                                v___x_161_ =
                                                    lean_string_dec_eq(v_str_147_, v___x_160_);
                                                if v___x_161_ == 0 {
                                                    v___x_162_ =
                                                        l_Lean_IR_nameToIRType___closed__11;
                                                    v___x_163_ =
                                                        lean_string_dec_eq(v_str_147_, v___x_162_);
                                                    if v___x_163_ == 0 {
                                                        v___x_164_ =
                                                            l_Lean_IR_nameToIRType___closed__12;
                                                        v___x_165_ = lean_string_dec_eq(
                                                            v_str_147_, v___x_164_,
                                                        );
                                                        if v___x_165_ == 0 {
                                                            v___x_166_ =
                                                                l_Lean_IR_nameToIRType___closed__13;
                                                            v___x_167_ = lean_string_dec_eq(
                                                                v_str_147_, v___x_166_,
                                                            );
                                                            if v___x_167_ == 0 {
                                                                v___x_168_ = l_Lean_IR_nameToIRType___closed__14;
                                                                v___x_169_ = lean_string_dec_eq(
                                                                    v_str_147_, v___x_168_,
                                                                );
                                                                if v___x_169_ == 0 {
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    v___x_170_ =
                                                                        crate::leanh::lean_box(13);
                                                                    return v___x_170_;
                                                                }
                                                            } else {
                                                                v___x_171_ =
                                                                    crate::leanh::lean_box(12);
                                                                return v___x_171_;
                                                            }
                                                        } else {
                                                            v___x_172_ = crate::leanh::lean_box(8);
                                                            return v___x_172_;
                                                        }
                                                    } else {
                                                        v___x_173_ = crate::leanh::lean_box(7);
                                                        return v___x_173_;
                                                    }
                                                } else {
                                                    v___x_174_ = crate::leanh::lean_box(6);
                                                    return v___x_174_;
                                                }
                                            } else {
                                                v___x_175_ = crate::leanh::lean_box(4);
                                                return v___x_175_;
                                            }
                                        } else {
                                            v___x_176_ = crate::leanh::lean_box(3);
                                            return v___x_176_;
                                        }
                                    } else {
                                        v___x_177_ = crate::leanh::lean_box(2);
                                        return v___x_177_;
                                    }
                                } else {
                                    v___x_178_ = crate::leanh::lean_box(1);
                                    return v___x_178_;
                                }
                            } else {
                                v___x_179_ = crate::leanh::lean_box(9);
                                return v___x_179_;
                            }
                        } else {
                            v___x_180_ = crate::leanh::lean_box(0);
                            return v___x_180_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_144_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_IR_nameToIRType___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_IR_nameToIRType___closed__3_once),
                    _init_l_Lean_IR_nameToIRType___closed__3,
                );
                v___x_145_ = l_panic___at___00Lean_IR_nameToIRType_spec__0(v___x_144_);
                return v___x_145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_nameToIRType___boxed(
    mut v_n_181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_182_ = l_Lean_IR_nameToIRType(v_n_181_);
    crate::leanh::lean_dec(v_n_181_);
    return v_res_182_;
}
pub unsafe fn _init_l_Lean_IR_toIRType___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_184_ = l_Lean_IR_nameToIRType___closed__2;
    v___x_185_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_186_ = crate::leanh::lean_unsigned_to_nat(49);
    v___x_187_ = l_Lean_IR_toIRType___closed__0;
    v___x_188_ = l_Lean_IR_nameToIRType___closed__0;
    v___x_189_ =
        l_mkPanicMessageWithDecl(v___x_188_, v___x_187_, v___x_186_, v___x_185_, v___x_184_);
    return v___x_189_;
}
pub unsafe fn l_Lean_IR_toIRType(
    mut v_type_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: u8 = 0;
    let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_202_: u8 = 0;
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: u8 = 0;
    let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: u8 = 0;
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_208_: u8 = 0;
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: u8 = 0;
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: u8 = 0;
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: u8 = 0;
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: u8 = 0;
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: u8 = 0;
    let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: u8 = 0;
    let mut v___x_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: u8 = 0;
    let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_type_191_) == 4 {
                    v_declName_195_ = crate::leanh::lean_ctor_get(v_type_191_, 0);
                    if crate::leanh::lean_obj_tag(v_declName_195_) == 1 {
                        v_pre_196_ = crate::leanh::lean_ctor_get(v_declName_195_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_196_) == 0 {
                            v_us_197_ = crate::leanh::lean_ctor_get(v_type_191_, 1);
                            v_str_198_ = crate::leanh::lean_ctor_get(v_declName_195_, 1);
                            v___x_199_ = l_Lean_IR_nameToIRType___closed__4;
                            v___x_200_ = lean_string_dec_eq(v_str_198_, v___x_199_);
                            if v___x_200_ == 0 {
                                v___x_201_ = l_Lean_IR_nameToIRType___closed__5;
                                v___x_202_ = lean_string_dec_eq(v_str_198_, v___x_201_);
                                if v___x_202_ == 0 {
                                    v___x_203_ = l_Lean_IR_nameToIRType___closed__6;
                                    v___x_204_ = lean_string_dec_eq(v_str_198_, v___x_203_);
                                    if v___x_204_ == 0 {
                                        v___x_205_ = l_Lean_IR_nameToIRType___closed__7;
                                        v___x_206_ = lean_string_dec_eq(v_str_198_, v___x_205_);
                                        if v___x_206_ == 0 {
                                            v___x_207_ = l_Lean_IR_nameToIRType___closed__8;
                                            v___x_208_ = lean_string_dec_eq(v_str_198_, v___x_207_);
                                            if v___x_208_ == 0 {
                                                v___x_209_ = l_Lean_IR_nameToIRType___closed__9;
                                                v___x_210_ =
                                                    lean_string_dec_eq(v_str_198_, v___x_209_);
                                                if v___x_210_ == 0 {
                                                    v___x_211_ = l_Lean_IR_toIRType___closed__2;
                                                    v___x_212_ =
                                                        lean_string_dec_eq(v_str_198_, v___x_211_);
                                                    if v___x_212_ == 0 {
                                                        v___x_213_ =
                                                            l_Lean_IR_nameToIRType___closed__10;
                                                        v___x_214_ = lean_string_dec_eq(
                                                            v_str_198_, v___x_213_,
                                                        );
                                                        if v___x_214_ == 0 {
                                                            v___x_215_ =
                                                                l_Lean_IR_nameToIRType___closed__11;
                                                            v___x_216_ = lean_string_dec_eq(
                                                                v_str_198_, v___x_215_,
                                                            );
                                                            if v___x_216_ == 0 {
                                                                v___x_217_ = l_Lean_IR_nameToIRType___closed__12;
                                                                v___x_218_ = lean_string_dec_eq(
                                                                    v_str_198_, v___x_217_,
                                                                );
                                                                if v___x_218_ == 0 {
                                                                    v___x_219_ = l_Lean_IR_nameToIRType___closed__13;
                                                                    v___x_220_ = lean_string_dec_eq(
                                                                        v_str_198_, v___x_219_,
                                                                    );
                                                                    if v___x_220_ == 0 {
                                                                        v___x_221_ = l_Lean_IR_nameToIRType___closed__14;
                                                                        v___x_222_ =
                                                                            lean_string_dec_eq(
                                                                                v_str_198_,
                                                                                v___x_221_,
                                                                            );
                                                                        if v___x_222_ == 0 {
                                                                            state = 1;
                                                                            continue;
                                                                        } else {
                                                                            if crate::leanh::lean_obj_tag(v_us_197_) == 0 {
v___x_223_ = crate::leanh::lean_box(13);
return v___x_223_;
} else {
state = 1; continue;
}
                                                                        }
                                                                    } else {
                                                                        if crate::leanh::lean_obj_tag(v_us_197_) == 0 {
v___x_224_ = crate::leanh::lean_box(12);
return v___x_224_;
} else {
state = 1; continue;
}
                                                                    }
                                                                } else {
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v_us_197_,
                                                                    ) == 0
                                                                    {
                                                                        v___x_225_ =
                                                                            crate::leanh::lean_box(
                                                                                8,
                                                                            );
                                                                        return v___x_225_;
                                                                    } else {
                                                                        state = 1;
                                                                        continue;
                                                                    }
                                                                }
                                                            } else {
                                                                if crate::leanh::lean_obj_tag(
                                                                    v_us_197_,
                                                                ) == 0
                                                                {
                                                                    v___x_226_ =
                                                                        crate::leanh::lean_box(7);
                                                                    return v___x_226_;
                                                                } else {
                                                                    state = 1;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            if crate::leanh::lean_obj_tag(v_us_197_)
                                                                == 0
                                                            {
                                                                v___x_227_ =
                                                                    crate::leanh::lean_box(6);
                                                                return v___x_227_;
                                                            } else {
                                                                state = 1;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        if crate::leanh::lean_obj_tag(v_us_197_)
                                                            == 0
                                                        {
                                                            v___x_228_ = crate::leanh::lean_box(5);
                                                            return v___x_228_;
                                                        } else {
                                                            state = 1;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    if crate::leanh::lean_obj_tag(v_us_197_) == 0 {
                                                        v___x_229_ = crate::leanh::lean_box(4);
                                                        return v___x_229_;
                                                    } else {
                                                        state = 1;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                if crate::leanh::lean_obj_tag(v_us_197_) == 0 {
                                                    v___x_230_ = crate::leanh::lean_box(3);
                                                    return v___x_230_;
                                                } else {
                                                    state = 1;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            if crate::leanh::lean_obj_tag(v_us_197_) == 0 {
                                                v___x_231_ = crate::leanh::lean_box(2);
                                                return v___x_231_;
                                            } else {
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    } else {
                                        if crate::leanh::lean_obj_tag(v_us_197_) == 0 {
                                            v___x_232_ = crate::leanh::lean_box(1);
                                            return v___x_232_;
                                        } else {
                                            state = 1;
                                            continue;
                                        }
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v_us_197_) == 0 {
                                        v___x_233_ = crate::leanh::lean_box(9);
                                        return v___x_233_;
                                    } else {
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                if crate::leanh::lean_obj_tag(v_us_197_) == 0 {
                                    v___x_234_ = crate::leanh::lean_box(0);
                                    return v___x_234_;
                                } else {
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_193_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_IR_toIRType___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_IR_toIRType___closed__1_once),
                    _init_l_Lean_IR_toIRType___closed__1,
                );
                v___x_194_ = l_panic___at___00Lean_IR_nameToIRType_spec__0(v___x_193_);
                return v___x_194_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_toIRType___boxed(
    mut v_type_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_236_ = l_Lean_IR_toIRType(v_type_235_);
    crate::leanh::lean_dec_ref(v_type_235_);
    return v_res_236_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_ToIRType(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_IR_Format(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_ToIRType(
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
pub unsafe fn initialize_Lean_Compiler_IR_ToIRType(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_IR_Format(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_ToIRType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_ToIRType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_ToIRType(builtin);
}
