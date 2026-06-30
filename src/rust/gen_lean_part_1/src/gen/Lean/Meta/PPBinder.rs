// Lean compiler output
// Module: Lean.Meta.PPBinder
// Imports: Lean.Meta.Basic
use crate::r#gen::Lean::Expr::l_Lean_mkFVar;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_bracket, l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_FVarId_getDecl___redArg, runtime_initialize_Lean_Meta_Basic,
};
pub static l_Lean_LocalDecl_ppAsBinder___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [32, 58, 32, 0],
    };
static mut l_Lean_LocalDecl_ppAsBinder___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LocalDecl_ppAsBinder___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_LocalDecl_ppAsBinder___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_LocalDecl_ppAsBinder___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_LocalDecl_ppAsBinder___closed__2_value: leanh::LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Lean_LocalDecl_ppAsBinder___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LocalDecl_ppAsBinder___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_LocalDecl_ppAsBinder___closed__3_value: leanh::LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_Lean_LocalDecl_ppAsBinder___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LocalDecl_ppAsBinder___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_LocalDecl_ppAsBinder___closed__4_value: leanh::LeanStringObject<2> =
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
        m_data: [123, 0],
    };
static mut l_Lean_LocalDecl_ppAsBinder___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LocalDecl_ppAsBinder___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_LocalDecl_ppAsBinder___closed__5_value: leanh::LeanStringObject<2> =
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
        m_data: [125, 0],
    };
static mut l_Lean_LocalDecl_ppAsBinder___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LocalDecl_ppAsBinder___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_LocalDecl_ppAsBinder___closed__6_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 166, 131, 0],
    };
static mut l_Lean_LocalDecl_ppAsBinder___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LocalDecl_ppAsBinder___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_LocalDecl_ppAsBinder___closed__7_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 166, 132, 0],
    };
static mut l_Lean_LocalDecl_ppAsBinder___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LocalDecl_ppAsBinder___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_LocalDecl_ppAsBinder___closed__8_value: leanh::LeanStringObject<2> =
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
        m_data: [91, 0],
    };
static mut l_Lean_LocalDecl_ppAsBinder___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LocalDecl_ppAsBinder___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_LocalDecl_ppAsBinder___closed__9_value: leanh::LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_Lean_LocalDecl_ppAsBinder___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LocalDecl_ppAsBinder___closed__9_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_LocalDecl_ppAsBinder___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_97_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_97_ = l_Lean_LocalDecl_ppAsBinder___closed__0;
    v___x_98_ = l_Lean_stringToMessageData(v___x_97_);
    return v___x_98_;
}
pub unsafe fn l_Lean_LocalDecl_ppAsBinder(
    mut v_x_107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarId_108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bi_110_: u8 = 0;
    let mut v_fst_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_107_) == 0 {
                    v_fvarId_108_ = leanh::lean_ctor_get(v_x_107_, 1);
                    leanh::lean_inc(v_fvarId_108_);
                    v_type_109_ = leanh::lean_ctor_get(v_x_107_, 3);
                    leanh::lean_inc_ref(v_type_109_);
                    v_bi_110_ = leanh::lean_ctor_get_uint8(
                        v_x_107_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    );
                    leanh::lean_dec_ref_known(v_x_107_, 4);
                    match v_bi_110_ {
                        0 => {
                            v___x_122_ = l_Lean_LocalDecl_ppAsBinder___closed__2;
                            v___x_123_ = l_Lean_LocalDecl_ppAsBinder___closed__3;
                            v_fst_112_ = v___x_122_;
                            v_snd_113_ = v___x_123_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v___x_124_ = l_Lean_LocalDecl_ppAsBinder___closed__4;
                            v___x_125_ = l_Lean_LocalDecl_ppAsBinder___closed__5;
                            v_fst_112_ = v___x_124_;
                            v_snd_113_ = v___x_125_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v___x_126_ = l_Lean_LocalDecl_ppAsBinder___closed__6;
                            v___x_127_ = l_Lean_LocalDecl_ppAsBinder___closed__7;
                            v_fst_112_ = v___x_126_;
                            v_snd_113_ = v___x_127_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___x_128_ = l_Lean_LocalDecl_ppAsBinder___closed__8;
                            v___x_129_ = l_Lean_LocalDecl_ppAsBinder___closed__9;
                            v_fst_112_ = v___x_128_;
                            v_snd_113_ = v___x_129_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v_x_107_, 5);
                    v___x_130_ = leanh::lean_box(0);
                    return v___x_130_;
                }
            }
            1 => {
                v___x_114_ = l_Lean_mkFVar(v_fvarId_108_);
                v___x_115_ = l_Lean_MessageData_ofExpr(v___x_114_);
                v___x_116_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_LocalDecl_ppAsBinder___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_LocalDecl_ppAsBinder___closed__1_once),
                    _init_l_Lean_LocalDecl_ppAsBinder___closed__1,
                );
                v___x_117_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_117_, 0, v___x_115_);
                leanh::lean_ctor_set(v___x_117_, 1, v___x_116_);
                v___x_118_ = l_Lean_MessageData_ofExpr(v_type_109_);
                v___x_119_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_119_, 0, v___x_117_);
                leanh::lean_ctor_set(v___x_119_, 1, v___x_118_);
                leanh::lean_inc_ref(v_snd_113_);
                leanh::lean_inc_ref(v_fst_112_);
                v___x_120_ = l_Lean_MessageData_bracket(v_fst_112_, v___x_119_, v_snd_113_);
                v___x_121_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_121_, 0, v___x_120_);
                return v___x_121_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FVarId_ppAsBinder___redArg(
    mut v_fvarId_131_: *mut leanh::LeanObject,
    mut v_a_132_: *mut leanh::LeanObject,
    mut v_a_133_: *mut leanh::LeanObject,
    mut v_a_134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_140_: u8 = 0;
    let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_145_: u8 = 0;
    let mut v_a_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_149_: u8 = 0;
    let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_136_ =
                    l_Lean_FVarId_getDecl___redArg(v_fvarId_131_, v_a_132_, v_a_133_, v_a_134_);
                if leanh::lean_obj_tag(v___x_136_) == 0 {
                    v_a_137_ = leanh::lean_ctor_get(v___x_136_, 0);
                    v_isSharedCheck_145_ = (!leanh::lean_is_exclusive(v___x_136_)) as u8;
                    if v_isSharedCheck_145_ == 0 {
                        v___x_139_ = v___x_136_;
                        v_isShared_140_ = v_isSharedCheck_145_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_137_);
                        leanh::lean_dec(v___x_136_);
                        v___x_139_ = leanh::lean_box(0);
                        v_isShared_140_ = v_isSharedCheck_145_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_146_ = leanh::lean_ctor_get(v___x_136_, 0);
                    v_isSharedCheck_153_ = (!leanh::lean_is_exclusive(v___x_136_)) as u8;
                    if v_isSharedCheck_153_ == 0 {
                        v___x_148_ = v___x_136_;
                        v_isShared_149_ = v_isSharedCheck_153_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_146_);
                        leanh::lean_dec(v___x_136_);
                        v___x_148_ = leanh::lean_box(0);
                        v_isShared_149_ = v_isSharedCheck_153_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_141_ = l_Lean_LocalDecl_ppAsBinder(v_a_137_);
                if v_isShared_140_ == 0 {
                    leanh::lean_ctor_set(v___x_139_, 0, v___x_141_);
                    v___x_143_ = v___x_139_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_144_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_141_);
                    v___x_143_ = v_reuseFailAlloc_144_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_143_;
            }
            3 => {
                if v_isShared_149_ == 0 {
                    v___x_151_ = v___x_148_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_152_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
                    v___x_151_ = v_reuseFailAlloc_152_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_151_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FVarId_ppAsBinder___redArg___boxed(
    mut v_fvarId_154_: *mut leanh::LeanObject,
    mut v_a_155_: *mut leanh::LeanObject,
    mut v_a_156_: *mut leanh::LeanObject,
    mut v_a_157_: *mut leanh::LeanObject,
    mut v_a_158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_159_ = l_Lean_FVarId_ppAsBinder___redArg(v_fvarId_154_, v_a_155_, v_a_156_, v_a_157_);
    leanh::lean_dec(v_a_157_);
    leanh::lean_dec_ref(v_a_156_);
    leanh::lean_dec_ref(v_a_155_);
    return v_res_159_;
}
pub unsafe fn l_Lean_FVarId_ppAsBinder(
    mut v_fvarId_160_: *mut leanh::LeanObject,
    mut v_a_161_: *mut leanh::LeanObject,
    mut v_a_162_: *mut leanh::LeanObject,
    mut v_a_163_: *mut leanh::LeanObject,
    mut v_a_164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_170_: u8 = 0;
    let mut v___x_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_175_: u8 = 0;
    let mut v_a_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_179_: u8 = 0;
    let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_183_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_166_ =
                    l_Lean_FVarId_getDecl___redArg(v_fvarId_160_, v_a_161_, v_a_163_, v_a_164_);
                if leanh::lean_obj_tag(v___x_166_) == 0 {
                    v_a_167_ = leanh::lean_ctor_get(v___x_166_, 0);
                    v_isSharedCheck_175_ = (!leanh::lean_is_exclusive(v___x_166_)) as u8;
                    if v_isSharedCheck_175_ == 0 {
                        v___x_169_ = v___x_166_;
                        v_isShared_170_ = v_isSharedCheck_175_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_167_);
                        leanh::lean_dec(v___x_166_);
                        v___x_169_ = leanh::lean_box(0);
                        v_isShared_170_ = v_isSharedCheck_175_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_176_ = leanh::lean_ctor_get(v___x_166_, 0);
                    v_isSharedCheck_183_ = (!leanh::lean_is_exclusive(v___x_166_)) as u8;
                    if v_isSharedCheck_183_ == 0 {
                        v___x_178_ = v___x_166_;
                        v_isShared_179_ = v_isSharedCheck_183_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_176_);
                        leanh::lean_dec(v___x_166_);
                        v___x_178_ = leanh::lean_box(0);
                        v_isShared_179_ = v_isSharedCheck_183_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_171_ = l_Lean_LocalDecl_ppAsBinder(v_a_167_);
                if v_isShared_170_ == 0 {
                    leanh::lean_ctor_set(v___x_169_, 0, v___x_171_);
                    v___x_173_ = v___x_169_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_174_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
                    v___x_173_ = v_reuseFailAlloc_174_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_173_;
            }
            3 => {
                if v_isShared_179_ == 0 {
                    v___x_181_ = v___x_178_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_182_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
                    v___x_181_ = v_reuseFailAlloc_182_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_181_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FVarId_ppAsBinder___boxed(
    mut v_fvarId_184_: *mut leanh::LeanObject,
    mut v_a_185_: *mut leanh::LeanObject,
    mut v_a_186_: *mut leanh::LeanObject,
    mut v_a_187_: *mut leanh::LeanObject,
    mut v_a_188_: *mut leanh::LeanObject,
    mut v_a_189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_190_ = l_Lean_FVarId_ppAsBinder(v_fvarId_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
    leanh::lean_dec(v_a_188_);
    leanh::lean_dec_ref(v_a_187_);
    leanh::lean_dec(v_a_186_);
    leanh::lean_dec_ref(v_a_185_);
    return v_res_190_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_PPBinder(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_PPBinder(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_PPBinder(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_PPBinder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_PPBinder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_PPBinder(builtin);
}