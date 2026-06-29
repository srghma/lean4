// Lean compiler output
// Module: Lean.Meta.Match.MVarRenaming
// Imports: Lean.Util.ReplaceExpr
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasMVar, l_Lean_mkMVar,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg,
};
use crate::r#gen::Lean::Util::ReplaceExpr::{
    initialize_Lean_Util_ReplaceExpr, runtime_initialize_Lean_Util_ReplaceExpr,
};
use crate::ffi::lean_panic_fn_borrowed;
use crate::ffi::lean_replace_expr;
pub static l_Lean_Meta_MVarRenaming_find_x21___closed__0_value: crate::leanh::LeanStringObject<26> =
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
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97,
            115, 105, 99, 65, 117, 120, 0,
        ],
    };
static mut l_Lean_Meta_MVarRenaming_find_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_MVarRenaming_find_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_MVarRenaming_find_x21___closed__1_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
    };
static mut l_Lean_Meta_MVarRenaming_find_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_MVarRenaming_find_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_MVarRenaming_find_x21___closed__2_value: crate::leanh::LeanStringObject<14> =
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
        m_data: [
            118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
        ],
    };
static mut l_Lean_Meta_MVarRenaming_find_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_MVarRenaming_find_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_MVarRenaming_find_x21___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_MVarRenaming_find_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_MVarRenaming_isEmpty(mut v_s_86_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_s_86_) == 0 {
        let mut v___x_87_: u8 = 0;
        v___x_87_ = 0;
        return v___x_87_;
    } else {
        let mut v___x_88_: u8 = 0;
        v___x_88_ = 1;
        return v___x_88_;
    }
}
pub unsafe fn l_Lean_Meta_MVarRenaming_isEmpty___boxed(
    mut v_s_89_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_90_: u8 = 0;
    let mut v_r_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_90_ = l_Lean_Meta_MVarRenaming_isEmpty(v_s_89_);
    crate::leanh::lean_dec(v_s_89_);
    v_r_91_ = crate::leanh::lean_box((v_res_90_) as usize);
    return v_r_91_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(
    mut v_t_92_: *mut crate::leanh::LeanObject,
    mut v_k_93_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: u8 = 0;
    let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_92_) == 0 {
                    v_k_94_ = crate::leanh::lean_ctor_get(v_t_92_, 1);
                    v_v_95_ = crate::leanh::lean_ctor_get(v_t_92_, 2);
                    v_l_96_ = crate::leanh::lean_ctor_get(v_t_92_, 3);
                    v_r_97_ = crate::leanh::lean_ctor_get(v_t_92_, 4);
                    v___x_98_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_93_, v_k_94_);
                    match v___x_98_ {
                        0 => {
                            v_t_92_ = v_l_96_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_95_);
                            v___x_100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_100_, 0, v_v_95_);
                            return v___x_100_;
                        }
                        _ => {
                            v_t_92_ = v_r_97_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_102_ = crate::leanh::lean_box(0);
                    return v___x_102_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg___boxed(
    mut v_t_103_: *mut crate::leanh::LeanObject,
    mut v_k_104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_105_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_t_103_, v_k_104_);
    crate::leanh::lean_dec(v_k_104_);
    crate::leanh::lean_dec(v_t_103_);
    return v_res_105_;
}
pub unsafe fn l_Lean_Meta_MVarRenaming_find_x3f(
    mut v_s_106_: *mut crate::leanh::LeanObject,
    mut v_mvarId_107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_108_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_s_106_, v_mvarId_107_);
    return v___x_108_;
}
pub unsafe fn l_Lean_Meta_MVarRenaming_find_x3f___boxed(
    mut v_s_109_: *mut crate::leanh::LeanObject,
    mut v_mvarId_110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_111_ = l_Lean_Meta_MVarRenaming_find_x3f(v_s_109_, v_mvarId_110_);
    crate::leanh::lean_dec(v_mvarId_110_);
    crate::leanh::lean_dec(v_s_109_);
    return v_res_111_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0(
    mut v_00_u03b4_112_: *mut crate::leanh::LeanObject,
    mut v_t_113_: *mut crate::leanh::LeanObject,
    mut v_k_114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_115_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_t_113_, v_k_114_);
    return v___x_115_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___boxed(
    mut v_00_u03b4_116_: *mut crate::leanh::LeanObject,
    mut v_t_117_: *mut crate::leanh::LeanObject,
    mut v_k_118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_119_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0(
            v_00_u03b4_116_,
            v_t_117_,
            v_k_118_,
        );
    crate::leanh::lean_dec(v_k_118_);
    crate::leanh::lean_dec(v_t_117_);
    return v_res_119_;
}
pub unsafe fn l_panic___at___00Lean_Meta_MVarRenaming_find_x21_spec__0(
    mut v_msg_120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_121_ = crate::leanh::lean_box(0);
    v___x_122_ = lean_panic_fn_borrowed(v___x_121_, v_msg_120_);
    return v___x_122_;
}
pub unsafe fn _init_l_Lean_Meta_MVarRenaming_find_x21___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_126_ = l_Lean_Meta_MVarRenaming_find_x21___closed__2;
    v___x_127_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_128_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_129_ = l_Lean_Meta_MVarRenaming_find_x21___closed__1;
    v___x_130_ = l_Lean_Meta_MVarRenaming_find_x21___closed__0;
    v___x_131_ =
        l_mkPanicMessageWithDecl(v___x_130_, v___x_129_, v___x_128_, v___x_127_, v___x_126_);
    return v___x_131_;
}
pub unsafe fn l_Lean_Meta_MVarRenaming_find_x21(
    mut v_s_132_: *mut crate::leanh::LeanObject,
    mut v_mvarId_133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_134_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_s_132_, v_mvarId_133_);
    if crate::leanh::lean_obj_tag(v___x_134_) == 0 {
        let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_135_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_MVarRenaming_find_x21___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Meta_MVarRenaming_find_x21___closed__3_once),
            _init_l_Lean_Meta_MVarRenaming_find_x21___closed__3,
        );
        v___x_136_ = l_panic___at___00Lean_Meta_MVarRenaming_find_x21_spec__0(v___x_135_);
        return v___x_136_;
    } else {
        let mut v_val_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_137_ = crate::leanh::lean_ctor_get(v___x_134_, 0);
        crate::leanh::lean_inc(v_val_137_);
        crate::leanh::lean_dec_ref_known(v___x_134_, 1);
        return v_val_137_;
    }
}
pub unsafe fn l_Lean_Meta_MVarRenaming_find_x21___boxed(
    mut v_s_138_: *mut crate::leanh::LeanObject,
    mut v_mvarId_139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_140_ = l_Lean_Meta_MVarRenaming_find_x21(v_s_138_, v_mvarId_139_);
    crate::leanh::lean_dec(v_mvarId_139_);
    crate::leanh::lean_dec(v_s_138_);
    return v_res_140_;
}
pub unsafe fn l_Lean_Meta_MVarRenaming_insert(
    mut v_s_141_: *mut crate::leanh::LeanObject,
    mut v_mvarId_142_: *mut crate::leanh::LeanObject,
    mut v_mvarId_x27_143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_144_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(
            v_mvarId_142_,
            v_mvarId_x27_143_,
            v_s_141_,
        );
    return v___x_144_;
}
pub unsafe fn l_Lean_Meta_MVarRenaming_apply___lam__0(
    mut v_s_145_: *mut crate::leanh::LeanObject,
    mut v_e_146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mvarId_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_153_: u8 = 0;
    let mut v___x_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_158_: u8 = 0;
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_146_) == 2 {
                    v_mvarId_147_ = crate::leanh::lean_ctor_get(v_e_146_, 0);
                    v___x_148_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Meta_MVarRenaming_find_x3f_spec__0___redArg(v_s_145_, v_mvarId_147_);
                    if crate::leanh::lean_obj_tag(v___x_148_) == 0 {
                        v___x_149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_149_, 0, v_e_146_);
                        return v___x_149_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_146_, 1);
                        v_val_150_ = crate::leanh::lean_ctor_get(v___x_148_, 0);
                        v_isSharedCheck_158_ = (!crate::leanh::lean_is_exclusive(v___x_148_)) as u8;
                        if v_isSharedCheck_158_ == 0 {
                            v___x_152_ = v___x_148_;
                            v_isShared_153_ = v_isSharedCheck_158_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_150_);
                            crate::leanh::lean_dec(v___x_148_);
                            v___x_152_ = crate::leanh::lean_box(0);
                            v_isShared_153_ = v_isSharedCheck_158_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_146_);
                    v___x_159_ = crate::leanh::lean_box(0);
                    return v___x_159_;
                }
            }
            1 => {
                v___x_154_ = l_Lean_mkMVar(v_val_150_);
                if v_isShared_153_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_152_, 0, v___x_154_);
                    v___x_156_ = v___x_152_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_157_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
                    v___x_156_ = v_reuseFailAlloc_157_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_156_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_MVarRenaming_apply___lam__0___boxed(
    mut v_s_160_: *mut crate::leanh::LeanObject,
    mut v_e_161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_162_ = l_Lean_Meta_MVarRenaming_apply___lam__0(v_s_160_, v_e_161_);
    crate::leanh::lean_dec(v_s_160_);
    return v_res_162_;
}
pub unsafe fn l_Lean_Meta_MVarRenaming_apply(
    mut v_s_163_: *mut crate::leanh::LeanObject,
    mut v_e_164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_165_: u8 = 0;
    v___x_165_ = l_Lean_Expr_hasMVar(v_e_164_);
    if v___x_165_ == 0 {
        crate::leanh::lean_dec(v_s_163_);
        crate::leanh::lean_inc_ref(v_e_164_);
        return v_e_164_;
    } else {
        if crate::leanh::lean_obj_tag(v_s_163_) == 0 {
            let mut v___f_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___f_166_ = crate::leanh::lean_alloc_closure(
                l_Lean_Meta_MVarRenaming_apply___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            crate::leanh::lean_closure_set(v___f_166_, 0, v_s_163_);
            v___x_167_ = lean_replace_expr(v___f_166_, v_e_164_);
            crate::leanh::lean_dec_ref(v___f_166_);
            return v___x_167_;
        } else {
            crate::leanh::lean_inc_ref(v_e_164_);
            return v_e_164_;
        }
    }
}
pub unsafe fn l_Lean_Meta_MVarRenaming_apply___boxed(
    mut v_s_168_: *mut crate::leanh::LeanObject,
    mut v_e_169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_170_ = l_Lean_Meta_MVarRenaming_apply(v_s_168_, v_e_169_);
    crate::leanh::lean_dec_ref(v_e_169_);
    return v_res_170_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_MVarRenaming(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_ReplaceExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_MVarRenaming(
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
pub unsafe fn initialize_Lean_Meta_Match_MVarRenaming(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_ReplaceExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MVarRenaming(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_MVarRenaming(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Match_MVarRenaming(builtin);
}
