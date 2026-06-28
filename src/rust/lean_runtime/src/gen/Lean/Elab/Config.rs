// Lean compiler output
// Module: Lean.Elab.Config
// Imports: Lean.Meta.Basic
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, runtime_initialize_Lean_Meta_Basic,
};
pub unsafe fn l_Lean_Elab_Term_setElabConfig(
    mut v_cfg_26_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isDefEqStuckEx_27_: u8 = 0;
    let mut v_unificationHints_28_: u8 = 0;
    let mut v_proofIrrelevance_29_: u8 = 0;
    let mut v_assignSyntheticOpaque_30_: u8 = 0;
    let mut v_offsetCnstrs_31_: u8 = 0;
    let mut v_transparency_32_: u8 = 0;
    let mut v_etaStruct_33_: u8 = 0;
    let mut v_univApprox_34_: u8 = 0;
    let mut v_iota_35_: u8 = 0;
    let mut v_beta_36_: u8 = 0;
    let mut v_proj_37_: u8 = 0;
    let mut v_zeta_38_: u8 = 0;
    let mut v_zetaDelta_39_: u8 = 0;
    let mut v_zetaUnused_40_: u8 = 0;
    let mut v_zetaHave_41_: u8 = 0;
    let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_44_: u8 = 0;
    let mut v___x_45_: u8 = 0;
    let mut v___x_46_: u8 = 0;
    let mut v___x_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_50_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isDefEqStuckEx_27_ = crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 4 as u32);
                v_unificationHints_28_ = crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 5 as u32);
                v_proofIrrelevance_29_ = crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 6 as u32);
                v_assignSyntheticOpaque_30_ =
                    crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 7 as u32);
                v_offsetCnstrs_31_ = crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 8 as u32);
                v_transparency_32_ = crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 9 as u32);
                v_etaStruct_33_ = crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 10 as u32);
                v_univApprox_34_ = crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 11 as u32);
                v_iota_35_ = crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 12 as u32);
                v_beta_36_ = crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 13 as u32);
                v_proj_37_ = crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 14 as u32);
                v_zeta_38_ = crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 15 as u32);
                v_zetaDelta_39_ = crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 16 as u32);
                v_zetaUnused_40_ = crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 17 as u32);
                v_zetaHave_41_ = crate::leanh::lean_ctor_get_uint8(v_cfg_26_, 18 as u32);
                v_isSharedCheck_50_ = (!crate::leanh::lean_is_exclusive(v_cfg_26_)) as u8;
                if v_isSharedCheck_50_ == 0 {
                    v___x_43_ = v_cfg_26_;
                    v_isShared_44_ = v_isSharedCheck_50_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_cfg_26_);
                    v___x_43_ = crate::leanh::lean_box(0);
                    v_isShared_44_ = v_isSharedCheck_50_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_45_ = 1;
                v___x_46_ = 0;
                if v_isShared_44_ == 0 {
                    v___x_48_ = v___x_43_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_49_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_49_,
                        4 as u32,
                        v_isDefEqStuckEx_27_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_49_,
                        5 as u32,
                        v_unificationHints_28_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_49_,
                        6 as u32,
                        v_proofIrrelevance_29_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_49_,
                        7 as u32,
                        v_assignSyntheticOpaque_30_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_49_,
                        8 as u32,
                        v_offsetCnstrs_31_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_49_,
                        9 as u32,
                        v_transparency_32_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_49_,
                        10 as u32,
                        v_etaStruct_33_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_49_,
                        11 as u32,
                        v_univApprox_34_,
                    );
                    crate::leanh::lean_ctor_set_uint8(v_reuseFailAlloc_49_, 12 as u32, v_iota_35_);
                    crate::leanh::lean_ctor_set_uint8(v_reuseFailAlloc_49_, 13 as u32, v_beta_36_);
                    crate::leanh::lean_ctor_set_uint8(v_reuseFailAlloc_49_, 14 as u32, v_proj_37_);
                    crate::leanh::lean_ctor_set_uint8(v_reuseFailAlloc_49_, 15 as u32, v_zeta_38_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_49_,
                        16 as u32,
                        v_zetaDelta_39_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_49_,
                        17 as u32,
                        v_zetaUnused_40_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_49_,
                        18 as u32,
                        v_zetaHave_41_,
                    );
                    v___x_48_ = v_reuseFailAlloc_49_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v___x_48_, 0 as u32, v___x_45_);
                crate::leanh::lean_ctor_set_uint8(v___x_48_, 1 as u32, v___x_45_);
                crate::leanh::lean_ctor_set_uint8(v___x_48_, 2 as u32, v___x_46_);
                crate::leanh::lean_ctor_set_uint8(v___x_48_, 3 as u32, v___x_46_);
                return v___x_48_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Config(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Config(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Config(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Config(builtin);
}
