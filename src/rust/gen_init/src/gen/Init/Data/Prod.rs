// Lean compiler output
// Module: Init.Data.Prod
// Imports: Init.NotationExtra
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
pub unsafe fn l_Prod_swap___redArg(
    mut v_p_15_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_16_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_17_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_19_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_20_: u8 = 0;
    let mut v___x_22_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_23_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_24_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_16_ = leanh::lean_ctor_get(v_p_15_, 0);
                v_snd_17_ = leanh::lean_ctor_get(v_p_15_, 1);
                v_isSharedCheck_24_ = (!leanh::lean_is_exclusive(v_p_15_)) as u8;
                if v_isSharedCheck_24_ == 0 {
                    v___x_19_ = v_p_15_;
                    v_isShared_20_ = v_isSharedCheck_24_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_17_);
                    leanh::lean_inc(v_fst_16_);
                    leanh::lean_dec(v_p_15_);
                    v___x_19_ = leanh::lean_box(0);
                    v_isShared_20_ = v_isSharedCheck_24_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_20_ == 0 {
                    leanh::lean_ctor_set(v___x_19_, 1, v_fst_16_);
                    leanh::lean_ctor_set(v___x_19_, 0, v_snd_17_);
                    v___x_22_ = v___x_19_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_23_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_17_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_23_, 1, v_fst_16_);
                    v___x_22_ = v_reuseFailAlloc_23_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_22_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Prod_swap(
    mut v_00_u03b1_25_: *mut leanh::LeanObject,
    mut v_00_u03b2_26_: *mut leanh::LeanObject,
    mut v_p_27_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_28_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_28_ = l_Prod_swap___redArg(v_p_27_);
    return v___x_28_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Prod(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Prod(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Prod(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Prod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Prod(builtin);
}