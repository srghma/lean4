// Lean compiler output
// Module: Std.Data.Internal.List.Defs
// Imports: Init.BinderPredicates Init.NotationExtra
use crate::r#gen::Init::BinderPredicates::{
    initialize_Init_BinderPredicates, runtime_initialize_Init_BinderPredicates,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
pub unsafe fn l_Std_Internal_List_keys___redArg(
    mut v_x_35_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_36_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_37_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_38_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_40_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_41_: u8 = 0;
    let mut v_fst_42_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_43_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_45_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_46_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_47_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_35_) == 0 {
                    v___x_36_ = leanh::lean_box(0);
                    return v___x_36_;
                } else {
                    v_head_37_ = leanh::lean_ctor_get(v_x_35_, 0);
                    v_tail_38_ = leanh::lean_ctor_get(v_x_35_, 1);
                    v_isSharedCheck_47_ = (!leanh::lean_is_exclusive(v_x_35_)) as u8;
                    if v_isSharedCheck_47_ == 0 {
                        v___x_40_ = v_x_35_;
                        v_isShared_41_ = v_isSharedCheck_47_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_38_);
                        leanh::lean_inc(v_head_37_);
                        leanh::lean_dec(v_x_35_);
                        v___x_40_ = leanh::lean_box(0);
                        v_isShared_41_ = v_isSharedCheck_47_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_42_ = leanh::lean_ctor_get(v_head_37_, 0);
                leanh::lean_inc(v_fst_42_);
                leanh::lean_dec(v_head_37_);
                v___x_43_ = l_Std_Internal_List_keys___redArg(v_tail_38_);
                if v_isShared_41_ == 0 {
                    leanh::lean_ctor_set(v___x_40_, 1, v___x_43_);
                    leanh::lean_ctor_set(v___x_40_, 0, v_fst_42_);
                    v___x_45_ = v___x_40_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_46_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_46_, 0, v_fst_42_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_46_, 1, v___x_43_);
                    v___x_45_ = v_reuseFailAlloc_46_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_45_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_keys(
    mut v_00_u03b1_48_: *mut leanh::LeanObject,
    mut v_00_u03b2_49_: *mut leanh::LeanObject,
    mut v_x_50_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_51_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_51_ = l_Std_Internal_List_keys___redArg(v_x_50_);
    return v___x_51_;
}
pub unsafe fn l_Std_Internal_List_values___redArg(
    mut v_x_52_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_53_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_54_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_55_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_57_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_58_: u8 = 0;
    let mut v_snd_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_60_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_63_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_64_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_52_) == 0 {
                    v___x_53_ = leanh::lean_box(0);
                    return v___x_53_;
                } else {
                    v_head_54_ = leanh::lean_ctor_get(v_x_52_, 0);
                    v_tail_55_ = leanh::lean_ctor_get(v_x_52_, 1);
                    v_isSharedCheck_64_ = (!leanh::lean_is_exclusive(v_x_52_)) as u8;
                    if v_isSharedCheck_64_ == 0 {
                        v___x_57_ = v_x_52_;
                        v_isShared_58_ = v_isSharedCheck_64_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_55_);
                        leanh::lean_inc(v_head_54_);
                        leanh::lean_dec(v_x_52_);
                        v___x_57_ = leanh::lean_box(0);
                        v_isShared_58_ = v_isSharedCheck_64_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_59_ = leanh::lean_ctor_get(v_head_54_, 1);
                leanh::lean_inc(v_snd_59_);
                leanh::lean_dec(v_head_54_);
                v___x_60_ = l_Std_Internal_List_values___redArg(v_tail_55_);
                if v_isShared_58_ == 0 {
                    leanh::lean_ctor_set(v___x_57_, 1, v___x_60_);
                    leanh::lean_ctor_set(v___x_57_, 0, v_snd_59_);
                    v___x_62_ = v___x_57_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_63_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_63_, 0, v_snd_59_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_63_, 1, v___x_60_);
                    v___x_62_ = v_reuseFailAlloc_63_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_62_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_List_values(
    mut v_00_u03b1_65_: *mut leanh::LeanObject,
    mut v_00_u03b2_66_: *mut leanh::LeanObject,
    mut v_x_67_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_68_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_68_ = l_Std_Internal_List_values___redArg(v_x_67_);
    return v___x_68_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Internal_List_Defs(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Internal_List_Defs(
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
pub unsafe fn initialize_Std_Data_Internal_List_Defs(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_BinderPredicates(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Internal_List_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Internal_List_Defs(builtin);
}