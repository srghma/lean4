// Lean compiler output
// Module: Std.Data.Internal.List.Defs
// Imports: Init.BinderPredicates Init.NotationExtra
use crate::r#gen::Init::BinderPredicates::{
    initialize_Init_BinderPredicates, runtime_initialize_Init_BinderPredicates,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_tag,
};
pub unsafe fn l_Std_Internal_List_keys___redArg(mut v_x_35_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_37_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_38_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_40_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_41_: u8 = 0;
    let mut v_fst_42_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_43_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_45_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_46_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_47_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_35_) == 0 {
                    v___x_36_ = lean_box(0);
                    return v___x_36_;
                } else {
                    v_head_37_ = lean_ctor_get(v_x_35_, 0);
                    v_tail_38_ = lean_ctor_get(v_x_35_, 1);
                    v_isSharedCheck_47_ = (!lean_is_exclusive(v_x_35_)) as u8;
                    if v_isSharedCheck_47_ == 0 {
                        v___x_40_ = v_x_35_;
                        v_isShared_41_ = v_isSharedCheck_47_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_38_);
                        lean_inc(v_head_37_);
                        lean_dec(v_x_35_);
                        v___x_40_ = lean_box(0);
                        v_isShared_41_ = v_isSharedCheck_47_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_42_ = lean_ctor_get(v_head_37_, 0);
                lean_inc(v_fst_42_);
                lean_dec(v_head_37_);
                v___x_43_ = l_Std_Internal_List_keys___redArg(v_tail_38_);
                if v_isShared_41_ == 0 {
                    lean_ctor_set(v___x_40_, 1, v___x_43_);
                    lean_ctor_set(v___x_40_, 0, v_fst_42_);
                    v___x_45_ = v___x_40_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_46_, 0, v_fst_42_);
                    lean_ctor_set(v_reuseFailAlloc_46_, 1, v___x_43_);
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
    mut v_00_u03b1_48_: *mut LeanObject,
    mut v_00_u03b2_49_: *mut LeanObject,
    mut v_x_50_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_51_: *mut LeanObject = core::ptr::null_mut();
    v___x_51_ = l_Std_Internal_List_keys___redArg(v_x_50_);
    return v___x_51_;
}
pub unsafe fn l_Std_Internal_List_values___redArg(mut v_x_52_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_53_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_54_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_55_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_57_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_58_: u8 = 0;
    let mut v_snd_59_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_63_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_64_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_52_) == 0 {
                    v___x_53_ = lean_box(0);
                    return v___x_53_;
                } else {
                    v_head_54_ = lean_ctor_get(v_x_52_, 0);
                    v_tail_55_ = lean_ctor_get(v_x_52_, 1);
                    v_isSharedCheck_64_ = (!lean_is_exclusive(v_x_52_)) as u8;
                    if v_isSharedCheck_64_ == 0 {
                        v___x_57_ = v_x_52_;
                        v_isShared_58_ = v_isSharedCheck_64_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_55_);
                        lean_inc(v_head_54_);
                        lean_dec(v_x_52_);
                        v___x_57_ = lean_box(0);
                        v_isShared_58_ = v_isSharedCheck_64_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_59_ = lean_ctor_get(v_head_54_, 1);
                lean_inc(v_snd_59_);
                lean_dec(v_head_54_);
                v___x_60_ = l_Std_Internal_List_values___redArg(v_tail_55_);
                if v_isShared_58_ == 0 {
                    lean_ctor_set(v___x_57_, 1, v___x_60_);
                    lean_ctor_set(v___x_57_, 0, v_snd_59_);
                    v___x_62_ = v___x_57_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_63_, 0, v_snd_59_);
                    lean_ctor_set(v_reuseFailAlloc_63_, 1, v___x_60_);
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
    mut v_00_u03b1_65_: *mut LeanObject,
    mut v_00_u03b2_66_: *mut LeanObject,
    mut v_x_67_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_68_: *mut LeanObject = core::ptr::null_mut();
    v___x_68_ = l_Std_Internal_List_values___redArg(v_x_67_);
    return v___x_68_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Internal_List_Defs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Internal_List_Defs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_Internal_List_Defs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_BinderPredicates(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Internal_List_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Internal_List_Defs(builtin);
}
