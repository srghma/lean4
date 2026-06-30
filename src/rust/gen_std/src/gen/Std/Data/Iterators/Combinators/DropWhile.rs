// Lean compiler output
// Module: Std.Data.Iterators.Combinators.DropWhile
// Imports: Std.Data.Iterators.Combinators.Monadic.DropWhile
use crate::r#gen::Std::Data::Iterators::Combinators::Monadic::DropWhile::{
    initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile,
    runtime_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile,
};
pub unsafe fn l_Std_Iter_Intermediate_dropWhile___redArg(
    mut v_dropping_35_: u8,
    mut v_it_36_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_37_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_37_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_37_, 0, v_it_36_);
    leanh::lean_ctor_set_uint8(
        v___x_37_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_dropping_35_,
    );
    return v___x_37_;
}
pub unsafe fn l_Std_Iter_Intermediate_dropWhile___redArg___boxed(
    mut v_dropping_38_: *mut leanh::LeanObject,
    mut v_it_39_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dropping_boxed_40_: u8 = 0;
    let mut v_res_41_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_40_ = (leanh::lean_unbox(v_dropping_38_) as u8);
    v_res_41_ = l_Std_Iter_Intermediate_dropWhile___redArg(v_dropping_boxed_40_, v_it_39_);
    return v_res_41_;
}
pub unsafe fn l_Std_Iter_Intermediate_dropWhile(
    mut v_00_u03b2_42_: *mut leanh::LeanObject,
    mut v_00_u03b1_43_: *mut leanh::LeanObject,
    mut v_P_44_: *mut leanh::LeanObject,
    mut v_dropping_45_: u8,
    mut v_it_46_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_47_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_47_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_47_, 0, v_it_46_);
    leanh::lean_ctor_set_uint8(
        v___x_47_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_dropping_45_,
    );
    return v___x_47_;
}
pub unsafe fn l_Std_Iter_Intermediate_dropWhile___boxed(
    mut v_00_u03b2_48_: *mut leanh::LeanObject,
    mut v_00_u03b1_49_: *mut leanh::LeanObject,
    mut v_P_50_: *mut leanh::LeanObject,
    mut v_dropping_51_: *mut leanh::LeanObject,
    mut v_it_52_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dropping_boxed_53_: u8 = 0;
    let mut v_res_54_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_53_ = (leanh::lean_unbox(v_dropping_51_) as u8);
    v_res_54_ = l_Std_Iter_Intermediate_dropWhile(
        v_00_u03b2_48_,
        v_00_u03b1_49_,
        v_P_50_,
        v_dropping_boxed_53_,
        v_it_52_,
    );
    leanh::lean_dec_ref(v_P_50_);
    return v_res_54_;
}
pub unsafe fn l_Std_Iter_dropWhile___redArg(
    mut v_it_55_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_56_: u8 = 0;
    let mut v___x_57_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_56_ = 1;
    v___x_57_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_57_, 0, v_it_55_);
    leanh::lean_ctor_set_uint8(
        v___x_57_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_56_,
    );
    return v___x_57_;
}
pub unsafe fn l_Std_Iter_dropWhile(
    mut v_00_u03b1_58_: *mut leanh::LeanObject,
    mut v_00_u03b2_59_: *mut leanh::LeanObject,
    mut v_P_60_: *mut leanh::LeanObject,
    mut v_it_61_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_62_: u8 = 0;
    let mut v___x_63_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_62_ = 1;
    v___x_63_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_63_, 0, v_it_61_);
    leanh::lean_ctor_set_uint8(
        v___x_63_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_62_,
    );
    return v___x_63_;
}
pub unsafe fn l_Std_Iter_dropWhile___boxed(
    mut v_00_u03b1_64_: *mut leanh::LeanObject,
    mut v_00_u03b2_65_: *mut leanh::LeanObject,
    mut v_P_66_: *mut leanh::LeanObject,
    mut v_it_67_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_68_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_68_ = l_Std_Iter_dropWhile(v_00_u03b1_64_, v_00_u03b2_65_, v_P_66_, v_it_67_);
    leanh::lean_dec_ref(v_P_66_);
    return v_res_68_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_DropWhile(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_DropWhile(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_DropWhile(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
}