// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Take
// Imports: Init.Data.Iterators.Combinators.Monadic.Take
use crate::ffi::lean_nat_add;
use crate::r#gen::Init::Data::Iterators::Combinators::Monadic::Take::{
    initialize_Init_Data_Iterators_Combinators_Monadic_Take,
    runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take,
};
pub unsafe fn l_Std_Iter_take___redArg(
    mut v_n_39_: *mut leanh::LeanObject,
    mut v_it_40_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_41_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_42_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_43_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_41_ = leanh::lean_unsigned_to_nat(1);
    v___x_42_ = lean_nat_add(v_n_39_, v___x_41_);
    v___x_43_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_43_, 0, v___x_42_);
    leanh::lean_ctor_set(v___x_43_, 1, v_it_40_);
    return v___x_43_;
}
pub unsafe fn l_Std_Iter_take___redArg___boxed(
    mut v_n_44_: *mut leanh::LeanObject,
    mut v_it_45_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_46_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Std_Iter_take___redArg(v_n_44_, v_it_45_);
    leanh::lean_dec(v_n_44_);
    return v_res_46_;
}
pub unsafe fn l_Std_Iter_take(
    mut v_00_u03b1_47_: *mut leanh::LeanObject,
    mut v_00_u03b2_48_: *mut leanh::LeanObject,
    mut v_inst_49_: *mut leanh::LeanObject,
    mut v_n_50_: *mut leanh::LeanObject,
    mut v_it_51_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_52_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_53_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_54_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_52_ = leanh::lean_unsigned_to_nat(1);
    v___x_53_ = lean_nat_add(v_n_50_, v___x_52_);
    v___x_54_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_54_, 0, v___x_53_);
    leanh::lean_ctor_set(v___x_54_, 1, v_it_51_);
    return v___x_54_;
}
pub unsafe fn l_Std_Iter_take___boxed(
    mut v_00_u03b1_55_: *mut leanh::LeanObject,
    mut v_00_u03b2_56_: *mut leanh::LeanObject,
    mut v_inst_57_: *mut leanh::LeanObject,
    mut v_n_58_: *mut leanh::LeanObject,
    mut v_it_59_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_60_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_60_ = l_Std_Iter_take(
        v_00_u03b1_55_,
        v_00_u03b2_56_,
        v_inst_57_,
        v_n_58_,
        v_it_59_,
    );
    leanh::lean_dec(v_n_58_);
    leanh::lean_dec(v_inst_57_);
    return v_res_60_;
}
pub unsafe fn l_Std_Iter_toTake___redArg(
    mut v_it_61_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_62_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_62_ = leanh::lean_unsigned_to_nat(0);
    v___x_63_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_63_, 0, v___x_62_);
    leanh::lean_ctor_set(v___x_63_, 1, v_it_61_);
    return v___x_63_;
}
pub unsafe fn l_Std_Iter_toTake(
    mut v_00_u03b1_64_: *mut leanh::LeanObject,
    mut v_00_u03b2_65_: *mut leanh::LeanObject,
    mut v_inst_66_: *mut leanh::LeanObject,
    mut v_inst_67_: *mut leanh::LeanObject,
    mut v_it_68_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_69_ = leanh::lean_unsigned_to_nat(0);
    v___x_70_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_70_, 0, v___x_69_);
    leanh::lean_ctor_set(v___x_70_, 1, v_it_68_);
    return v___x_70_;
}
pub unsafe fn l_Std_Iter_toTake___boxed(
    mut v_00_u03b1_71_: *mut leanh::LeanObject,
    mut v_00_u03b2_72_: *mut leanh::LeanObject,
    mut v_inst_73_: *mut leanh::LeanObject,
    mut v_inst_74_: *mut leanh::LeanObject,
    mut v_it_75_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_76_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_76_ = l_Std_Iter_toTake(
        v_00_u03b1_71_,
        v_00_u03b2_72_,
        v_inst_73_,
        v_inst_74_,
        v_it_75_,
    );
    leanh::lean_dec(v_inst_73_);
    return v_res_76_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Take(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Take(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Take(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Take(builtin);
}