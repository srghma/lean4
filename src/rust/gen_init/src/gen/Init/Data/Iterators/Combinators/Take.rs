// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Take
// Imports: Init.Data.Iterators.Combinators.Monadic.Take
use crate::ffi::lean_nat_add;
use crate::r#gen::Init::Data::Iterators::Combinators::Monadic::Take::{
    initialize_Init_Data_Iterators_Combinators_Monadic_Take,
    runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take,
};
pub unsafe fn l_Std_Iter_take___redArg(
    mut v_n_39_: *mut crate::leanh::LeanObject,
    mut v_it_40_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_41_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_42_ = lean_nat_add(v_n_39_, v___x_41_);
    v___x_43_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_43_, 0, v___x_42_);
    crate::leanh::lean_ctor_set(v___x_43_, 1, v_it_40_);
    return v___x_43_;
}
pub unsafe fn l_Std_Iter_take___redArg___boxed(
    mut v_n_44_: *mut crate::leanh::LeanObject,
    mut v_it_45_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Std_Iter_take___redArg(v_n_44_, v_it_45_);
    crate::leanh::lean_dec(v_n_44_);
    return v_res_46_;
}
pub unsafe fn l_Std_Iter_take(
    mut v_00_u03b1_47_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_48_: *mut crate::leanh::LeanObject,
    mut v_inst_49_: *mut crate::leanh::LeanObject,
    mut v_n_50_: *mut crate::leanh::LeanObject,
    mut v_it_51_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_52_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_53_ = lean_nat_add(v_n_50_, v___x_52_);
    v___x_54_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_54_, 0, v___x_53_);
    crate::leanh::lean_ctor_set(v___x_54_, 1, v_it_51_);
    return v___x_54_;
}
pub unsafe fn l_Std_Iter_take___boxed(
    mut v_00_u03b1_55_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_56_: *mut crate::leanh::LeanObject,
    mut v_inst_57_: *mut crate::leanh::LeanObject,
    mut v_n_58_: *mut crate::leanh::LeanObject,
    mut v_it_59_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_60_ = l_Std_Iter_take(
        v_00_u03b1_55_,
        v_00_u03b2_56_,
        v_inst_57_,
        v_n_58_,
        v_it_59_,
    );
    crate::leanh::lean_dec(v_n_58_);
    crate::leanh::lean_dec(v_inst_57_);
    return v_res_60_;
}
pub unsafe fn l_Std_Iter_toTake___redArg(
    mut v_it_61_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_62_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_63_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_63_, 0, v___x_62_);
    crate::leanh::lean_ctor_set(v___x_63_, 1, v_it_61_);
    return v___x_63_;
}
pub unsafe fn l_Std_Iter_toTake(
    mut v_00_u03b1_64_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_65_: *mut crate::leanh::LeanObject,
    mut v_inst_66_: *mut crate::leanh::LeanObject,
    mut v_inst_67_: *mut crate::leanh::LeanObject,
    mut v_it_68_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_69_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_69_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_70_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_70_, 0, v___x_69_);
    crate::leanh::lean_ctor_set(v___x_70_, 1, v_it_68_);
    return v___x_70_;
}
pub unsafe fn l_Std_Iter_toTake___boxed(
    mut v_00_u03b1_71_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_72_: *mut crate::leanh::LeanObject,
    mut v_inst_73_: *mut crate::leanh::LeanObject,
    mut v_inst_74_: *mut crate::leanh::LeanObject,
    mut v_it_75_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_76_ = l_Std_Iter_toTake(
        v_00_u03b1_71_,
        v_00_u03b2_72_,
        v_inst_73_,
        v_inst_74_,
        v_it_75_,
    );
    crate::leanh::lean_dec(v_inst_73_);
    return v_res_76_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Take(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Take(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Take(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Take(builtin);
}
