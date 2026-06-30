// Lean compiler output
// Module: Init.Data.Iterators.ToIterator
// Imports: Init.Data.Iterators.Basic
use crate::r#gen::Init::Data::Iterators::Basic::{
    initialize_Init_Data_Iterators_Basic, runtime_initialize_Init_Data_Iterators_Basic,
};
pub unsafe fn l_Std_ToIterator_iterM___redArg(
    mut v_x_41_: *mut leanh::LeanObject,
    mut v_inst_42_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_43_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_43_ = leanh::lean_apply_1(v_inst_42_, v_x_41_);
    return v___x_43_;
}
pub unsafe fn l_Std_ToIterator_iterM(
    mut v_00_u03b3_44_: *mut leanh::LeanObject,
    mut v_m_45_: *mut leanh::LeanObject,
    mut v_00_u03b1_46_: *mut leanh::LeanObject,
    mut v_00_u03b2_47_: *mut leanh::LeanObject,
    mut v_x_48_: *mut leanh::LeanObject,
    mut v_inst_49_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_50_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_50_ = leanh::lean_apply_1(v_inst_49_, v_x_48_);
    return v___x_50_;
}
pub unsafe fn l_Std_ToIterator_iter___redArg(
    mut v_inst_51_: *mut leanh::LeanObject,
    mut v_x_52_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_53_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_53_ = leanh::lean_apply_1(v_inst_51_, v_x_52_);
    return v___x_53_;
}
pub unsafe fn l_Std_ToIterator_iter(
    mut v_00_u03b3_54_: *mut leanh::LeanObject,
    mut v_00_u03b1_55_: *mut leanh::LeanObject,
    mut v_00_u03b2_56_: *mut leanh::LeanObject,
    mut v_inst_57_: *mut leanh::LeanObject,
    mut v_x_58_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_59_ = leanh::lean_apply_1(v_inst_57_, v_x_58_);
    return v___x_59_;
}
pub unsafe fn l_Std_ToIterator_ofM___redArg___lam__0(
    mut v_iterM_60_: *mut leanh::LeanObject,
    mut v_x_61_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_62_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_62_ = leanh::lean_apply_1(v_iterM_60_, v_x_61_);
    return v___x_62_;
}
pub unsafe fn l_Std_ToIterator_ofM___redArg(
    mut v_iterM_63_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_64_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_64_ = leanh::lean_alloc_closure(
        l_Std_ToIterator_ofM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_64_, 0, v_iterM_63_);
    return v___f_64_;
}
pub unsafe fn l_Std_ToIterator_ofM(
    mut v_00_u03b3_65_: *mut leanh::LeanObject,
    mut v_m_66_: *mut leanh::LeanObject,
    mut v_00_u03b2_67_: *mut leanh::LeanObject,
    mut v_00_u03b1_68_: *mut leanh::LeanObject,
    mut v_iterM_69_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_70_ = leanh::lean_alloc_closure(
        l_Std_ToIterator_ofM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_70_, 0, v_iterM_69_);
    return v___f_70_;
}
pub unsafe fn l_Std_ToIterator_of___redArg___lam__0(
    mut v_iter_71_: *mut leanh::LeanObject,
    mut v_x_72_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_73_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_73_ = leanh::lean_apply_1(v_iter_71_, v_x_72_);
    return v___x_73_;
}
pub unsafe fn l_Std_ToIterator_of___redArg(
    mut v_iter_74_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_75_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_75_ = leanh::lean_alloc_closure(
        l_Std_ToIterator_of___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_75_, 0, v_iter_74_);
    return v___f_75_;
}
pub unsafe fn l_Std_ToIterator_of(
    mut v_00_u03b3_76_: *mut leanh::LeanObject,
    mut v_00_u03b2_77_: *mut leanh::LeanObject,
    mut v_00_u03b1_78_: *mut leanh::LeanObject,
    mut v_iter_79_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_80_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_80_ = leanh::lean_alloc_closure(
        l_Std_ToIterator_of___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_80_, 0, v_iter_79_);
    return v___f_80_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_ToIterator(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_ToIterator(
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
pub unsafe fn initialize_Init_Data_Iterators_ToIterator(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_ToIterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_ToIterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_ToIterator(builtin);
}