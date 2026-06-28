// Lean compiler output
// Module: Init.Data.Iterators.ToIterator
// Imports: Init.Data.Iterators.Basic
use crate::r#gen::Init::Data::Iterators::Basic::{
    initialize_Init_Data_Iterators_Basic, runtime_initialize_Init_Data_Iterators_Basic,
};
pub unsafe fn l_Std_ToIterator_iterM___redArg(
    mut v_x_41_: *mut crate::leanh::LeanObject,
    mut v_inst_42_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_43_ = crate::leanh::lean_apply_1(v_inst_42_, v_x_41_);
    return v___x_43_;
}
pub unsafe fn l_Std_ToIterator_iterM(
    mut v_00_u03b3_44_: *mut crate::leanh::LeanObject,
    mut v_m_45_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_46_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_47_: *mut crate::leanh::LeanObject,
    mut v_x_48_: *mut crate::leanh::LeanObject,
    mut v_inst_49_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_50_ = crate::leanh::lean_apply_1(v_inst_49_, v_x_48_);
    return v___x_50_;
}
pub unsafe fn l_Std_ToIterator_iter___redArg(
    mut v_inst_51_: *mut crate::leanh::LeanObject,
    mut v_x_52_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_53_ = crate::leanh::lean_apply_1(v_inst_51_, v_x_52_);
    return v___x_53_;
}
pub unsafe fn l_Std_ToIterator_iter(
    mut v_00_u03b3_54_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_55_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_56_: *mut crate::leanh::LeanObject,
    mut v_inst_57_: *mut crate::leanh::LeanObject,
    mut v_x_58_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_59_ = crate::leanh::lean_apply_1(v_inst_57_, v_x_58_);
    return v___x_59_;
}
pub unsafe fn l_Std_ToIterator_ofM___redArg___lam__0(
    mut v_iterM_60_: *mut crate::leanh::LeanObject,
    mut v_x_61_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_62_ = crate::leanh::lean_apply_1(v_iterM_60_, v_x_61_);
    return v___x_62_;
}
pub unsafe fn l_Std_ToIterator_ofM___redArg(
    mut v_iterM_63_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_64_ = crate::leanh::lean_alloc_closure(
        l_Std_ToIterator_ofM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_64_, 0, v_iterM_63_);
    return v___f_64_;
}
pub unsafe fn l_Std_ToIterator_ofM(
    mut v_00_u03b3_65_: *mut crate::leanh::LeanObject,
    mut v_m_66_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_67_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_68_: *mut crate::leanh::LeanObject,
    mut v_iterM_69_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_70_ = crate::leanh::lean_alloc_closure(
        l_Std_ToIterator_ofM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_70_, 0, v_iterM_69_);
    return v___f_70_;
}
pub unsafe fn l_Std_ToIterator_of___redArg___lam__0(
    mut v_iter_71_: *mut crate::leanh::LeanObject,
    mut v_x_72_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_73_ = crate::leanh::lean_apply_1(v_iter_71_, v_x_72_);
    return v___x_73_;
}
pub unsafe fn l_Std_ToIterator_of___redArg(
    mut v_iter_74_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_75_ = crate::leanh::lean_alloc_closure(
        l_Std_ToIterator_of___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_75_, 0, v_iter_74_);
    return v___f_75_;
}
pub unsafe fn l_Std_ToIterator_of(
    mut v_00_u03b3_76_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_77_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_78_: *mut crate::leanh::LeanObject,
    mut v_iter_79_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_80_ = crate::leanh::lean_alloc_closure(
        l_Std_ToIterator_of___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_80_, 0, v_iter_79_);
    return v___f_80_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_ToIterator(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_ToIterator(
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
pub unsafe fn initialize_Init_Data_Iterators_ToIterator(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_ToIterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_ToIterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_ToIterator(builtin);
}
