// Lean compiler output
// Module: Init.Data.Ord.Vector
// Imports: Init.Data.Order.Ord Init.Data.Vector.Basic Init.Data.Vector.Lemmas
use crate::r#gen::Init::Data::Ord::Array::l___private_Init_Data_Ord_Array_0__Array_compareLex_go;
use crate::r#gen::Init::Data::Order::Ord::{
    initialize_Init_Data_Order_Ord, runtime_initialize_Init_Data_Order_Ord,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Data::Vector::Lemmas::{
    initialize_Init_Data_Vector_Lemmas, runtime_initialize_Init_Data_Vector_Lemmas,
};
pub unsafe fn l_Array_compareLex___at___00Vector_compareLex_spec__0___redArg(
    mut v_cmp_51_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_52_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_53_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_55_: u8 = 0;
    v___x_54_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_55_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(
        crate::leanh::lean_box(0),
        v_cmp_51_,
        v_a_u2081_52_,
        v_a_u2082_53_,
        v___x_54_,
    );
    return v___x_55_;
}
pub unsafe fn l_Array_compareLex___at___00Vector_compareLex_spec__0___redArg___boxed(
    mut v_cmp_56_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_57_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_58_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_59_: u8 = 0;
    let mut v_r_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_59_ = l_Array_compareLex___at___00Vector_compareLex_spec__0___redArg(
        v_cmp_56_,
        v_a_u2081_57_,
        v_a_u2082_58_,
    );
    crate::leanh::lean_dec_ref(v_a_u2082_58_);
    crate::leanh::lean_dec_ref(v_a_u2081_57_);
    v_r_60_ = crate::leanh::lean_box((v_res_59_) as usize);
    return v_r_60_;
}
pub unsafe fn l_Array_compareLex___at___00Vector_compareLex_spec__0(
    mut v_00_u03b1_61_: *mut crate::leanh::LeanObject,
    mut v_cmp_62_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_63_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_64_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_65_: u8 = 0;
    v___x_65_ = l_Array_compareLex___at___00Vector_compareLex_spec__0___redArg(
        v_cmp_62_,
        v_a_u2081_63_,
        v_a_u2082_64_,
    );
    return v___x_65_;
}
pub unsafe fn l_Array_compareLex___at___00Vector_compareLex_spec__0___boxed(
    mut v_00_u03b1_66_: *mut crate::leanh::LeanObject,
    mut v_cmp_67_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_68_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_69_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_70_: u8 = 0;
    let mut v_r_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_70_ = l_Array_compareLex___at___00Vector_compareLex_spec__0(
        v_00_u03b1_66_,
        v_cmp_67_,
        v_a_u2081_68_,
        v_a_u2082_69_,
    );
    crate::leanh::lean_dec_ref(v_a_u2082_69_);
    crate::leanh::lean_dec_ref(v_a_u2081_68_);
    v_r_71_ = crate::leanh::lean_box((v_res_70_) as usize);
    return v_r_71_;
}
pub unsafe fn l_Vector_compareLex___redArg(
    mut v_cmp_72_: *mut crate::leanh::LeanObject,
    mut v_a_73_: *mut crate::leanh::LeanObject,
    mut v_b_74_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_75_: u8 = 0;
    v___x_75_ =
        l_Array_compareLex___at___00Vector_compareLex_spec__0___redArg(v_cmp_72_, v_a_73_, v_b_74_);
    return v___x_75_;
}
pub unsafe fn l_Vector_compareLex___redArg___boxed(
    mut v_cmp_76_: *mut crate::leanh::LeanObject,
    mut v_a_77_: *mut crate::leanh::LeanObject,
    mut v_b_78_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_79_: u8 = 0;
    let mut v_r_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_79_ = l_Vector_compareLex___redArg(v_cmp_76_, v_a_77_, v_b_78_);
    crate::leanh::lean_dec_ref(v_b_78_);
    crate::leanh::lean_dec_ref(v_a_77_);
    v_r_80_ = crate::leanh::lean_box((v_res_79_) as usize);
    return v_r_80_;
}
pub unsafe fn l_Vector_compareLex(
    mut v_00_u03b1_81_: *mut crate::leanh::LeanObject,
    mut v_n_82_: *mut crate::leanh::LeanObject,
    mut v_cmp_83_: *mut crate::leanh::LeanObject,
    mut v_a_84_: *mut crate::leanh::LeanObject,
    mut v_b_85_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_86_: u8 = 0;
    v___x_86_ =
        l_Array_compareLex___at___00Vector_compareLex_spec__0___redArg(v_cmp_83_, v_a_84_, v_b_85_);
    return v___x_86_;
}
pub unsafe fn l_Vector_compareLex___boxed(
    mut v_00_u03b1_87_: *mut crate::leanh::LeanObject,
    mut v_n_88_: *mut crate::leanh::LeanObject,
    mut v_cmp_89_: *mut crate::leanh::LeanObject,
    mut v_a_90_: *mut crate::leanh::LeanObject,
    mut v_b_91_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_92_: u8 = 0;
    let mut v_r_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_92_ = l_Vector_compareLex(v_00_u03b1_87_, v_n_88_, v_cmp_89_, v_a_90_, v_b_91_);
    crate::leanh::lean_dec_ref(v_b_91_);
    crate::leanh::lean_dec_ref(v_a_90_);
    crate::leanh::lean_dec(v_n_88_);
    v_r_93_ = crate::leanh::lean_box((v_res_92_) as usize);
    return v_r_93_;
}
pub unsafe fn l_Vector_instOrd___redArg(
    mut v_n_94_: *mut crate::leanh::LeanObject,
    mut v_inst_95_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_96_ = crate::leanh::lean_alloc_closure(
        l_Vector_compareLex___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___x_96_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_96_, 1, v_n_94_);
    crate::leanh::lean_closure_set(v___x_96_, 2, v_inst_95_);
    return v___x_96_;
}
pub unsafe fn l_Vector_instOrd(
    mut v_00_u03b1_97_: *mut crate::leanh::LeanObject,
    mut v_n_98_: *mut crate::leanh::LeanObject,
    mut v_inst_99_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_100_ = crate::leanh::lean_alloc_closure(
        l_Vector_compareLex___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___x_100_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_100_, 1, v_n_98_);
    crate::leanh::lean_closure_set(v___x_100_, 2, v_inst_99_);
    return v___x_100_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Ord_Vector(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_Ord(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Ord_Vector(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Ord_Vector(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_Ord(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_Vector(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Ord_Vector(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Ord_Vector(builtin);
}
