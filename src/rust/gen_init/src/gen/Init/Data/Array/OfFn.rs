// Lean compiler output
// Module: Init.Data.Array.OfFn
// Imports: Init.Data.Array.Basic Init.Data.List.OfFn Init.Data.Array.Bootstrap Init.Data.Array.Monadic Init.Data.Fin.Lemmas Init.Data.List.FinRange Init.Data.Option.Lemmas Init.Omega
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::Monadic::{
    initialize_Init_Data_Array_Monadic, runtime_initialize_Init_Data_Array_Monadic,
};
use crate::r#gen::Init::Data::Fin::Fold::l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop;
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::List::FinRange::{
    initialize_Init_Data_List_FinRange, runtime_initialize_Init_Data_List_FinRange,
};
use crate::r#gen::Init::Data::List::OfFn::{
    initialize_Init_Data_List_OfFn, runtime_initialize_Init_Data_List_OfFn,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_Array_push___boxed;
use crate::ffi::{
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_sub,
};
pub unsafe fn l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter___redArg(
    mut v_x_56_: *mut crate::leanh::LeanObject,
    mut v_h__1_57_: *mut crate::leanh::LeanObject,
    mut v_h__2_58_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_60_: u8 = 0;
    v_zero_59_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_60_ = lean_nat_dec_eq(v_x_56_, v_zero_59_);
    if v_isZero_60_ == 1 {
        let mut v___x_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_57_);
        v___x_61_ = crate::leanh::lean_apply_1(v_h__2_58_, crate::leanh::lean_box(0));
        return v___x_61_;
    } else {
        let mut v_one_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_58_);
        v_one_62_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_63_ = lean_nat_sub(v_x_56_, v_one_62_);
        v___x_64_ = crate::leanh::lean_apply_2(v_h__1_57_, v_n_63_, crate::leanh::lean_box(0));
        return v___x_64_;
    }
}
pub unsafe fn l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter___redArg___boxed(
    mut v_x_65_: *mut crate::leanh::LeanObject,
    mut v_h__1_66_: *mut crate::leanh::LeanObject,
    mut v_h__2_67_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_68_ = l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter___redArg(
        v_x_65_, v_h__1_66_, v_h__2_67_,
    );
    crate::leanh::lean_dec(v_x_65_);
    return v_res_68_;
}
pub unsafe fn l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter(
    mut v_n_69_: *mut crate::leanh::LeanObject,
    mut v_motive_70_: *mut crate::leanh::LeanObject,
    mut v_x_71_: *mut crate::leanh::LeanObject,
    mut v_x_72_: *mut crate::leanh::LeanObject,
    mut v_h__1_73_: *mut crate::leanh::LeanObject,
    mut v_h__2_74_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_76_: u8 = 0;
    v_zero_75_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_76_ = lean_nat_dec_eq(v_x_71_, v_zero_75_);
    if v_isZero_76_ == 1 {
        let mut v___x_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_73_);
        v___x_77_ = crate::leanh::lean_apply_1(v_h__2_74_, crate::leanh::lean_box(0));
        return v___x_77_;
    } else {
        let mut v_one_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_74_);
        v_one_78_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_79_ = lean_nat_sub(v_x_71_, v_one_78_);
        v___x_80_ = crate::leanh::lean_apply_2(v_h__1_73_, v_n_79_, crate::leanh::lean_box(0));
        return v___x_80_;
    }
}
pub unsafe fn l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter___boxed(
    mut v_n_81_: *mut crate::leanh::LeanObject,
    mut v_motive_82_: *mut crate::leanh::LeanObject,
    mut v_x_83_: *mut crate::leanh::LeanObject,
    mut v_x_84_: *mut crate::leanh::LeanObject,
    mut v_h__1_85_: *mut crate::leanh::LeanObject,
    mut v_h__2_86_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_87_ = l___private_Init_Data_Array_OfFn_0__Array_ofFn_go_match__1_splitter(
        v_n_81_,
        v_motive_82_,
        v_x_83_,
        v_x_84_,
        v_h__1_85_,
        v_h__2_86_,
    );
    crate::leanh::lean_dec(v_x_83_);
    crate::leanh::lean_dec(v_n_81_);
    return v_res_87_;
}
pub unsafe fn l_Array_ofFnM___redArg___lam__0(
    mut v_toFunctor_88_: *mut crate::leanh::LeanObject,
    mut v_f_89_: *mut crate::leanh::LeanObject,
    mut v_xs_90_: *mut crate::leanh::LeanObject,
    mut v_i_91_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_92_ = crate::leanh::lean_ctor_get(v_toFunctor_88_, 0);
    crate::leanh::lean_inc(v_map_92_);
    crate::leanh::lean_dec_ref(v_toFunctor_88_);
    v___x_93_ =
        crate::leanh::lean_alloc_closure(l_Array_push___boxed as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_93_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_93_, 1, v_xs_90_);
    v___x_94_ = crate::leanh::lean_apply_1(v_f_89_, v_i_91_);
    v___x_95_ = crate::leanh::lean_apply_4(
        v_map_92_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_93_,
        v___x_94_,
    );
    return v___x_95_;
}
pub unsafe fn l_Array_ofFnM___redArg(
    mut v_n_96_: *mut crate::leanh::LeanObject,
    mut v_inst_97_: *mut crate::leanh::LeanObject,
    mut v_f_98_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_99_ = crate::leanh::lean_ctor_get(v_inst_97_, 0);
    v_toFunctor_100_ = crate::leanh::lean_ctor_get(v_toApplicative_99_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_100_);
    v___f_101_ = crate::leanh::lean_alloc_closure(
        l_Array_ofFnM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_101_, 0, v_toFunctor_100_);
    crate::leanh::lean_closure_set(v___f_101_, 1, v_f_98_);
    v___x_102_ = lean_mk_empty_array_with_capacity(v_n_96_);
    v___x_103_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_104_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_97_,
        v_n_96_,
        v___f_101_,
        v___x_102_,
        v___x_103_,
    );
    return v___x_104_;
}
pub unsafe fn l_Array_ofFnM(
    mut v_m_105_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_106_: *mut crate::leanh::LeanObject,
    mut v_n_107_: *mut crate::leanh::LeanObject,
    mut v_inst_108_: *mut crate::leanh::LeanObject,
    mut v_f_109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_110_ = l_Array_ofFnM___redArg(v_n_107_, v_inst_108_, v_f_109_);
    return v___x_110_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_OfFn(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_OfFn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_FinRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_OfFn(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_OfFn(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_OfFn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_FinRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_OfFn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_OfFn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_OfFn(builtin);
}
