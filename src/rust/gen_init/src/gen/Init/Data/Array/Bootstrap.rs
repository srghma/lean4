// Lean compiler output
// Module: Init.Data.Array.Bootstrap
// Imports: Init.Data.Array.Basic Init.Data.List.Control Init.Data.List.Lemmas Init.Data.List.TakeDrop
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::List::Control::{
    initialize_Init_Data_List_Control, runtime_initialize_Init_Data_List_Control,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___redArg(
    mut v_i_65_: *mut leanh::LeanObject,
    mut v_h__1_66_: *mut leanh::LeanObject,
    mut v_h__2_67_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_68_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_69_: u8 = 0;
    v_zero_68_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_69_ = lean_nat_dec_eq(v_i_65_, v_zero_68_);
    if v_isZero_69_ == 1 {
        let mut v___x_70_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_71_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_67_);
        v___x_70_ = leanh::lean_box(0);
        v___x_71_ = leanh::lean_apply_1(v_h__1_66_, v___x_70_);
        return v___x_71_;
    } else {
        let mut v_one_72_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_73_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_74_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_66_);
        v_one_72_ = leanh::lean_unsigned_to_nat(1);
        v_n_73_ = lean_nat_sub(v_i_65_, v_one_72_);
        v___x_74_ = leanh::lean_apply_1(v_h__2_67_, v_n_73_);
        return v___x_74_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(
    mut v_i_75_: *mut leanh::LeanObject,
    mut v_h__1_76_: *mut leanh::LeanObject,
    mut v_h__2_77_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_78_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_78_ =
        l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___redArg(
            v_i_75_, v_h__1_76_, v_h__2_77_,
        );
    leanh::lean_dec(v_i_75_);
    return v_res_78_;
}
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter(
    mut v_motive_79_: *mut leanh::LeanObject,
    mut v_i_80_: *mut leanh::LeanObject,
    mut v_h__1_81_: *mut leanh::LeanObject,
    mut v_h__2_82_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_83_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_84_: u8 = 0;
    v_zero_83_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_84_ = lean_nat_dec_eq(v_i_80_, v_zero_83_);
    if v_isZero_84_ == 1 {
        let mut v___x_85_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_86_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_82_);
        v___x_85_ = leanh::lean_box(0);
        v___x_86_ = leanh::lean_apply_1(v_h__1_81_, v___x_85_);
        return v___x_86_;
    } else {
        let mut v_one_87_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_88_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_89_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_81_);
        v_one_87_ = leanh::lean_unsigned_to_nat(1);
        v_n_88_ = lean_nat_sub(v_i_80_, v_one_87_);
        v___x_89_ = leanh::lean_apply_1(v_h__2_82_, v_n_88_);
        return v___x_89_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___boxed(
    mut v_motive_90_: *mut leanh::LeanObject,
    mut v_i_91_: *mut leanh::LeanObject,
    mut v_h__1_92_: *mut leanh::LeanObject,
    mut v_h__2_93_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_94_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_94_ = l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter(
        v_motive_90_,
        v_i_91_,
        v_h__1_92_,
        v_h__2_93_,
    );
    leanh::lean_dec(v_i_91_);
    return v_res_94_;
}
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg(
    mut v_i_95_: *mut leanh::LeanObject,
    mut v_h__1_96_: *mut leanh::LeanObject,
    mut v_h__2_97_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_99_: u8 = 0;
    v_zero_98_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_99_ = lean_nat_dec_eq(v_i_95_, v_zero_98_);
    if v_isZero_99_ == 1 {
        let mut v___x_100_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_97_);
        v___x_100_ = leanh::lean_apply_1(v_h__1_96_, leanh::lean_box(0));
        return v___x_100_;
    } else {
        let mut v_one_101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_102_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_96_);
        v_one_101_ = leanh::lean_unsigned_to_nat(1);
        v_n_102_ = lean_nat_sub(v_i_95_, v_one_101_);
        v___x_103_ = leanh::lean_apply_2(v_h__2_97_, v_n_102_, leanh::lean_box(0));
        return v___x_103_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(
    mut v_i_104_: *mut leanh::LeanObject,
    mut v_h__1_105_: *mut leanh::LeanObject,
    mut v_h__2_106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_107_ =
        l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg(
            v_i_104_,
            v_h__1_105_,
            v_h__2_106_,
        );
    leanh::lean_dec(v_i_104_);
    return v_res_107_;
}
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter(
    mut v_00_u03b1_108_: *mut leanh::LeanObject,
    mut v_as_109_: *mut leanh::LeanObject,
    mut v_motive_110_: *mut leanh::LeanObject,
    mut v_i_111_: *mut leanh::LeanObject,
    mut v_h_112_: *mut leanh::LeanObject,
    mut v_h__1_113_: *mut leanh::LeanObject,
    mut v_h__2_114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_116_: u8 = 0;
    v_zero_115_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_116_ = lean_nat_dec_eq(v_i_111_, v_zero_115_);
    if v_isZero_116_ == 1 {
        let mut v___x_117_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_114_);
        v___x_117_ = leanh::lean_apply_1(v_h__1_113_, leanh::lean_box(0));
        return v___x_117_;
    } else {
        let mut v_one_118_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_119_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_120_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_113_);
        v_one_118_ = leanh::lean_unsigned_to_nat(1);
        v_n_119_ = lean_nat_sub(v_i_111_, v_one_118_);
        v___x_120_ = leanh::lean_apply_2(v_h__2_114_, v_n_119_, leanh::lean_box(0));
        return v___x_120_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___boxed(
    mut v_00_u03b1_121_: *mut leanh::LeanObject,
    mut v_as_122_: *mut leanh::LeanObject,
    mut v_motive_123_: *mut leanh::LeanObject,
    mut v_i_124_: *mut leanh::LeanObject,
    mut v_h_125_: *mut leanh::LeanObject,
    mut v_h__1_126_: *mut leanh::LeanObject,
    mut v_h__2_127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_128_ = l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter(
        v_00_u03b1_121_,
        v_as_122_,
        v_motive_123_,
        v_i_124_,
        v_h_125_,
        v_h__1_126_,
        v_h__2_127_,
    );
    leanh::lean_dec(v_i_124_);
    leanh::lean_dec_ref(v_as_122_);
    return v_res_128_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Bootstrap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Bootstrap(
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
pub unsafe fn initialize_Init_Data_Array_Bootstrap(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Bootstrap(builtin);
}