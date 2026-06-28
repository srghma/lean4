// Lean compiler output
// Module: Init.Data.Array.Bootstrap
// Imports: Init.Data.Array.Basic Init.Data.List.Control Init.Data.List.Lemmas Init.Data.List.TakeDrop
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
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_dec, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___redArg(
    mut v_i_65_: *mut LeanObject,
    mut v_h__1_66_: *mut LeanObject,
    mut v_h__2_67_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_68_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_69_: u8 = 0;
    v_zero_68_ = lean_unsigned_to_nat(0);
    v_isZero_69_ = lean_nat_dec_eq(v_i_65_, v_zero_68_);
    if v_isZero_69_ == 1 {
        let mut v___x_70_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_71_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_67_);
        v___x_70_ = lean_box(0);
        v___x_71_ = lean_apply_1(v_h__1_66_, v___x_70_);
        return v___x_71_;
    } else {
        let mut v_one_72_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_73_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_74_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_66_);
        v_one_72_ = lean_unsigned_to_nat(1);
        v_n_73_ = lean_nat_sub(v_i_65_, v_one_72_);
        v___x_74_ = lean_apply_1(v_h__2_67_, v_n_73_);
        return v___x_74_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(
    mut v_i_75_: *mut LeanObject,
    mut v_h__1_76_: *mut LeanObject,
    mut v_h__2_77_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_78_: *mut LeanObject = core::ptr::null_mut();
    v_res_78_ =
        l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___redArg(
            v_i_75_, v_h__1_76_, v_h__2_77_,
        );
    lean_dec(v_i_75_);
    return v_res_78_;
}
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter(
    mut v_motive_79_: *mut LeanObject,
    mut v_i_80_: *mut LeanObject,
    mut v_h__1_81_: *mut LeanObject,
    mut v_h__2_82_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_83_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_84_: u8 = 0;
    v_zero_83_ = lean_unsigned_to_nat(0);
    v_isZero_84_ = lean_nat_dec_eq(v_i_80_, v_zero_83_);
    if v_isZero_84_ == 1 {
        let mut v___x_85_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_82_);
        v___x_85_ = lean_box(0);
        v___x_86_ = lean_apply_1(v_h__1_81_, v___x_85_);
        return v___x_86_;
    } else {
        let mut v_one_87_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_88_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_81_);
        v_one_87_ = lean_unsigned_to_nat(1);
        v_n_88_ = lean_nat_sub(v_i_80_, v_one_87_);
        v___x_89_ = lean_apply_1(v_h__2_82_, v_n_88_);
        return v___x_89_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter___boxed(
    mut v_motive_90_: *mut LeanObject,
    mut v_i_91_: *mut LeanObject,
    mut v_h__1_92_: *mut LeanObject,
    mut v_h__2_93_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_94_: *mut LeanObject = core::ptr::null_mut();
    v_res_94_ = l___private_Init_Data_Array_Bootstrap_0__Array_foldlM_loop_match__1_splitter(
        v_motive_90_,
        v_i_91_,
        v_h__1_92_,
        v_h__2_93_,
    );
    lean_dec(v_i_91_);
    return v_res_94_;
}
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg(
    mut v_i_95_: *mut LeanObject,
    mut v_h__1_96_: *mut LeanObject,
    mut v_h__2_97_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_99_: u8 = 0;
    v_zero_98_ = lean_unsigned_to_nat(0);
    v_isZero_99_ = lean_nat_dec_eq(v_i_95_, v_zero_98_);
    if v_isZero_99_ == 1 {
        let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_97_);
        v___x_100_ = lean_apply_1(v_h__1_96_, lean_box(0));
        return v___x_100_;
    } else {
        let mut v_one_101_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_102_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_96_);
        v_one_101_ = lean_unsigned_to_nat(1);
        v_n_102_ = lean_nat_sub(v_i_95_, v_one_101_);
        v___x_103_ = lean_apply_2(v_h__2_97_, v_n_102_, lean_box(0));
        return v___x_103_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(
    mut v_i_104_: *mut LeanObject,
    mut v_h__1_105_: *mut LeanObject,
    mut v_h__2_106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_107_: *mut LeanObject = core::ptr::null_mut();
    v_res_107_ =
        l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___redArg(
            v_i_104_,
            v_h__1_105_,
            v_h__2_106_,
        );
    lean_dec(v_i_104_);
    return v_res_107_;
}
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter(
    mut v_00_u03b1_108_: *mut LeanObject,
    mut v_as_109_: *mut LeanObject,
    mut v_motive_110_: *mut LeanObject,
    mut v_i_111_: *mut LeanObject,
    mut v_h_112_: *mut LeanObject,
    mut v_h__1_113_: *mut LeanObject,
    mut v_h__2_114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_116_: u8 = 0;
    v_zero_115_ = lean_unsigned_to_nat(0);
    v_isZero_116_ = lean_nat_dec_eq(v_i_111_, v_zero_115_);
    if v_isZero_116_ == 1 {
        let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_114_);
        v___x_117_ = lean_apply_1(v_h__1_113_, lean_box(0));
        return v___x_117_;
    } else {
        let mut v_one_118_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_119_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_113_);
        v_one_118_ = lean_unsigned_to_nat(1);
        v_n_119_ = lean_nat_sub(v_i_111_, v_one_118_);
        v___x_120_ = lean_apply_2(v_h__2_114_, v_n_119_, lean_box(0));
        return v___x_120_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter___boxed(
    mut v_00_u03b1_121_: *mut LeanObject,
    mut v_as_122_: *mut LeanObject,
    mut v_motive_123_: *mut LeanObject,
    mut v_i_124_: *mut LeanObject,
    mut v_h_125_: *mut LeanObject,
    mut v_h__1_126_: *mut LeanObject,
    mut v_h__2_127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_128_: *mut LeanObject = core::ptr::null_mut();
    v_res_128_ = l___private_Init_Data_Array_Bootstrap_0__Array_forIn_x27_loop_match__3_splitter(
        v_00_u03b1_121_,
        v_as_122_,
        v_motive_123_,
        v_i_124_,
        v_h_125_,
        v_h__1_126_,
        v_h__2_127_,
    );
    lean_dec(v_i_124_);
    lean_dec_ref(v_as_122_);
    return v_res_128_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Bootstrap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Bootstrap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Bootstrap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_Bootstrap(builtin);
}
