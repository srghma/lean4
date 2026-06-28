// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Consumers.Access
// Imports: Init.Data.Iterators.Consumers.Access
use crate::r#gen::Init::Data::Iterators::Consumers::Access::{
    initialize_Init_Data_Iterators_Consumers_Access,
    runtime_initialize_Init_Data_Iterators_Consumers_Access,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter___redArg(
    mut v_x_56_: *mut LeanObject,
    mut v_h__1_57_: *mut LeanObject,
    mut v_h__2_58_: *mut LeanObject,
    mut v_h__3_59_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_56_) {
        0 => {
            let mut v_it_60_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_61_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_59_);
            lean_dec(v_h__2_58_);
            v_it_60_ = lean_ctor_get(v_x_56_, 0);
            lean_inc(v_it_60_);
            v_out_61_ = lean_ctor_get(v_x_56_, 1);
            lean_inc(v_out_61_);
            lean_dec_ref_known(v_x_56_, 2);
            v___x_62_ = lean_apply_2(v_h__1_57_, v_it_60_, v_out_61_);
            return v___x_62_;
        }
        1 => {
            let mut v_it_63_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_64_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_59_);
            lean_dec(v_h__1_57_);
            v_it_63_ = lean_ctor_get(v_x_56_, 0);
            lean_inc(v_it_63_);
            lean_dec_ref_known(v_x_56_, 1);
            v___x_64_ = lean_apply_1(v_h__2_58_, v_it_63_);
            return v___x_64_;
        }
        _ => {
            let mut v___x_65_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_66_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_58_);
            lean_dec(v_h__1_57_);
            v___x_65_ = lean_box(0);
            v___x_66_ = lean_apply_1(v_h__3_59_, v___x_65_);
            return v___x_66_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter(
    mut v_00_u03b1_67_: *mut LeanObject,
    mut v_00_u03b2_68_: *mut LeanObject,
    mut v_motive_69_: *mut LeanObject,
    mut v_x_70_: *mut LeanObject,
    mut v_h__1_71_: *mut LeanObject,
    mut v_h__2_72_: *mut LeanObject,
    mut v_h__3_73_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_70_) {
        0 => {
            let mut v_it_74_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_75_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_76_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_73_);
            lean_dec(v_h__2_72_);
            v_it_74_ = lean_ctor_get(v_x_70_, 0);
            lean_inc(v_it_74_);
            v_out_75_ = lean_ctor_get(v_x_70_, 1);
            lean_inc(v_out_75_);
            lean_dec_ref_known(v_x_70_, 2);
            v___x_76_ = lean_apply_2(v_h__1_71_, v_it_74_, v_out_75_);
            return v___x_76_;
        }
        1 => {
            let mut v_it_77_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_78_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_73_);
            lean_dec(v_h__1_71_);
            v_it_77_ = lean_ctor_get(v_x_70_, 0);
            lean_inc(v_it_77_);
            lean_dec_ref_known(v_x_70_, 1);
            v___x_78_ = lean_apply_1(v_h__2_72_, v_it_77_);
            return v___x_78_;
        }
        _ => {
            let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_80_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_72_);
            lean_dec(v_h__1_71_);
            v___x_79_ = lean_box(0);
            v___x_80_ = lean_apply_1(v_h__3_73_, v___x_79_);
            return v___x_80_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(
    mut v_n_81_: *mut LeanObject,
    mut v_h__1_82_: *mut LeanObject,
    mut v_h__2_83_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_84_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_85_: u8 = 0;
    v_zero_84_ = lean_unsigned_to_nat(0);
    v_isZero_85_ = lean_nat_dec_eq(v_n_81_, v_zero_84_);
    if v_isZero_85_ == 1 {
        let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_87_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_83_);
        v___x_86_ = lean_box(0);
        v___x_87_ = lean_apply_1(v_h__1_82_, v___x_86_);
        return v___x_87_;
    } else {
        let mut v_one_88_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_89_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_82_);
        v_one_88_ = lean_unsigned_to_nat(1);
        v_n_89_ = lean_nat_sub(v_n_81_, v_one_88_);
        v___x_90_ = lean_apply_1(v_h__2_83_, v_n_89_);
        return v___x_90_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(
    mut v_n_91_: *mut LeanObject,
    mut v_h__1_92_: *mut LeanObject,
    mut v_h__2_93_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_94_: *mut LeanObject = core::ptr::null_mut();
    v_res_94_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_91_, v_h__1_92_, v_h__2_93_);
    lean_dec(v_n_91_);
    return v_res_94_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(
    mut v_motive_95_: *mut LeanObject,
    mut v_n_96_: *mut LeanObject,
    mut v_h__1_97_: *mut LeanObject,
    mut v_h__2_98_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_100_: u8 = 0;
    v_zero_99_ = lean_unsigned_to_nat(0);
    v_isZero_100_ = lean_nat_dec_eq(v_n_96_, v_zero_99_);
    if v_isZero_100_ == 1 {
        let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_98_);
        v___x_101_ = lean_box(0);
        v___x_102_ = lean_apply_1(v_h__1_97_, v___x_101_);
        return v___x_102_;
    } else {
        let mut v_one_103_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_104_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_97_);
        v_one_103_ = lean_unsigned_to_nat(1);
        v_n_104_ = lean_nat_sub(v_n_96_, v_one_103_);
        v___x_105_ = lean_apply_1(v_h__2_98_, v_n_104_);
        return v___x_105_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(
    mut v_motive_106_: *mut LeanObject,
    mut v_n_107_: *mut LeanObject,
    mut v_h__1_108_: *mut LeanObject,
    mut v_h__2_109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_110_: *mut LeanObject = core::ptr::null_mut();
    v_res_110_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(v_motive_106_, v_n_107_, v_h__1_108_, v_h__2_109_);
    lean_dec(v_n_107_);
    return v_res_110_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Consumers_Access(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
}
