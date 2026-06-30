// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Consumers.Access
// Imports: Init.Data.Iterators.Consumers.Access
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
use crate::r#gen::Init::Data::Iterators::Consumers::Access::{
    initialize_Init_Data_Iterators_Consumers_Access,
    runtime_initialize_Init_Data_Iterators_Consumers_Access,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter___redArg(
    mut v_x_56_: *mut leanh::LeanObject,
    mut v_h__1_57_: *mut leanh::LeanObject,
    mut v_h__2_58_: *mut leanh::LeanObject,
    mut v_h__3_59_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_56_) {
        0 => {
            let mut v_it_60_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_61_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_62_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_59_);
            leanh::lean_dec(v_h__2_58_);
            v_it_60_ = leanh::lean_ctor_get(v_x_56_, 0);
            leanh::lean_inc(v_it_60_);
            v_out_61_ = leanh::lean_ctor_get(v_x_56_, 1);
            leanh::lean_inc(v_out_61_);
            leanh::lean_dec_ref_known(v_x_56_, 2);
            v___x_62_ = leanh::lean_apply_2(v_h__1_57_, v_it_60_, v_out_61_);
            return v___x_62_;
        }
        1 => {
            let mut v_it_63_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_64_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_59_);
            leanh::lean_dec(v_h__1_57_);
            v_it_63_ = leanh::lean_ctor_get(v_x_56_, 0);
            leanh::lean_inc(v_it_63_);
            leanh::lean_dec_ref_known(v_x_56_, 1);
            v___x_64_ = leanh::lean_apply_1(v_h__2_58_, v_it_63_);
            return v___x_64_;
        }
        _ => {
            let mut v___x_65_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_66_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_58_);
            leanh::lean_dec(v_h__1_57_);
            v___x_65_ = leanh::lean_box(0);
            v___x_66_ = leanh::lean_apply_1(v_h__3_59_, v___x_65_);
            return v___x_66_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter(
    mut v_00_u03b1_67_: *mut leanh::LeanObject,
    mut v_00_u03b2_68_: *mut leanh::LeanObject,
    mut v_motive_69_: *mut leanh::LeanObject,
    mut v_x_70_: *mut leanh::LeanObject,
    mut v_h__1_71_: *mut leanh::LeanObject,
    mut v_h__2_72_: *mut leanh::LeanObject,
    mut v_h__3_73_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_70_) {
        0 => {
            let mut v_it_74_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_75_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_76_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_73_);
            leanh::lean_dec(v_h__2_72_);
            v_it_74_ = leanh::lean_ctor_get(v_x_70_, 0);
            leanh::lean_inc(v_it_74_);
            v_out_75_ = leanh::lean_ctor_get(v_x_70_, 1);
            leanh::lean_inc(v_out_75_);
            leanh::lean_dec_ref_known(v_x_70_, 2);
            v___x_76_ = leanh::lean_apply_2(v_h__1_71_, v_it_74_, v_out_75_);
            return v___x_76_;
        }
        1 => {
            let mut v_it_77_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_78_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_73_);
            leanh::lean_dec(v_h__1_71_);
            v_it_77_ = leanh::lean_ctor_get(v_x_70_, 0);
            leanh::lean_inc(v_it_77_);
            leanh::lean_dec_ref_known(v_x_70_, 1);
            v___x_78_ = leanh::lean_apply_1(v_h__2_72_, v_it_77_);
            return v___x_78_;
        }
        _ => {
            let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_80_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_72_);
            leanh::lean_dec(v_h__1_71_);
            v___x_79_ = leanh::lean_box(0);
            v___x_80_ = leanh::lean_apply_1(v_h__3_73_, v___x_79_);
            return v___x_80_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(
    mut v_n_81_: *mut leanh::LeanObject,
    mut v_h__1_82_: *mut leanh::LeanObject,
    mut v_h__2_83_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_84_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_85_: u8 = 0;
    v_zero_84_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_85_ = lean_nat_dec_eq(v_n_81_, v_zero_84_);
    if v_isZero_85_ == 1 {
        let mut v___x_86_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_87_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_83_);
        v___x_86_ = leanh::lean_box(0);
        v___x_87_ = leanh::lean_apply_1(v_h__1_82_, v___x_86_);
        return v___x_87_;
    } else {
        let mut v_one_88_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_89_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_90_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_82_);
        v_one_88_ = leanh::lean_unsigned_to_nat(1);
        v_n_89_ = lean_nat_sub(v_n_81_, v_one_88_);
        v___x_90_ = leanh::lean_apply_1(v_h__2_83_, v_n_89_);
        return v___x_90_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(
    mut v_n_91_: *mut leanh::LeanObject,
    mut v_h__1_92_: *mut leanh::LeanObject,
    mut v_h__2_93_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_94_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_94_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_91_, v_h__1_92_, v_h__2_93_);
    leanh::lean_dec(v_n_91_);
    return v_res_94_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(
    mut v_motive_95_: *mut leanh::LeanObject,
    mut v_n_96_: *mut leanh::LeanObject,
    mut v_h__1_97_: *mut leanh::LeanObject,
    mut v_h__2_98_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_99_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_100_: u8 = 0;
    v_zero_99_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_100_ = lean_nat_dec_eq(v_n_96_, v_zero_99_);
    if v_isZero_100_ == 1 {
        let mut v___x_101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_102_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_98_);
        v___x_101_ = leanh::lean_box(0);
        v___x_102_ = leanh::lean_apply_1(v_h__1_97_, v___x_101_);
        return v___x_102_;
    } else {
        let mut v_one_103_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_104_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_105_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_97_);
        v_one_103_ = leanh::lean_unsigned_to_nat(1);
        v_n_104_ = lean_nat_sub(v_n_96_, v_one_103_);
        v___x_105_ = leanh::lean_apply_1(v_h__2_98_, v_n_104_);
        return v___x_105_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(
    mut v_motive_106_: *mut leanh::LeanObject,
    mut v_n_107_: *mut leanh::LeanObject,
    mut v_h__1_108_: *mut leanh::LeanObject,
    mut v_h__2_109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_110_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(v_motive_106_, v_n_107_, v_h__1_108_, v_h__2_109_);
    leanh::lean_dec(v_n_107_);
    return v_res_110_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Consumers_Access(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
}