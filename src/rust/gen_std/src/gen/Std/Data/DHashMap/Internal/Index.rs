// Lean compiler output
// Module: Std.Data.DHashMap.Internal.Index
// Imports: Init.Data.UInt.Bitwise Init.ByCases Init.Data.UInt.Lemmas
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::UInt::Bitwise::{
    initialize_Init_Data_UInt_Bitwise, runtime_initialize_Init_Data_UInt_Bitwise,
};
use crate::r#gen::Init::Data::UInt::Lemmas::{
    initialize_Init_Data_UInt_Lemmas, runtime_initialize_Init_Data_UInt_Lemmas,
};
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{lean_usize_of_nat, lean_usize_sub};
pub unsafe fn l_Std_DHashMap_Internal_scrambleHash(mut v_hash_50_: u64) -> u64 {
    let mut v___x_51_: u64 = 0;
    let mut v___x_52_: u64 = 0;
    let mut v_fold_53_: u64 = 0;
    let mut v___x_54_: u64 = 0;
    let mut v___x_55_: u64 = 0;
    let mut v___x_56_: u64 = 0;
    v___x_51_ = 32u64;
    v___x_52_ = lean_uint64_shift_right(v_hash_50_, v___x_51_);
    v_fold_53_ = lean_uint64_xor(v_hash_50_, v___x_52_);
    v___x_54_ = 16u64;
    v___x_55_ = lean_uint64_shift_right(v_fold_53_, v___x_54_);
    v___x_56_ = lean_uint64_xor(v_fold_53_, v___x_55_);
    return v___x_56_;
}
pub unsafe fn l_Std_DHashMap_Internal_scrambleHash___boxed(
    mut v_hash_57_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hash_boxed_58_: u64 = 0;
    let mut v_res_59_: u64 = 0;
    let mut v_r_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hash_boxed_58_ = crate::leanh::lean_unbox_uint64(v_hash_57_);
    crate::leanh::lean_dec_ref(v_hash_57_);
    v_res_59_ = l_Std_DHashMap_Internal_scrambleHash(v_hash_boxed_58_);
    v_r_60_ = crate::leanh::lean_box_uint64(v_res_59_);
    return v_r_60_;
}
pub unsafe fn l_Std_DHashMap_Internal_mkIdx___redArg(
    mut v_sz_61_: *mut crate::leanh::LeanObject,
    mut v_hash_62_: u64,
) -> usize {
    let mut v___x_63_: u64 = 0;
    let mut v___x_64_: u64 = 0;
    let mut v_fold_65_: u64 = 0;
    let mut v___x_66_: u64 = 0;
    let mut v___x_67_: u64 = 0;
    let mut v___x_68_: u64 = 0;
    let mut v___x_69_: usize = 0;
    let mut v___x_70_: usize = 0;
    let mut v___x_71_: usize = 0;
    let mut v___x_72_: usize = 0;
    let mut v___x_73_: usize = 0;
    v___x_63_ = 32u64;
    v___x_64_ = lean_uint64_shift_right(v_hash_62_, v___x_63_);
    v_fold_65_ = lean_uint64_xor(v_hash_62_, v___x_64_);
    v___x_66_ = 16u64;
    v___x_67_ = lean_uint64_shift_right(v_fold_65_, v___x_66_);
    v___x_68_ = lean_uint64_xor(v_fold_65_, v___x_67_);
    v___x_69_ = lean_uint64_to_usize(v___x_68_);
    v___x_70_ = lean_usize_of_nat(v_sz_61_);
    v___x_71_ = 1usize;
    v___x_72_ = lean_usize_sub(v___x_70_, v___x_71_);
    v___x_73_ = lean_usize_land(v___x_69_, v___x_72_);
    return v___x_73_;
}
pub unsafe fn l_Std_DHashMap_Internal_mkIdx___redArg___boxed(
    mut v_sz_74_: *mut crate::leanh::LeanObject,
    mut v_hash_75_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hash_boxed_76_: u64 = 0;
    let mut v_res_77_: usize = 0;
    let mut v_r_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hash_boxed_76_ = crate::leanh::lean_unbox_uint64(v_hash_75_);
    crate::leanh::lean_dec_ref(v_hash_75_);
    v_res_77_ = l_Std_DHashMap_Internal_mkIdx___redArg(v_sz_74_, v_hash_boxed_76_);
    crate::leanh::lean_dec(v_sz_74_);
    v_r_78_ = crate::leanh::lean_box_usize(v_res_77_);
    return v_r_78_;
}
pub unsafe fn l_Std_DHashMap_Internal_mkIdx(
    mut v_sz_79_: *mut crate::leanh::LeanObject,
    mut v_h_80_: *mut crate::leanh::LeanObject,
    mut v_hash_81_: u64,
) -> usize {
    let mut v___x_82_: u64 = 0;
    let mut v___x_83_: u64 = 0;
    let mut v_fold_84_: u64 = 0;
    let mut v___x_85_: u64 = 0;
    let mut v___x_86_: u64 = 0;
    let mut v___x_87_: u64 = 0;
    let mut v___x_88_: usize = 0;
    let mut v___x_89_: usize = 0;
    let mut v___x_90_: usize = 0;
    let mut v___x_91_: usize = 0;
    let mut v___x_92_: usize = 0;
    v___x_82_ = 32u64;
    v___x_83_ = lean_uint64_shift_right(v_hash_81_, v___x_82_);
    v_fold_84_ = lean_uint64_xor(v_hash_81_, v___x_83_);
    v___x_85_ = 16u64;
    v___x_86_ = lean_uint64_shift_right(v_fold_84_, v___x_85_);
    v___x_87_ = lean_uint64_xor(v_fold_84_, v___x_86_);
    v___x_88_ = lean_uint64_to_usize(v___x_87_);
    v___x_89_ = lean_usize_of_nat(v_sz_79_);
    v___x_90_ = 1usize;
    v___x_91_ = lean_usize_sub(v___x_89_, v___x_90_);
    v___x_92_ = lean_usize_land(v___x_88_, v___x_91_);
    return v___x_92_;
}
pub unsafe fn l_Std_DHashMap_Internal_mkIdx___boxed(
    mut v_sz_93_: *mut crate::leanh::LeanObject,
    mut v_h_94_: *mut crate::leanh::LeanObject,
    mut v_hash_95_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hash_boxed_96_: u64 = 0;
    let mut v_res_97_: usize = 0;
    let mut v_r_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hash_boxed_96_ = crate::leanh::lean_unbox_uint64(v_hash_95_);
    crate::leanh::lean_dec_ref(v_hash_95_);
    v_res_97_ = l_Std_DHashMap_Internal_mkIdx(v_sz_93_, v_h_94_, v_hash_boxed_96_);
    crate::leanh::lean_dec(v_sz_93_);
    v_r_98_ = crate::leanh::lean_box_usize(v_res_97_);
    return v_r_98_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Internal_Index(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_UInt_Bitwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Internal_Index(
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
pub unsafe fn initialize_Std_Data_DHashMap_Internal_Index(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_UInt_Bitwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Index(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Internal_Index(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Internal_Index(builtin);
}
