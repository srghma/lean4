// Lean compiler output
// Module: Init.Data.SInt.Float
// Imports: Init.Data.Float Init.Data.SInt.Basic
use crate::ffi::{
    lean_float_to_int8, lean_float_to_int16, lean_float_to_int32, lean_float_to_int64,
    lean_float_to_isize, lean_int8_to_float, lean_int16_to_float, lean_int32_to_float,
    lean_int64_to_float, lean_isize_to_float,
};
use crate::r#gen::Init::Data::Float::{
    initialize_Init_Data_Float, runtime_initialize_Init_Data_Float,
};
use crate::r#gen::Init::Data::SInt::Basic::{
    initialize_Init_Data_SInt_Basic, runtime_initialize_Init_Data_SInt_Basic,
};
pub unsafe fn l_Float_toInt8___boxed(
    mut v_a_00___x40___internal___hyg_52_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_53_: f64 = 0.0;
    let mut v_res_54_: u8 = 0;
    let mut v_r_55_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_53_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_52_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_52_);
    v_res_54_ = lean_float_to_int8(v_a_00___x40___internal___hyg_1__boxed_53_);
    v_r_55_ = leanh::lean_box((v_res_54_) as usize);
    return v_r_55_;
}
pub unsafe fn l_Float_toInt16___boxed(
    mut v_a_00___x40___internal___hyg_57_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_58_: f64 = 0.0;
    let mut v_res_59_: u16 = 0;
    let mut v_r_60_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_58_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_57_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_57_);
    v_res_59_ = lean_float_to_int16(v_a_00___x40___internal___hyg_1__boxed_58_);
    v_r_60_ = leanh::lean_box((v_res_59_) as usize);
    return v_r_60_;
}
pub unsafe fn l_Float_toInt32___boxed(
    mut v_a_00___x40___internal___hyg_62_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_63_: f64 = 0.0;
    let mut v_res_64_: u32 = 0;
    let mut v_r_65_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_63_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_62_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_62_);
    v_res_64_ = lean_float_to_int32(v_a_00___x40___internal___hyg_1__boxed_63_);
    v_r_65_ = leanh::lean_box_uint32(v_res_64_);
    return v_r_65_;
}
pub unsafe fn l_Float_toInt64___boxed(
    mut v_a_00___x40___internal___hyg_67_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_68_: f64 = 0.0;
    let mut v_res_69_: u64 = 0;
    let mut v_r_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_68_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_67_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_67_);
    v_res_69_ = lean_float_to_int64(v_a_00___x40___internal___hyg_1__boxed_68_);
    v_r_70_ = leanh::lean_box_uint64(v_res_69_);
    return v_r_70_;
}
pub unsafe fn l_Float_toISize___boxed(
    mut v_a_00___x40___internal___hyg_72_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_73_: f64 = 0.0;
    let mut v_res_74_: usize = 0;
    let mut v_r_75_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_73_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_72_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_72_);
    v_res_74_ = lean_float_to_isize(v_a_00___x40___internal___hyg_1__boxed_73_);
    v_r_75_ = leanh::lean_box_usize(v_res_74_);
    return v_r_75_;
}
pub unsafe fn l_Int8_toFloat___boxed(
    mut v_n_77_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_78_: u8 = 0;
    let mut v_res_79_: f64 = 0.0;
    let mut v_r_80_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_78_ = (leanh::lean_unbox(v_n_77_) as u8);
    v_res_79_ = lean_int8_to_float(v_n_boxed_78_);
    v_r_80_ = leanh::lean_box_float(v_res_79_);
    return v_r_80_;
}
pub unsafe fn l_Int16_toFloat___boxed(
    mut v_n_82_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_83_: u16 = 0;
    let mut v_res_84_: f64 = 0.0;
    let mut v_r_85_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_83_ = (leanh::lean_unbox(v_n_82_) as u16);
    v_res_84_ = lean_int16_to_float(v_n_boxed_83_);
    v_r_85_ = leanh::lean_box_float(v_res_84_);
    return v_r_85_;
}
pub unsafe fn l_Int32_toFloat___boxed(
    mut v_n_87_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_88_: u32 = 0;
    let mut v_res_89_: f64 = 0.0;
    let mut v_r_90_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_88_ = leanh::lean_unbox_uint32(v_n_87_);
    leanh::lean_dec(v_n_87_);
    v_res_89_ = lean_int32_to_float(v_n_boxed_88_);
    v_r_90_ = leanh::lean_box_float(v_res_89_);
    return v_r_90_;
}
pub unsafe fn l_Int64_toFloat___boxed(
    mut v_n_92_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_93_: u64 = 0;
    let mut v_res_94_: f64 = 0.0;
    let mut v_r_95_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_93_ = leanh::lean_unbox_uint64(v_n_92_);
    leanh::lean_dec_ref(v_n_92_);
    v_res_94_ = lean_int64_to_float(v_n_boxed_93_);
    v_r_95_ = leanh::lean_box_float(v_res_94_);
    return v_r_95_;
}
pub unsafe fn l_ISize_toFloat___boxed(
    mut v_n_97_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_98_: usize = 0;
    let mut v_res_99_: f64 = 0.0;
    let mut v_r_100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_98_ = leanh::lean_unbox_usize(v_n_97_);
    leanh::lean_dec(v_n_97_);
    v_res_99_ = lean_isize_to_float(v_n_boxed_98_);
    v_r_100_ = leanh::lean_box_float(v_res_99_);
    return v_r_100_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_SInt_Float(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Float(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_SInt_Float(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_SInt_Float(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Float(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Float(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_SInt_Float(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_SInt_Float(builtin);
}