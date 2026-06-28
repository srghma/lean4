// Lean compiler output
// Module: Init.Data.SInt.Float32
// Imports: Init.Data.Float32 Init.Data.SInt.Basic
use crate::r#gen::Init::Data::Float32::{
    initialize_Init_Data_Float32, runtime_initialize_Init_Data_Float32,
};
use crate::r#gen::Init::Data::SInt::Basic::{
    initialize_Init_Data_SInt_Basic, runtime_initialize_Init_Data_SInt_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_box_float32, lean_box_uint32, lean_box_uint64,
    lean_box_usize, lean_dec, lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_unbox, lean_unbox_float32, lean_unbox_uint32, lean_unbox_uint64, lean_unbox_usize,
};
pub unsafe fn l_Float32_toInt8___boxed(
    mut v_a_00___x40___internal___hyg_52_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_53_: f32 = 0.0f32;
    let mut v_res_54_: u8 = 0;
    let mut v_r_55_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_53_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_52_);
    lean_dec_ref(v_a_00___x40___internal___hyg_52_);
    v_res_54_ = lean_float32_to_int8(v_a_00___x40___internal___hyg_1__boxed_53_);
    v_r_55_ = lean_box((v_res_54_) as usize);
    return v_r_55_;
}
pub unsafe fn l_Float32_toInt16___boxed(
    mut v_a_00___x40___internal___hyg_57_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_58_: f32 = 0.0f32;
    let mut v_res_59_: u16 = 0;
    let mut v_r_60_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_58_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_57_);
    lean_dec_ref(v_a_00___x40___internal___hyg_57_);
    v_res_59_ = lean_float32_to_int16(v_a_00___x40___internal___hyg_1__boxed_58_);
    v_r_60_ = lean_box((v_res_59_) as usize);
    return v_r_60_;
}
pub unsafe fn l_Float32_toInt32___boxed(
    mut v_a_00___x40___internal___hyg_62_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_63_: f32 = 0.0f32;
    let mut v_res_64_: u32 = 0;
    let mut v_r_65_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_63_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_62_);
    lean_dec_ref(v_a_00___x40___internal___hyg_62_);
    v_res_64_ = lean_float32_to_int32(v_a_00___x40___internal___hyg_1__boxed_63_);
    v_r_65_ = lean_box_uint32(v_res_64_);
    return v_r_65_;
}
pub unsafe fn l_Float32_toInt64___boxed(
    mut v_a_00___x40___internal___hyg_67_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_68_: f32 = 0.0f32;
    let mut v_res_69_: u64 = 0;
    let mut v_r_70_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_68_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_67_);
    lean_dec_ref(v_a_00___x40___internal___hyg_67_);
    v_res_69_ = lean_float32_to_int64(v_a_00___x40___internal___hyg_1__boxed_68_);
    v_r_70_ = lean_box_uint64(v_res_69_);
    return v_r_70_;
}
pub unsafe fn l_Float32_toISize___boxed(
    mut v_a_00___x40___internal___hyg_72_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_73_: f32 = 0.0f32;
    let mut v_res_74_: usize = 0;
    let mut v_r_75_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_73_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_72_);
    lean_dec_ref(v_a_00___x40___internal___hyg_72_);
    v_res_74_ = lean_float32_to_isize(v_a_00___x40___internal___hyg_1__boxed_73_);
    v_r_75_ = lean_box_usize(v_res_74_);
    return v_r_75_;
}
pub unsafe fn l_Int8_toFloat32___boxed(mut v_n_77_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_78_: u8 = 0;
    let mut v_res_79_: f32 = 0.0f32;
    let mut v_r_80_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_78_ = (lean_unbox(v_n_77_) as u8);
    v_res_79_ = lean_int8_to_float32(v_n_boxed_78_);
    v_r_80_ = lean_box_float32(v_res_79_);
    return v_r_80_;
}
pub unsafe fn l_Int16_toFloat32___boxed(mut v_n_82_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_83_: u16 = 0;
    let mut v_res_84_: f32 = 0.0f32;
    let mut v_r_85_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_83_ = (lean_unbox(v_n_82_) as u16);
    v_res_84_ = lean_int16_to_float32(v_n_boxed_83_);
    v_r_85_ = lean_box_float32(v_res_84_);
    return v_r_85_;
}
pub unsafe fn l_Int32_toFloat32___boxed(mut v_n_87_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_88_: u32 = 0;
    let mut v_res_89_: f32 = 0.0f32;
    let mut v_r_90_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_88_ = lean_unbox_uint32(v_n_87_);
    lean_dec(v_n_87_);
    v_res_89_ = lean_int32_to_float32(v_n_boxed_88_);
    v_r_90_ = lean_box_float32(v_res_89_);
    return v_r_90_;
}
pub unsafe fn l_Int64_toFloat32___boxed(mut v_n_92_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_93_: u64 = 0;
    let mut v_res_94_: f32 = 0.0f32;
    let mut v_r_95_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_93_ = lean_unbox_uint64(v_n_92_);
    lean_dec_ref(v_n_92_);
    v_res_94_ = lean_int64_to_float32(v_n_boxed_93_);
    v_r_95_ = lean_box_float32(v_res_94_);
    return v_r_95_;
}
pub unsafe fn l_ISize_toFloat32___boxed(mut v_n_97_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_98_: usize = 0;
    let mut v_res_99_: f32 = 0.0f32;
    let mut v_r_100_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_98_ = lean_unbox_usize(v_n_97_);
    lean_dec(v_n_97_);
    v_res_99_ = lean_isize_to_float32(v_n_boxed_98_);
    v_r_100_ = lean_box_float32(v_res_99_);
    return v_r_100_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_SInt_Float32(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Float32(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_SInt_Float32(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_SInt_Float32(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Float32(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_SInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Float32(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_SInt_Float32(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_SInt_Float32(builtin);
}
