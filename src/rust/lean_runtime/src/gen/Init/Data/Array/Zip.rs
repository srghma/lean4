// Lean compiler output
// Module: Init.Data.Array.Zip
// Imports: Init.Data.Array.Basic Init.Control.Lawful Init.Data.Function Init.Data.Array.Lemmas Init.Data.List.Nat.TakeDrop Init.Data.List.Zip Init.Data.Option.Lemmas Init.Data.Prod Init.Omega
use crate::r#gen::Init::Control::Lawful::{
    initialize_Init_Control_Lawful, runtime_initialize_Init_Control_Lawful,
};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Function::{
    initialize_Init_Data_Function, runtime_initialize_Init_Data_Function,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::Zip::{
    initialize_Init_Data_List_Zip, runtime_initialize_Init_Data_List_Zip,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Prod::{
    initialize_Init_Data_Prod, runtime_initialize_Init_Data_Prod,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWith_match__1_splitter___redArg(
    mut v_x_81_: *mut LeanObject,
    mut v_x_82_: *mut LeanObject,
    mut v_h__1_83_: *mut LeanObject,
    mut v_h__2_84_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_81_) == 1 {
        if lean_obj_tag(v_x_82_) == 1 {
            let mut v_val_85_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_86_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_87_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_84_);
            v_val_85_ = lean_ctor_get(v_x_81_, 0);
            lean_inc(v_val_85_);
            lean_dec_ref_known(v_x_81_, 1);
            v_val_86_ = lean_ctor_get(v_x_82_, 0);
            lean_inc(v_val_86_);
            lean_dec_ref_known(v_x_82_, 1);
            v___x_87_ = lean_apply_2(v_h__1_83_, v_val_85_, v_val_86_);
            return v___x_87_;
        } else {
            let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_83_);
            v___x_88_ = lean_apply_3(v_h__2_84_, v_x_81_, v_x_82_, lean_box(0));
            return v___x_88_;
        }
    } else {
        let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_83_);
        v___x_89_ = lean_apply_3(v_h__2_84_, v_x_81_, v_x_82_, lean_box(0));
        return v___x_89_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWith_match__1_splitter(
    mut v_00_u03b1_90_: *mut LeanObject,
    mut v_00_u03b2_91_: *mut LeanObject,
    mut v_motive_92_: *mut LeanObject,
    mut v_x_93_: *mut LeanObject,
    mut v_x_94_: *mut LeanObject,
    mut v_h__1_95_: *mut LeanObject,
    mut v_h__2_96_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_93_) == 1 {
        if lean_obj_tag(v_x_94_) == 1 {
            let mut v_val_97_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_98_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_96_);
            v_val_97_ = lean_ctor_get(v_x_93_, 0);
            lean_inc(v_val_97_);
            lean_dec_ref_known(v_x_93_, 1);
            v_val_98_ = lean_ctor_get(v_x_94_, 0);
            lean_inc(v_val_98_);
            lean_dec_ref_known(v_x_94_, 1);
            v___x_99_ = lean_apply_2(v_h__1_95_, v_val_97_, v_val_98_);
            return v___x_99_;
        } else {
            let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_95_);
            v___x_100_ = lean_apply_3(v_h__2_96_, v_x_93_, v_x_94_, lean_box(0));
            return v___x_100_;
        }
    } else {
        let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_95_);
        v___x_101_ = lean_apply_3(v_h__2_96_, v_x_93_, v_x_94_, lean_box(0));
        return v___x_101_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWith_match__1_splitter___redArg(
    mut v_x_102_: *mut LeanObject,
    mut v_x_103_: *mut LeanObject,
    mut v_h__1_104_: *mut LeanObject,
    mut v_h__2_105_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_102_) == 1 {
        if lean_obj_tag(v_x_103_) == 1 {
            let mut v_val_106_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_107_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_105_);
            v_val_106_ = lean_ctor_get(v_x_102_, 0);
            lean_inc(v_val_106_);
            lean_dec_ref_known(v_x_102_, 1);
            v_val_107_ = lean_ctor_get(v_x_103_, 0);
            lean_inc(v_val_107_);
            lean_dec_ref_known(v_x_103_, 1);
            v___x_108_ = lean_apply_2(v_h__1_104_, v_val_106_, v_val_107_);
            return v___x_108_;
        } else {
            let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_104_);
            v___x_109_ = lean_apply_3(v_h__2_105_, v_x_102_, v_x_103_, lean_box(0));
            return v___x_109_;
        }
    } else {
        let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_104_);
        v___x_110_ = lean_apply_3(v_h__2_105_, v_x_102_, v_x_103_, lean_box(0));
        return v___x_110_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWith_match__1_splitter(
    mut v_00_u03b1_111_: *mut LeanObject,
    mut v_00_u03b2_112_: *mut LeanObject,
    mut v_motive_113_: *mut LeanObject,
    mut v_x_114_: *mut LeanObject,
    mut v_x_115_: *mut LeanObject,
    mut v_h__1_116_: *mut LeanObject,
    mut v_h__2_117_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_114_) == 1 {
        if lean_obj_tag(v_x_115_) == 1 {
            let mut v_val_118_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_119_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_117_);
            v_val_118_ = lean_ctor_get(v_x_114_, 0);
            lean_inc(v_val_118_);
            lean_dec_ref_known(v_x_114_, 1);
            v_val_119_ = lean_ctor_get(v_x_115_, 0);
            lean_inc(v_val_119_);
            lean_dec_ref_known(v_x_115_, 1);
            v___x_120_ = lean_apply_2(v_h__1_116_, v_val_118_, v_val_119_);
            return v___x_120_;
        } else {
            let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_116_);
            v___x_121_ = lean_apply_3(v_h__2_117_, v_x_114_, v_x_115_, lean_box(0));
            return v___x_121_;
        }
    } else {
        let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_116_);
        v___x_122_ = lean_apply_3(v_h__2_117_, v_x_114_, v_x_115_, lean_box(0));
        return v___x_122_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter___redArg(
    mut v_x_123_: *mut LeanObject,
    mut v_x_124_: *mut LeanObject,
    mut v_h__1_125_: *mut LeanObject,
    mut v_h__2_126_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_123_) == 0 {
        if lean_obj_tag(v_x_124_) == 0 {
            let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_126_);
            v___x_127_ = lean_box(0);
            v___x_128_ = lean_apply_1(v_h__1_125_, v___x_127_);
            return v___x_128_;
        } else {
            let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_125_);
            v___x_129_ = lean_apply_3(v_h__2_126_, v_x_123_, v_x_124_, lean_box(0));
            return v___x_129_;
        }
    } else {
        let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_125_);
        v___x_130_ = lean_apply_3(v_h__2_126_, v_x_123_, v_x_124_, lean_box(0));
        return v___x_130_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter(
    mut v_00_u03b1_131_: *mut LeanObject,
    mut v_00_u03b2_132_: *mut LeanObject,
    mut v_motive_133_: *mut LeanObject,
    mut v_x_134_: *mut LeanObject,
    mut v_x_135_: *mut LeanObject,
    mut v_h__1_136_: *mut LeanObject,
    mut v_h__2_137_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_134_) == 0 {
        if lean_obj_tag(v_x_135_) == 0 {
            let mut v___x_138_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_137_);
            v___x_138_ = lean_box(0);
            v___x_139_ = lean_apply_1(v_h__1_136_, v___x_138_);
            return v___x_139_;
        } else {
            let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_136_);
            v___x_140_ = lean_apply_3(v_h__2_137_, v_x_134_, v_x_135_, lean_box(0));
            return v___x_140_;
        }
    } else {
        let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_136_);
        v___x_141_ = lean_apply_3(v_h__2_137_, v_x_134_, v_x_135_, lean_box(0));
        return v___x_141_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWithAll_match__1_splitter___redArg(
    mut v_x_142_: *mut LeanObject,
    mut v_x_143_: *mut LeanObject,
    mut v_h__1_144_: *mut LeanObject,
    mut v_h__2_145_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_142_) == 0 {
        if lean_obj_tag(v_x_143_) == 0 {
            let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_145_);
            v___x_146_ = lean_box(0);
            v___x_147_ = lean_apply_1(v_h__1_144_, v___x_146_);
            return v___x_147_;
        } else {
            let mut v___x_148_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_144_);
            v___x_148_ = lean_apply_3(v_h__2_145_, v_x_142_, v_x_143_, lean_box(0));
            return v___x_148_;
        }
    } else {
        let mut v___x_149_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_144_);
        v___x_149_ = lean_apply_3(v_h__2_145_, v_x_142_, v_x_143_, lean_box(0));
        return v___x_149_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWithAll_match__1_splitter(
    mut v_00_u03b1_150_: *mut LeanObject,
    mut v_00_u03b2_151_: *mut LeanObject,
    mut v_motive_152_: *mut LeanObject,
    mut v_x_153_: *mut LeanObject,
    mut v_x_154_: *mut LeanObject,
    mut v_h__1_155_: *mut LeanObject,
    mut v_h__2_156_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_153_) == 0 {
        if lean_obj_tag(v_x_154_) == 0 {
            let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_156_);
            v___x_157_ = lean_box(0);
            v___x_158_ = lean_apply_1(v_h__1_155_, v___x_157_);
            return v___x_158_;
        } else {
            let mut v___x_159_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_155_);
            v___x_159_ = lean_apply_3(v_h__2_156_, v_x_153_, v_x_154_, lean_box(0));
            return v___x_159_;
        }
    } else {
        let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_155_);
        v___x_160_ = lean_apply_3(v_h__2_156_, v_x_153_, v_x_154_, lean_box(0));
        return v___x_160_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Zip(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Control_Lawful(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Zip(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Zip(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Init_Control_Lawful(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_Zip(builtin);
}
