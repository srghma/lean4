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
pub unsafe fn l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWith_match__1_splitter___redArg(
    mut v_x_81_: *mut leanh::LeanObject,
    mut v_x_82_: *mut leanh::LeanObject,
    mut v_h__1_83_: *mut leanh::LeanObject,
    mut v_h__2_84_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_81_) == 1 {
        if leanh::lean_obj_tag(v_x_82_) == 1 {
            let mut v_val_85_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_86_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_87_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_84_);
            v_val_85_ = leanh::lean_ctor_get(v_x_81_, 0);
            leanh::lean_inc(v_val_85_);
            leanh::lean_dec_ref_known(v_x_81_, 1);
            v_val_86_ = leanh::lean_ctor_get(v_x_82_, 0);
            leanh::lean_inc(v_val_86_);
            leanh::lean_dec_ref_known(v_x_82_, 1);
            v___x_87_ = leanh::lean_apply_2(v_h__1_83_, v_val_85_, v_val_86_);
            return v___x_87_;
        } else {
            let mut v___x_88_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_83_);
            v___x_88_ =
                leanh::lean_apply_3(v_h__2_84_, v_x_81_, v_x_82_, leanh::lean_box(0));
            return v___x_88_;
        }
    } else {
        let mut v___x_89_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_83_);
        v___x_89_ =
            leanh::lean_apply_3(v_h__2_84_, v_x_81_, v_x_82_, leanh::lean_box(0));
        return v___x_89_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWith_match__1_splitter(
    mut v_00_u03b1_90_: *mut leanh::LeanObject,
    mut v_00_u03b2_91_: *mut leanh::LeanObject,
    mut v_motive_92_: *mut leanh::LeanObject,
    mut v_x_93_: *mut leanh::LeanObject,
    mut v_x_94_: *mut leanh::LeanObject,
    mut v_h__1_95_: *mut leanh::LeanObject,
    mut v_h__2_96_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_93_) == 1 {
        if leanh::lean_obj_tag(v_x_94_) == 1 {
            let mut v_val_97_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_98_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_99_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_96_);
            v_val_97_ = leanh::lean_ctor_get(v_x_93_, 0);
            leanh::lean_inc(v_val_97_);
            leanh::lean_dec_ref_known(v_x_93_, 1);
            v_val_98_ = leanh::lean_ctor_get(v_x_94_, 0);
            leanh::lean_inc(v_val_98_);
            leanh::lean_dec_ref_known(v_x_94_, 1);
            v___x_99_ = leanh::lean_apply_2(v_h__1_95_, v_val_97_, v_val_98_);
            return v___x_99_;
        } else {
            let mut v___x_100_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_95_);
            v___x_100_ =
                leanh::lean_apply_3(v_h__2_96_, v_x_93_, v_x_94_, leanh::lean_box(0));
            return v___x_100_;
        }
    } else {
        let mut v___x_101_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_95_);
        v___x_101_ =
            leanh::lean_apply_3(v_h__2_96_, v_x_93_, v_x_94_, leanh::lean_box(0));
        return v___x_101_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWith_match__1_splitter___redArg(
    mut v_x_102_: *mut leanh::LeanObject,
    mut v_x_103_: *mut leanh::LeanObject,
    mut v_h__1_104_: *mut leanh::LeanObject,
    mut v_h__2_105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_102_) == 1 {
        if leanh::lean_obj_tag(v_x_103_) == 1 {
            let mut v_val_106_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_107_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_108_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_105_);
            v_val_106_ = leanh::lean_ctor_get(v_x_102_, 0);
            leanh::lean_inc(v_val_106_);
            leanh::lean_dec_ref_known(v_x_102_, 1);
            v_val_107_ = leanh::lean_ctor_get(v_x_103_, 0);
            leanh::lean_inc(v_val_107_);
            leanh::lean_dec_ref_known(v_x_103_, 1);
            v___x_108_ = leanh::lean_apply_2(v_h__1_104_, v_val_106_, v_val_107_);
            return v___x_108_;
        } else {
            let mut v___x_109_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_104_);
            v___x_109_ = leanh::lean_apply_3(
                v_h__2_105_,
                v_x_102_,
                v_x_103_,
                leanh::lean_box(0),
            );
            return v___x_109_;
        }
    } else {
        let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_104_);
        v___x_110_ =
            leanh::lean_apply_3(v_h__2_105_, v_x_102_, v_x_103_, leanh::lean_box(0));
        return v___x_110_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWith_match__1_splitter(
    mut v_00_u03b1_111_: *mut leanh::LeanObject,
    mut v_00_u03b2_112_: *mut leanh::LeanObject,
    mut v_motive_113_: *mut leanh::LeanObject,
    mut v_x_114_: *mut leanh::LeanObject,
    mut v_x_115_: *mut leanh::LeanObject,
    mut v_h__1_116_: *mut leanh::LeanObject,
    mut v_h__2_117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_114_) == 1 {
        if leanh::lean_obj_tag(v_x_115_) == 1 {
            let mut v_val_118_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_119_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_120_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_117_);
            v_val_118_ = leanh::lean_ctor_get(v_x_114_, 0);
            leanh::lean_inc(v_val_118_);
            leanh::lean_dec_ref_known(v_x_114_, 1);
            v_val_119_ = leanh::lean_ctor_get(v_x_115_, 0);
            leanh::lean_inc(v_val_119_);
            leanh::lean_dec_ref_known(v_x_115_, 1);
            v___x_120_ = leanh::lean_apply_2(v_h__1_116_, v_val_118_, v_val_119_);
            return v___x_120_;
        } else {
            let mut v___x_121_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_116_);
            v___x_121_ = leanh::lean_apply_3(
                v_h__2_117_,
                v_x_114_,
                v_x_115_,
                leanh::lean_box(0),
            );
            return v___x_121_;
        }
    } else {
        let mut v___x_122_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_116_);
        v___x_122_ =
            leanh::lean_apply_3(v_h__2_117_, v_x_114_, v_x_115_, leanh::lean_box(0));
        return v___x_122_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter___redArg(
    mut v_x_123_: *mut leanh::LeanObject,
    mut v_x_124_: *mut leanh::LeanObject,
    mut v_h__1_125_: *mut leanh::LeanObject,
    mut v_h__2_126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_123_) == 0 {
        if leanh::lean_obj_tag(v_x_124_) == 0 {
            let mut v___x_127_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_128_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_126_);
            v___x_127_ = leanh::lean_box(0);
            v___x_128_ = leanh::lean_apply_1(v_h__1_125_, v___x_127_);
            return v___x_128_;
        } else {
            let mut v___x_129_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_125_);
            v___x_129_ = leanh::lean_apply_3(
                v_h__2_126_,
                v_x_123_,
                v_x_124_,
                leanh::lean_box(0),
            );
            return v___x_129_;
        }
    } else {
        let mut v___x_130_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_125_);
        v___x_130_ =
            leanh::lean_apply_3(v_h__2_126_, v_x_123_, v_x_124_, leanh::lean_box(0));
        return v___x_130_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter(
    mut v_00_u03b1_131_: *mut leanh::LeanObject,
    mut v_00_u03b2_132_: *mut leanh::LeanObject,
    mut v_motive_133_: *mut leanh::LeanObject,
    mut v_x_134_: *mut leanh::LeanObject,
    mut v_x_135_: *mut leanh::LeanObject,
    mut v_h__1_136_: *mut leanh::LeanObject,
    mut v_h__2_137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_134_) == 0 {
        if leanh::lean_obj_tag(v_x_135_) == 0 {
            let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_137_);
            v___x_138_ = leanh::lean_box(0);
            v___x_139_ = leanh::lean_apply_1(v_h__1_136_, v___x_138_);
            return v___x_139_;
        } else {
            let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_136_);
            v___x_140_ = leanh::lean_apply_3(
                v_h__2_137_,
                v_x_134_,
                v_x_135_,
                leanh::lean_box(0),
            );
            return v___x_140_;
        }
    } else {
        let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_136_);
        v___x_141_ =
            leanh::lean_apply_3(v_h__2_137_, v_x_134_, v_x_135_, leanh::lean_box(0));
        return v___x_141_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWithAll_match__1_splitter___redArg(
    mut v_x_142_: *mut leanh::LeanObject,
    mut v_x_143_: *mut leanh::LeanObject,
    mut v_h__1_144_: *mut leanh::LeanObject,
    mut v_h__2_145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_142_) == 0 {
        if leanh::lean_obj_tag(v_x_143_) == 0 {
            let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_147_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_145_);
            v___x_146_ = leanh::lean_box(0);
            v___x_147_ = leanh::lean_apply_1(v_h__1_144_, v___x_146_);
            return v___x_147_;
        } else {
            let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_144_);
            v___x_148_ = leanh::lean_apply_3(
                v_h__2_145_,
                v_x_142_,
                v_x_143_,
                leanh::lean_box(0),
            );
            return v___x_148_;
        }
    } else {
        let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_144_);
        v___x_149_ =
            leanh::lean_apply_3(v_h__2_145_, v_x_142_, v_x_143_, leanh::lean_box(0));
        return v___x_149_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWithAll_match__1_splitter(
    mut v_00_u03b1_150_: *mut leanh::LeanObject,
    mut v_00_u03b2_151_: *mut leanh::LeanObject,
    mut v_motive_152_: *mut leanh::LeanObject,
    mut v_x_153_: *mut leanh::LeanObject,
    mut v_x_154_: *mut leanh::LeanObject,
    mut v_h__1_155_: *mut leanh::LeanObject,
    mut v_h__2_156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_153_) == 0 {
        if leanh::lean_obj_tag(v_x_154_) == 0 {
            let mut v___x_157_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_156_);
            v___x_157_ = leanh::lean_box(0);
            v___x_158_ = leanh::lean_apply_1(v_h__1_155_, v___x_157_);
            return v___x_158_;
        } else {
            let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_155_);
            v___x_159_ = leanh::lean_apply_3(
                v_h__2_156_,
                v_x_153_,
                v_x_154_,
                leanh::lean_box(0),
            );
            return v___x_159_;
        }
    } else {
        let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_155_);
        v___x_160_ =
            leanh::lean_apply_3(v_h__2_156_, v_x_153_, v_x_154_, leanh::lean_box(0));
        return v___x_160_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Zip(builtin: u8) -> *mut leanh::LeanObject {
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
    res = runtime_initialize_Init_Control_Lawful(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Function(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Zip(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Zip(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Init_Control_Lawful(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Function(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Zip(builtin);
}