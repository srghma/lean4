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
    mut v_x_81_: *mut crate::leanh::LeanObject,
    mut v_x_82_: *mut crate::leanh::LeanObject,
    mut v_h__1_83_: *mut crate::leanh::LeanObject,
    mut v_h__2_84_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_81_) == 1 {
        if crate::leanh::lean_obj_tag(v_x_82_) == 1 {
            let mut v_val_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_84_);
            v_val_85_ = crate::leanh::lean_ctor_get(v_x_81_, 0);
            crate::leanh::lean_inc(v_val_85_);
            crate::leanh::lean_dec_ref_known(v_x_81_, 1);
            v_val_86_ = crate::leanh::lean_ctor_get(v_x_82_, 0);
            crate::leanh::lean_inc(v_val_86_);
            crate::leanh::lean_dec_ref_known(v_x_82_, 1);
            v___x_87_ = crate::leanh::lean_apply_2(v_h__1_83_, v_val_85_, v_val_86_);
            return v___x_87_;
        } else {
            let mut v___x_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_83_);
            v___x_88_ =
                crate::leanh::lean_apply_3(v_h__2_84_, v_x_81_, v_x_82_, crate::leanh::lean_box(0));
            return v___x_88_;
        }
    } else {
        let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_83_);
        v___x_89_ =
            crate::leanh::lean_apply_3(v_h__2_84_, v_x_81_, v_x_82_, crate::leanh::lean_box(0));
        return v___x_89_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWith_match__1_splitter(
    mut v_00_u03b1_90_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_91_: *mut crate::leanh::LeanObject,
    mut v_motive_92_: *mut crate::leanh::LeanObject,
    mut v_x_93_: *mut crate::leanh::LeanObject,
    mut v_x_94_: *mut crate::leanh::LeanObject,
    mut v_h__1_95_: *mut crate::leanh::LeanObject,
    mut v_h__2_96_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_93_) == 1 {
        if crate::leanh::lean_obj_tag(v_x_94_) == 1 {
            let mut v_val_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_96_);
            v_val_97_ = crate::leanh::lean_ctor_get(v_x_93_, 0);
            crate::leanh::lean_inc(v_val_97_);
            crate::leanh::lean_dec_ref_known(v_x_93_, 1);
            v_val_98_ = crate::leanh::lean_ctor_get(v_x_94_, 0);
            crate::leanh::lean_inc(v_val_98_);
            crate::leanh::lean_dec_ref_known(v_x_94_, 1);
            v___x_99_ = crate::leanh::lean_apply_2(v_h__1_95_, v_val_97_, v_val_98_);
            return v___x_99_;
        } else {
            let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_95_);
            v___x_100_ =
                crate::leanh::lean_apply_3(v_h__2_96_, v_x_93_, v_x_94_, crate::leanh::lean_box(0));
            return v___x_100_;
        }
    } else {
        let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_95_);
        v___x_101_ =
            crate::leanh::lean_apply_3(v_h__2_96_, v_x_93_, v_x_94_, crate::leanh::lean_box(0));
        return v___x_101_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWith_match__1_splitter___redArg(
    mut v_x_102_: *mut crate::leanh::LeanObject,
    mut v_x_103_: *mut crate::leanh::LeanObject,
    mut v_h__1_104_: *mut crate::leanh::LeanObject,
    mut v_h__2_105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_102_) == 1 {
        if crate::leanh::lean_obj_tag(v_x_103_) == 1 {
            let mut v_val_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_105_);
            v_val_106_ = crate::leanh::lean_ctor_get(v_x_102_, 0);
            crate::leanh::lean_inc(v_val_106_);
            crate::leanh::lean_dec_ref_known(v_x_102_, 1);
            v_val_107_ = crate::leanh::lean_ctor_get(v_x_103_, 0);
            crate::leanh::lean_inc(v_val_107_);
            crate::leanh::lean_dec_ref_known(v_x_103_, 1);
            v___x_108_ = crate::leanh::lean_apply_2(v_h__1_104_, v_val_106_, v_val_107_);
            return v___x_108_;
        } else {
            let mut v___x_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_104_);
            v___x_109_ = crate::leanh::lean_apply_3(
                v_h__2_105_,
                v_x_102_,
                v_x_103_,
                crate::leanh::lean_box(0),
            );
            return v___x_109_;
        }
    } else {
        let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_104_);
        v___x_110_ =
            crate::leanh::lean_apply_3(v_h__2_105_, v_x_102_, v_x_103_, crate::leanh::lean_box(0));
        return v___x_110_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWith_match__1_splitter(
    mut v_00_u03b1_111_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_112_: *mut crate::leanh::LeanObject,
    mut v_motive_113_: *mut crate::leanh::LeanObject,
    mut v_x_114_: *mut crate::leanh::LeanObject,
    mut v_x_115_: *mut crate::leanh::LeanObject,
    mut v_h__1_116_: *mut crate::leanh::LeanObject,
    mut v_h__2_117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_114_) == 1 {
        if crate::leanh::lean_obj_tag(v_x_115_) == 1 {
            let mut v_val_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_117_);
            v_val_118_ = crate::leanh::lean_ctor_get(v_x_114_, 0);
            crate::leanh::lean_inc(v_val_118_);
            crate::leanh::lean_dec_ref_known(v_x_114_, 1);
            v_val_119_ = crate::leanh::lean_ctor_get(v_x_115_, 0);
            crate::leanh::lean_inc(v_val_119_);
            crate::leanh::lean_dec_ref_known(v_x_115_, 1);
            v___x_120_ = crate::leanh::lean_apply_2(v_h__1_116_, v_val_118_, v_val_119_);
            return v___x_120_;
        } else {
            let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_116_);
            v___x_121_ = crate::leanh::lean_apply_3(
                v_h__2_117_,
                v_x_114_,
                v_x_115_,
                crate::leanh::lean_box(0),
            );
            return v___x_121_;
        }
    } else {
        let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_116_);
        v___x_122_ =
            crate::leanh::lean_apply_3(v_h__2_117_, v_x_114_, v_x_115_, crate::leanh::lean_box(0));
        return v___x_122_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter___redArg(
    mut v_x_123_: *mut crate::leanh::LeanObject,
    mut v_x_124_: *mut crate::leanh::LeanObject,
    mut v_h__1_125_: *mut crate::leanh::LeanObject,
    mut v_h__2_126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_123_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_124_) == 0 {
            let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_126_);
            v___x_127_ = crate::leanh::lean_box(0);
            v___x_128_ = crate::leanh::lean_apply_1(v_h__1_125_, v___x_127_);
            return v___x_128_;
        } else {
            let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_125_);
            v___x_129_ = crate::leanh::lean_apply_3(
                v_h__2_126_,
                v_x_123_,
                v_x_124_,
                crate::leanh::lean_box(0),
            );
            return v___x_129_;
        }
    } else {
        let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_125_);
        v___x_130_ =
            crate::leanh::lean_apply_3(v_h__2_126_, v_x_123_, v_x_124_, crate::leanh::lean_box(0));
        return v___x_130_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter(
    mut v_00_u03b1_131_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_132_: *mut crate::leanh::LeanObject,
    mut v_motive_133_: *mut crate::leanh::LeanObject,
    mut v_x_134_: *mut crate::leanh::LeanObject,
    mut v_x_135_: *mut crate::leanh::LeanObject,
    mut v_h__1_136_: *mut crate::leanh::LeanObject,
    mut v_h__2_137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_134_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_135_) == 0 {
            let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_137_);
            v___x_138_ = crate::leanh::lean_box(0);
            v___x_139_ = crate::leanh::lean_apply_1(v_h__1_136_, v___x_138_);
            return v___x_139_;
        } else {
            let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_136_);
            v___x_140_ = crate::leanh::lean_apply_3(
                v_h__2_137_,
                v_x_134_,
                v_x_135_,
                crate::leanh::lean_box(0),
            );
            return v___x_140_;
        }
    } else {
        let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_136_);
        v___x_141_ =
            crate::leanh::lean_apply_3(v_h__2_137_, v_x_134_, v_x_135_, crate::leanh::lean_box(0));
        return v___x_141_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWithAll_match__1_splitter___redArg(
    mut v_x_142_: *mut crate::leanh::LeanObject,
    mut v_x_143_: *mut crate::leanh::LeanObject,
    mut v_h__1_144_: *mut crate::leanh::LeanObject,
    mut v_h__2_145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_142_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_143_) == 0 {
            let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_145_);
            v___x_146_ = crate::leanh::lean_box(0);
            v___x_147_ = crate::leanh::lean_apply_1(v_h__1_144_, v___x_146_);
            return v___x_147_;
        } else {
            let mut v___x_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_144_);
            v___x_148_ = crate::leanh::lean_apply_3(
                v_h__2_145_,
                v_x_142_,
                v_x_143_,
                crate::leanh::lean_box(0),
            );
            return v___x_148_;
        }
    } else {
        let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_144_);
        v___x_149_ =
            crate::leanh::lean_apply_3(v_h__2_145_, v_x_142_, v_x_143_, crate::leanh::lean_box(0));
        return v___x_149_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWithAll_match__1_splitter(
    mut v_00_u03b1_150_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_151_: *mut crate::leanh::LeanObject,
    mut v_motive_152_: *mut crate::leanh::LeanObject,
    mut v_x_153_: *mut crate::leanh::LeanObject,
    mut v_x_154_: *mut crate::leanh::LeanObject,
    mut v_h__1_155_: *mut crate::leanh::LeanObject,
    mut v_h__2_156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_153_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_154_) == 0 {
            let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_156_);
            v___x_157_ = crate::leanh::lean_box(0);
            v___x_158_ = crate::leanh::lean_apply_1(v_h__1_155_, v___x_157_);
            return v___x_158_;
        } else {
            let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_155_);
            v___x_159_ = crate::leanh::lean_apply_3(
                v_h__2_156_,
                v_x_153_,
                v_x_154_,
                crate::leanh::lean_box(0),
            );
            return v___x_159_;
        }
    } else {
        let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_155_);
        v___x_160_ =
            crate::leanh::lean_apply_3(v_h__2_156_, v_x_153_, v_x_154_, crate::leanh::lean_box(0));
        return v___x_160_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Zip(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Init_Control_Lawful(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Function(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Array_Zip(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Zip(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Init_Control_Lawful(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Function(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Zip(builtin);
}
