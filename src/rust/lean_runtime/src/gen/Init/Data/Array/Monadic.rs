// Lean compiler output
// Module: Init.Data.Array.Monadic
// Imports: Init.Data.List.Control Init.Data.Array.Basic Init.Data.Array.Attach Init.Data.Bool
use crate::r#gen::Init::Data::Array::Attach::{
    initialize_Init_Data_Array_Attach, runtime_initialize_Init_Data_Array_Attach,
};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Control::{
    initialize_Init_Data_List_Control, runtime_initialize_Init_Data_List_Control,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_foldlM__filterMap_match__1_splitter___redArg(
    mut v_x_97_: *mut LeanObject,
    mut v_h__1_98_: *mut LeanObject,
    mut v_h__2_99_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_97_) == 0 {
        let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_98_);
        v___x_100_ = lean_box(0);
        v___x_101_ = lean_apply_1(v_h__2_99_, v___x_100_);
        return v___x_101_;
    } else {
        let mut v_val_102_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_99_);
        v_val_102_ = lean_ctor_get(v_x_97_, 0);
        lean_inc(v_val_102_);
        lean_dec_ref_known(v_x_97_, 1);
        v___x_103_ = lean_apply_1(v_h__1_98_, v_val_102_);
        return v___x_103_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_foldlM__filterMap_match__1_splitter(
    mut v_00_u03b2_104_: *mut LeanObject,
    mut v_motive_105_: *mut LeanObject,
    mut v_x_106_: *mut LeanObject,
    mut v_h__1_107_: *mut LeanObject,
    mut v_h__2_108_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_106_) == 0 {
        let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_107_);
        v___x_109_ = lean_box(0);
        v___x_110_ = lean_apply_1(v_h__2_108_, v___x_109_);
        return v___x_110_;
    } else {
        let mut v_val_111_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_108_);
        v_val_111_ = lean_ctor_get(v_x_106_, 0);
        lean_inc(v_val_111_);
        lean_dec_ref_known(v_x_106_, 1);
        v___x_112_ = lean_apply_1(v_h__1_107_, v_val_111_);
        return v___x_112_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_foldlM__filterMap_match__1_splitter___redArg(
    mut v_x_113_: *mut LeanObject,
    mut v_h__1_114_: *mut LeanObject,
    mut v_h__2_115_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_113_) == 0 {
        let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_114_);
        v___x_116_ = lean_box(0);
        v___x_117_ = lean_apply_1(v_h__2_115_, v___x_116_);
        return v___x_117_;
    } else {
        let mut v_val_118_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_115_);
        v_val_118_ = lean_ctor_get(v_x_113_, 0);
        lean_inc(v_val_118_);
        lean_dec_ref_known(v_x_113_, 1);
        v___x_119_ = lean_apply_1(v_h__1_114_, v_val_118_);
        return v___x_119_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_foldlM__filterMap_match__1_splitter(
    mut v_00_u03b2_120_: *mut LeanObject,
    mut v_motive_121_: *mut LeanObject,
    mut v_x_122_: *mut LeanObject,
    mut v_h__1_123_: *mut LeanObject,
    mut v_h__2_124_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_122_) == 0 {
        let mut v___x_125_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_123_);
        v___x_125_ = lean_box(0);
        v___x_126_ = lean_apply_1(v_h__2_124_, v___x_125_);
        return v___x_126_;
    } else {
        let mut v_val_127_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_124_);
        v_val_127_ = lean_ctor_get(v_x_122_, 0);
        lean_inc(v_val_127_);
        lean_dec_ref_known(v_x_122_, 1);
        v___x_128_ = lean_apply_1(v_h__1_123_, v_val_127_);
        return v___x_128_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_129_: *mut LeanObject,
    mut v_h__1_130_: *mut LeanObject,
    mut v_h__2_131_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_129_) == 0 {
        let mut v_a_132_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_130_);
        v_a_132_ = lean_ctor_get(v_b_129_, 0);
        lean_inc(v_a_132_);
        lean_dec_ref_known(v_b_129_, 1);
        v___x_133_ = lean_apply_1(v_h__2_131_, v_a_132_);
        return v___x_133_;
    } else {
        let mut v_a_134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_131_);
        v_a_134_ = lean_ctor_get(v_b_129_, 0);
        lean_inc(v_a_134_);
        lean_dec_ref_known(v_b_129_, 1);
        v___x_135_ = lean_apply_1(v_h__1_130_, v_a_134_);
        return v___x_135_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_136_: *mut LeanObject,
    mut v_motive_137_: *mut LeanObject,
    mut v_b_138_: *mut LeanObject,
    mut v_h__1_139_: *mut LeanObject,
    mut v_h__2_140_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_138_) == 0 {
        let mut v_a_141_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_142_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_139_);
        v_a_141_ = lean_ctor_get(v_b_138_, 0);
        lean_inc(v_a_141_);
        lean_dec_ref_known(v_b_138_, 1);
        v___x_142_ = lean_apply_1(v_h__2_140_, v_a_141_);
        return v___x_142_;
    } else {
        let mut v_a_143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_144_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_140_);
        v_a_143_ = lean_ctor_get(v_b_138_, 0);
        lean_inc(v_a_143_);
        lean_dec_ref_known(v_b_138_, 1);
        v___x_144_ = lean_apply_1(v_h__1_139_, v_a_143_);
        return v___x_144_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_145_: *mut LeanObject,
    mut v_h__1_146_: *mut LeanObject,
    mut v_h__2_147_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_145_) == 0 {
        let mut v_a_148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_149_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_146_);
        v_a_148_ = lean_ctor_get(v_b_145_, 0);
        lean_inc(v_a_148_);
        lean_dec_ref_known(v_b_145_, 1);
        v___x_149_ = lean_apply_1(v_h__2_147_, v_a_148_);
        return v___x_149_;
    } else {
        let mut v_a_150_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_147_);
        v_a_150_ = lean_ctor_get(v_b_145_, 0);
        lean_inc(v_a_150_);
        lean_dec_ref_known(v_b_145_, 1);
        v___x_151_ = lean_apply_1(v_h__1_146_, v_a_150_);
        return v___x_151_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_152_: *mut LeanObject,
    mut v_motive_153_: *mut LeanObject,
    mut v_b_154_: *mut LeanObject,
    mut v_h__1_155_: *mut LeanObject,
    mut v_h__2_156_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_154_) == 0 {
        let mut v_a_157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_155_);
        v_a_157_ = lean_ctor_get(v_b_154_, 0);
        lean_inc(v_a_157_);
        lean_dec_ref_known(v_b_154_, 1);
        v___x_158_ = lean_apply_1(v_h__2_156_, v_a_157_);
        return v___x_158_;
    } else {
        let mut v_a_159_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_156_);
        v_a_159_ = lean_ctor_get(v_b_154_, 0);
        lean_inc(v_a_159_);
        lean_dec_ref_known(v_b_154_, 1);
        v___x_160_ = lean_apply_1(v_h__1_155_, v_a_159_);
        return v___x_160_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_161_: *mut LeanObject,
    mut v_h__1_162_: *mut LeanObject,
    mut v_h__2_163_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_161_) == 0 {
        let mut v___x_164_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_165_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_162_);
        v___x_164_ = lean_box(0);
        v___x_165_ = lean_apply_1(v_h__2_163_, v___x_164_);
        return v___x_165_;
    } else {
        let mut v_val_166_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_163_);
        v_val_166_ = lean_ctor_get(v_____do__lift_161_, 0);
        lean_inc(v_val_166_);
        lean_dec_ref_known(v_____do__lift_161_, 1);
        v___x_167_ = lean_apply_1(v_h__1_162_, v_val_166_);
        return v___x_167_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_filterMapM_match__1_splitter(
    mut v_00_u03b2_168_: *mut LeanObject,
    mut v_motive_169_: *mut LeanObject,
    mut v_____do__lift_170_: *mut LeanObject,
    mut v_h__1_171_: *mut LeanObject,
    mut v_h__2_172_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_170_) == 0 {
        let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_171_);
        v___x_173_ = lean_box(0);
        v___x_174_ = lean_apply_1(v_h__2_172_, v___x_173_);
        return v___x_174_;
    } else {
        let mut v_val_175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_172_);
        v_val_175_ = lean_ctor_get(v_____do__lift_170_, 0);
        lean_inc(v_val_175_);
        lean_dec_ref_known(v_____do__lift_170_, 1);
        v___x_176_ = lean_apply_1(v_h__1_171_, v_val_175_);
        return v___x_176_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_177_: *mut LeanObject,
    mut v_h__1_178_: *mut LeanObject,
    mut v_h__2_179_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_177_) == 0 {
        let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_179_);
        v___x_180_ = lean_box(0);
        v___x_181_ = lean_apply_1(v_h__1_178_, v___x_180_);
        return v___x_181_;
    } else {
        let mut v_val_182_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_178_);
        v_val_182_ = lean_ctor_get(v_____do__lift_177_, 0);
        lean_inc(v_val_182_);
        lean_dec_ref_known(v_____do__lift_177_, 1);
        v___x_183_ = lean_apply_1(v_h__2_179_, v_val_182_);
        return v___x_183_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_filterMapM_match__1_splitter(
    mut v_00_u03b2_184_: *mut LeanObject,
    mut v_motive_185_: *mut LeanObject,
    mut v_____do__lift_186_: *mut LeanObject,
    mut v_h__1_187_: *mut LeanObject,
    mut v_h__2_188_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_186_) == 0 {
        let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_188_);
        v___x_189_ = lean_box(0);
        v___x_190_ = lean_apply_1(v_h__1_187_, v___x_189_);
        return v___x_190_;
    } else {
        let mut v_val_191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_187_);
        v_val_191_ = lean_ctor_get(v_____do__lift_186_, 0);
        lean_inc(v_val_191_);
        lean_dec_ref_known(v_____do__lift_186_, 1);
        v___x_192_ = lean_apply_1(v_h__2_188_, v_val_191_);
        return v___x_192_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Monadic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Monadic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Monadic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_Monadic(builtin);
}
