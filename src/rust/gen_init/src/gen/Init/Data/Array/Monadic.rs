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
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_foldlM__filterMap_match__1_splitter___redArg(
    mut v_x_97_: *mut leanh::LeanObject,
    mut v_h__1_98_: *mut leanh::LeanObject,
    mut v_h__2_99_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_97_) == 0 {
        let mut v___x_100_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_101_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_98_);
        v___x_100_ = leanh::lean_box(0);
        v___x_101_ = leanh::lean_apply_1(v_h__2_99_, v___x_100_);
        return v___x_101_;
    } else {
        let mut v_val_102_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_99_);
        v_val_102_ = leanh::lean_ctor_get(v_x_97_, 0);
        leanh::lean_inc(v_val_102_);
        leanh::lean_dec_ref_known(v_x_97_, 1);
        v___x_103_ = leanh::lean_apply_1(v_h__1_98_, v_val_102_);
        return v___x_103_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_foldlM__filterMap_match__1_splitter(
    mut v_00_u03b2_104_: *mut leanh::LeanObject,
    mut v_motive_105_: *mut leanh::LeanObject,
    mut v_x_106_: *mut leanh::LeanObject,
    mut v_h__1_107_: *mut leanh::LeanObject,
    mut v_h__2_108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_106_) == 0 {
        let mut v___x_109_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_107_);
        v___x_109_ = leanh::lean_box(0);
        v___x_110_ = leanh::lean_apply_1(v_h__2_108_, v___x_109_);
        return v___x_110_;
    } else {
        let mut v_val_111_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_108_);
        v_val_111_ = leanh::lean_ctor_get(v_x_106_, 0);
        leanh::lean_inc(v_val_111_);
        leanh::lean_dec_ref_known(v_x_106_, 1);
        v___x_112_ = leanh::lean_apply_1(v_h__1_107_, v_val_111_);
        return v___x_112_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_foldlM__filterMap_match__1_splitter___redArg(
    mut v_x_113_: *mut leanh::LeanObject,
    mut v_h__1_114_: *mut leanh::LeanObject,
    mut v_h__2_115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_113_) == 0 {
        let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_117_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_114_);
        v___x_116_ = leanh::lean_box(0);
        v___x_117_ = leanh::lean_apply_1(v_h__2_115_, v___x_116_);
        return v___x_117_;
    } else {
        let mut v_val_118_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_115_);
        v_val_118_ = leanh::lean_ctor_get(v_x_113_, 0);
        leanh::lean_inc(v_val_118_);
        leanh::lean_dec_ref_known(v_x_113_, 1);
        v___x_119_ = leanh::lean_apply_1(v_h__1_114_, v_val_118_);
        return v___x_119_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_foldlM__filterMap_match__1_splitter(
    mut v_00_u03b2_120_: *mut leanh::LeanObject,
    mut v_motive_121_: *mut leanh::LeanObject,
    mut v_x_122_: *mut leanh::LeanObject,
    mut v_h__1_123_: *mut leanh::LeanObject,
    mut v_h__2_124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_122_) == 0 {
        let mut v___x_125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_123_);
        v___x_125_ = leanh::lean_box(0);
        v___x_126_ = leanh::lean_apply_1(v_h__2_124_, v___x_125_);
        return v___x_126_;
    } else {
        let mut v_val_127_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_128_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_124_);
        v_val_127_ = leanh::lean_ctor_get(v_x_122_, 0);
        leanh::lean_inc(v_val_127_);
        leanh::lean_dec_ref_known(v_x_122_, 1);
        v___x_128_ = leanh::lean_apply_1(v_h__1_123_, v_val_127_);
        return v___x_128_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_129_: *mut leanh::LeanObject,
    mut v_h__1_130_: *mut leanh::LeanObject,
    mut v_h__2_131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_129_) == 0 {
        let mut v_a_132_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_130_);
        v_a_132_ = leanh::lean_ctor_get(v_b_129_, 0);
        leanh::lean_inc(v_a_132_);
        leanh::lean_dec_ref_known(v_b_129_, 1);
        v___x_133_ = leanh::lean_apply_1(v_h__2_131_, v_a_132_);
        return v___x_133_;
    } else {
        let mut v_a_134_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_131_);
        v_a_134_ = leanh::lean_ctor_get(v_b_129_, 0);
        leanh::lean_inc(v_a_134_);
        leanh::lean_dec_ref_known(v_b_129_, 1);
        v___x_135_ = leanh::lean_apply_1(v_h__1_130_, v_a_134_);
        return v___x_135_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_136_: *mut leanh::LeanObject,
    mut v_motive_137_: *mut leanh::LeanObject,
    mut v_b_138_: *mut leanh::LeanObject,
    mut v_h__1_139_: *mut leanh::LeanObject,
    mut v_h__2_140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_138_) == 0 {
        let mut v_a_141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_142_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_139_);
        v_a_141_ = leanh::lean_ctor_get(v_b_138_, 0);
        leanh::lean_inc(v_a_141_);
        leanh::lean_dec_ref_known(v_b_138_, 1);
        v___x_142_ = leanh::lean_apply_1(v_h__2_140_, v_a_141_);
        return v___x_142_;
    } else {
        let mut v_a_143_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_144_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_140_);
        v_a_143_ = leanh::lean_ctor_get(v_b_138_, 0);
        leanh::lean_inc(v_a_143_);
        leanh::lean_dec_ref_known(v_b_138_, 1);
        v___x_144_ = leanh::lean_apply_1(v_h__1_139_, v_a_143_);
        return v___x_144_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_145_: *mut leanh::LeanObject,
    mut v_h__1_146_: *mut leanh::LeanObject,
    mut v_h__2_147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_145_) == 0 {
        let mut v_a_148_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_146_);
        v_a_148_ = leanh::lean_ctor_get(v_b_145_, 0);
        leanh::lean_inc(v_a_148_);
        leanh::lean_dec_ref_known(v_b_145_, 1);
        v___x_149_ = leanh::lean_apply_1(v_h__2_147_, v_a_148_);
        return v___x_149_;
    } else {
        let mut v_a_150_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_147_);
        v_a_150_ = leanh::lean_ctor_get(v_b_145_, 0);
        leanh::lean_inc(v_a_150_);
        leanh::lean_dec_ref_known(v_b_145_, 1);
        v___x_151_ = leanh::lean_apply_1(v_h__1_146_, v_a_150_);
        return v___x_151_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_152_: *mut leanh::LeanObject,
    mut v_motive_153_: *mut leanh::LeanObject,
    mut v_b_154_: *mut leanh::LeanObject,
    mut v_h__1_155_: *mut leanh::LeanObject,
    mut v_h__2_156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_154_) == 0 {
        let mut v_a_157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_155_);
        v_a_157_ = leanh::lean_ctor_get(v_b_154_, 0);
        leanh::lean_inc(v_a_157_);
        leanh::lean_dec_ref_known(v_b_154_, 1);
        v___x_158_ = leanh::lean_apply_1(v_h__2_156_, v_a_157_);
        return v___x_158_;
    } else {
        let mut v_a_159_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_156_);
        v_a_159_ = leanh::lean_ctor_get(v_b_154_, 0);
        leanh::lean_inc(v_a_159_);
        leanh::lean_dec_ref_known(v_b_154_, 1);
        v___x_160_ = leanh::lean_apply_1(v_h__1_155_, v_a_159_);
        return v___x_160_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_161_: *mut leanh::LeanObject,
    mut v_h__1_162_: *mut leanh::LeanObject,
    mut v_h__2_163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_161_) == 0 {
        let mut v___x_164_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_165_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_162_);
        v___x_164_ = leanh::lean_box(0);
        v___x_165_ = leanh::lean_apply_1(v_h__2_163_, v___x_164_);
        return v___x_165_;
    } else {
        let mut v_val_166_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_167_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_163_);
        v_val_166_ = leanh::lean_ctor_get(v_____do__lift_161_, 0);
        leanh::lean_inc(v_val_166_);
        leanh::lean_dec_ref_known(v_____do__lift_161_, 1);
        v___x_167_ = leanh::lean_apply_1(v_h__1_162_, v_val_166_);
        return v___x_167_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_filterMapM_match__1_splitter(
    mut v_00_u03b2_168_: *mut leanh::LeanObject,
    mut v_motive_169_: *mut leanh::LeanObject,
    mut v_____do__lift_170_: *mut leanh::LeanObject,
    mut v_h__1_171_: *mut leanh::LeanObject,
    mut v_h__2_172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_170_) == 0 {
        let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_171_);
        v___x_173_ = leanh::lean_box(0);
        v___x_174_ = leanh::lean_apply_1(v_h__2_172_, v___x_173_);
        return v___x_174_;
    } else {
        let mut v_val_175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_172_);
        v_val_175_ = leanh::lean_ctor_get(v_____do__lift_170_, 0);
        leanh::lean_inc(v_val_175_);
        leanh::lean_dec_ref_known(v_____do__lift_170_, 1);
        v___x_176_ = leanh::lean_apply_1(v_h__1_171_, v_val_175_);
        return v___x_176_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_177_: *mut leanh::LeanObject,
    mut v_h__1_178_: *mut leanh::LeanObject,
    mut v_h__2_179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_177_) == 0 {
        let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_179_);
        v___x_180_ = leanh::lean_box(0);
        v___x_181_ = leanh::lean_apply_1(v_h__1_178_, v___x_180_);
        return v___x_181_;
    } else {
        let mut v_val_182_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_178_);
        v_val_182_ = leanh::lean_ctor_get(v_____do__lift_177_, 0);
        leanh::lean_inc(v_val_182_);
        leanh::lean_dec_ref_known(v_____do__lift_177_, 1);
        v___x_183_ = leanh::lean_apply_1(v_h__2_179_, v_val_182_);
        return v___x_183_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_filterMapM_match__1_splitter(
    mut v_00_u03b2_184_: *mut leanh::LeanObject,
    mut v_motive_185_: *mut leanh::LeanObject,
    mut v_____do__lift_186_: *mut leanh::LeanObject,
    mut v_h__1_187_: *mut leanh::LeanObject,
    mut v_h__2_188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_186_) == 0 {
        let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_188_);
        v___x_189_ = leanh::lean_box(0);
        v___x_190_ = leanh::lean_apply_1(v_h__1_187_, v___x_189_);
        return v___x_190_;
    } else {
        let mut v_val_191_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_187_);
        v_val_191_ = leanh::lean_ctor_get(v_____do__lift_186_, 0);
        leanh::lean_inc(v_val_191_);
        leanh::lean_dec_ref_known(v_____do__lift_186_, 1);
        v___x_192_ = leanh::lean_apply_1(v_h__2_188_, v_val_191_);
        return v___x_192_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Monadic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Monadic(
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
pub unsafe fn initialize_Init_Data_Array_Monadic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Monadic(builtin);
}