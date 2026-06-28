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
    mut v_x_97_: *mut crate::leanh::LeanObject,
    mut v_h__1_98_: *mut crate::leanh::LeanObject,
    mut v_h__2_99_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_97_) == 0 {
        let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_98_);
        v___x_100_ = crate::leanh::lean_box(0);
        v___x_101_ = crate::leanh::lean_apply_1(v_h__2_99_, v___x_100_);
        return v___x_101_;
    } else {
        let mut v_val_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_99_);
        v_val_102_ = crate::leanh::lean_ctor_get(v_x_97_, 0);
        crate::leanh::lean_inc(v_val_102_);
        crate::leanh::lean_dec_ref_known(v_x_97_, 1);
        v___x_103_ = crate::leanh::lean_apply_1(v_h__1_98_, v_val_102_);
        return v___x_103_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_foldlM__filterMap_match__1_splitter(
    mut v_00_u03b2_104_: *mut crate::leanh::LeanObject,
    mut v_motive_105_: *mut crate::leanh::LeanObject,
    mut v_x_106_: *mut crate::leanh::LeanObject,
    mut v_h__1_107_: *mut crate::leanh::LeanObject,
    mut v_h__2_108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_106_) == 0 {
        let mut v___x_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_107_);
        v___x_109_ = crate::leanh::lean_box(0);
        v___x_110_ = crate::leanh::lean_apply_1(v_h__2_108_, v___x_109_);
        return v___x_110_;
    } else {
        let mut v_val_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_108_);
        v_val_111_ = crate::leanh::lean_ctor_get(v_x_106_, 0);
        crate::leanh::lean_inc(v_val_111_);
        crate::leanh::lean_dec_ref_known(v_x_106_, 1);
        v___x_112_ = crate::leanh::lean_apply_1(v_h__1_107_, v_val_111_);
        return v___x_112_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_foldlM__filterMap_match__1_splitter___redArg(
    mut v_x_113_: *mut crate::leanh::LeanObject,
    mut v_h__1_114_: *mut crate::leanh::LeanObject,
    mut v_h__2_115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_113_) == 0 {
        let mut v___x_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_114_);
        v___x_116_ = crate::leanh::lean_box(0);
        v___x_117_ = crate::leanh::lean_apply_1(v_h__2_115_, v___x_116_);
        return v___x_117_;
    } else {
        let mut v_val_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_115_);
        v_val_118_ = crate::leanh::lean_ctor_get(v_x_113_, 0);
        crate::leanh::lean_inc(v_val_118_);
        crate::leanh::lean_dec_ref_known(v_x_113_, 1);
        v___x_119_ = crate::leanh::lean_apply_1(v_h__1_114_, v_val_118_);
        return v___x_119_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_foldlM__filterMap_match__1_splitter(
    mut v_00_u03b2_120_: *mut crate::leanh::LeanObject,
    mut v_motive_121_: *mut crate::leanh::LeanObject,
    mut v_x_122_: *mut crate::leanh::LeanObject,
    mut v_h__1_123_: *mut crate::leanh::LeanObject,
    mut v_h__2_124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_122_) == 0 {
        let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_123_);
        v___x_125_ = crate::leanh::lean_box(0);
        v___x_126_ = crate::leanh::lean_apply_1(v_h__2_124_, v___x_125_);
        return v___x_126_;
    } else {
        let mut v_val_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_124_);
        v_val_127_ = crate::leanh::lean_ctor_get(v_x_122_, 0);
        crate::leanh::lean_inc(v_val_127_);
        crate::leanh::lean_dec_ref_known(v_x_122_, 1);
        v___x_128_ = crate::leanh::lean_apply_1(v_h__1_123_, v_val_127_);
        return v___x_128_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_129_: *mut crate::leanh::LeanObject,
    mut v_h__1_130_: *mut crate::leanh::LeanObject,
    mut v_h__2_131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_129_) == 0 {
        let mut v_a_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_130_);
        v_a_132_ = crate::leanh::lean_ctor_get(v_b_129_, 0);
        crate::leanh::lean_inc(v_a_132_);
        crate::leanh::lean_dec_ref_known(v_b_129_, 1);
        v___x_133_ = crate::leanh::lean_apply_1(v_h__2_131_, v_a_132_);
        return v___x_133_;
    } else {
        let mut v_a_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_131_);
        v_a_134_ = crate::leanh::lean_ctor_get(v_b_129_, 0);
        crate::leanh::lean_inc(v_a_134_);
        crate::leanh::lean_dec_ref_known(v_b_129_, 1);
        v___x_135_ = crate::leanh::lean_apply_1(v_h__1_130_, v_a_134_);
        return v___x_135_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_136_: *mut crate::leanh::LeanObject,
    mut v_motive_137_: *mut crate::leanh::LeanObject,
    mut v_b_138_: *mut crate::leanh::LeanObject,
    mut v_h__1_139_: *mut crate::leanh::LeanObject,
    mut v_h__2_140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_138_) == 0 {
        let mut v_a_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_139_);
        v_a_141_ = crate::leanh::lean_ctor_get(v_b_138_, 0);
        crate::leanh::lean_inc(v_a_141_);
        crate::leanh::lean_dec_ref_known(v_b_138_, 1);
        v___x_142_ = crate::leanh::lean_apply_1(v_h__2_140_, v_a_141_);
        return v___x_142_;
    } else {
        let mut v_a_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_140_);
        v_a_143_ = crate::leanh::lean_ctor_get(v_b_138_, 0);
        crate::leanh::lean_inc(v_a_143_);
        crate::leanh::lean_dec_ref_known(v_b_138_, 1);
        v___x_144_ = crate::leanh::lean_apply_1(v_h__1_139_, v_a_143_);
        return v___x_144_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_145_: *mut crate::leanh::LeanObject,
    mut v_h__1_146_: *mut crate::leanh::LeanObject,
    mut v_h__2_147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_145_) == 0 {
        let mut v_a_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_146_);
        v_a_148_ = crate::leanh::lean_ctor_get(v_b_145_, 0);
        crate::leanh::lean_inc(v_a_148_);
        crate::leanh::lean_dec_ref_known(v_b_145_, 1);
        v___x_149_ = crate::leanh::lean_apply_1(v_h__2_147_, v_a_148_);
        return v___x_149_;
    } else {
        let mut v_a_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_147_);
        v_a_150_ = crate::leanh::lean_ctor_get(v_b_145_, 0);
        crate::leanh::lean_inc(v_a_150_);
        crate::leanh::lean_dec_ref_known(v_b_145_, 1);
        v___x_151_ = crate::leanh::lean_apply_1(v_h__1_146_, v_a_150_);
        return v___x_151_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_152_: *mut crate::leanh::LeanObject,
    mut v_motive_153_: *mut crate::leanh::LeanObject,
    mut v_b_154_: *mut crate::leanh::LeanObject,
    mut v_h__1_155_: *mut crate::leanh::LeanObject,
    mut v_h__2_156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_154_) == 0 {
        let mut v_a_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_155_);
        v_a_157_ = crate::leanh::lean_ctor_get(v_b_154_, 0);
        crate::leanh::lean_inc(v_a_157_);
        crate::leanh::lean_dec_ref_known(v_b_154_, 1);
        v___x_158_ = crate::leanh::lean_apply_1(v_h__2_156_, v_a_157_);
        return v___x_158_;
    } else {
        let mut v_a_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_156_);
        v_a_159_ = crate::leanh::lean_ctor_get(v_b_154_, 0);
        crate::leanh::lean_inc(v_a_159_);
        crate::leanh::lean_dec_ref_known(v_b_154_, 1);
        v___x_160_ = crate::leanh::lean_apply_1(v_h__1_155_, v_a_159_);
        return v___x_160_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_161_: *mut crate::leanh::LeanObject,
    mut v_h__1_162_: *mut crate::leanh::LeanObject,
    mut v_h__2_163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_161_) == 0 {
        let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_162_);
        v___x_164_ = crate::leanh::lean_box(0);
        v___x_165_ = crate::leanh::lean_apply_1(v_h__2_163_, v___x_164_);
        return v___x_165_;
    } else {
        let mut v_val_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_163_);
        v_val_166_ = crate::leanh::lean_ctor_get(v_____do__lift_161_, 0);
        crate::leanh::lean_inc(v_val_166_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_161_, 1);
        v___x_167_ = crate::leanh::lean_apply_1(v_h__1_162_, v_val_166_);
        return v___x_167_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__Array_filterMapM_match__1_splitter(
    mut v_00_u03b2_168_: *mut crate::leanh::LeanObject,
    mut v_motive_169_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_170_: *mut crate::leanh::LeanObject,
    mut v_h__1_171_: *mut crate::leanh::LeanObject,
    mut v_h__2_172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_170_) == 0 {
        let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_171_);
        v___x_173_ = crate::leanh::lean_box(0);
        v___x_174_ = crate::leanh::lean_apply_1(v_h__2_172_, v___x_173_);
        return v___x_174_;
    } else {
        let mut v_val_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_172_);
        v_val_175_ = crate::leanh::lean_ctor_get(v_____do__lift_170_, 0);
        crate::leanh::lean_inc(v_val_175_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_170_, 1);
        v___x_176_ = crate::leanh::lean_apply_1(v_h__1_171_, v_val_175_);
        return v___x_176_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_177_: *mut crate::leanh::LeanObject,
    mut v_h__1_178_: *mut crate::leanh::LeanObject,
    mut v_h__2_179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_177_) == 0 {
        let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_179_);
        v___x_180_ = crate::leanh::lean_box(0);
        v___x_181_ = crate::leanh::lean_apply_1(v_h__1_178_, v___x_180_);
        return v___x_181_;
    } else {
        let mut v_val_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_178_);
        v_val_182_ = crate::leanh::lean_ctor_get(v_____do__lift_177_, 0);
        crate::leanh::lean_inc(v_val_182_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_177_, 1);
        v___x_183_ = crate::leanh::lean_apply_1(v_h__2_179_, v_val_182_);
        return v___x_183_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Monadic_0__List_filterMapM_match__1_splitter(
    mut v_00_u03b2_184_: *mut crate::leanh::LeanObject,
    mut v_motive_185_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_186_: *mut crate::leanh::LeanObject,
    mut v_h__1_187_: *mut crate::leanh::LeanObject,
    mut v_h__2_188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_186_) == 0 {
        let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_188_);
        v___x_189_ = crate::leanh::lean_box(0);
        v___x_190_ = crate::leanh::lean_apply_1(v_h__1_187_, v___x_189_);
        return v___x_190_;
    } else {
        let mut v_val_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_187_);
        v_val_191_ = crate::leanh::lean_ctor_get(v_____do__lift_186_, 0);
        crate::leanh::lean_inc(v_val_191_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_186_, 1);
        v___x_192_ = crate::leanh::lean_apply_1(v_h__2_188_, v_val_191_);
        return v___x_192_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Monadic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Monadic(
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
pub unsafe fn initialize_Init_Data_Array_Monadic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Monadic(builtin);
}
