// Lean compiler output
// Module: Init.Data.String.Lemmas.Splits
// Imports: Init.Data.String.Basic Init.Data.String.FindPos Init.Data.ByteArray.Lemmas Init.Data.String.Lemmas.Basic Init.Data.Nat.MinMax Init.Data.String.Lemmas.IsEmpty Init.Data.String.Lemmas.Order Init.Data.String.OrderInstances Init.Data.Nat.Order Init.Omega Init.Data.String.Lemmas.FindPos Init.Data.List.TakeDrop Init.Data.List.Nat.TakeDrop
use crate::r#gen::Init::Data::ByteArray::Lemmas::{
    initialize_Init_Data_ByteArray_Lemmas, runtime_initialize_Init_Data_ByteArray_Lemmas,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Nat::MinMax::{
    initialize_Init_Data_Nat_MinMax, runtime_initialize_Init_Data_Nat_MinMax,
};
use crate::r#gen::Init::Data::Nat::Order::{
    initialize_Init_Data_Nat_Order, runtime_initialize_Init_Data_Nat_Order,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::FindPos::{
    initialize_Init_Data_String_FindPos, runtime_initialize_Init_Data_String_FindPos,
};
use crate::r#gen::Init::Data::String::Lemmas::Basic::{
    initialize_Init_Data_String_Lemmas_Basic, runtime_initialize_Init_Data_String_Lemmas_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::FindPos::{
    initialize_Init_Data_String_Lemmas_FindPos, runtime_initialize_Init_Data_String_Lemmas_FindPos,
};
use crate::r#gen::Init::Data::String::Lemmas::IsEmpty::{
    initialize_Init_Data_String_Lemmas_IsEmpty, runtime_initialize_Init_Data_String_Lemmas_IsEmpty,
};
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_add, lean_string_utf8_byte_size};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_String_Slice_Pos_Splits_rotateRight___redArg(
    mut v_p_109_: *mut LeanObject,
    mut v_t_u2082_110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
    v___x_111_ = lean_string_utf8_byte_size(v_t_u2082_110_);
    v___x_112_ = lean_nat_add(v_p_109_, v___x_111_);
    return v___x_112_;
}
pub unsafe fn l_String_Slice_Pos_Splits_rotateRight___redArg___boxed(
    mut v_p_113_: *mut LeanObject,
    mut v_t_u2082_114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_115_: *mut LeanObject = core::ptr::null_mut();
    v_res_115_ = l_String_Slice_Pos_Splits_rotateRight___redArg(v_p_113_, v_t_u2082_114_);
    lean_dec_ref(v_t_u2082_114_);
    lean_dec(v_p_113_);
    return v_res_115_;
}
pub unsafe fn l_String_Slice_Pos_Splits_rotateRight(
    mut v_s_116_: *mut LeanObject,
    mut v_p_117_: *mut LeanObject,
    mut v_t_u2081_118_: *mut LeanObject,
    mut v_t_u2082_119_: *mut LeanObject,
    mut v_t_u2083_120_: *mut LeanObject,
    mut v_h_121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
    v___x_122_ = lean_string_utf8_byte_size(v_t_u2082_119_);
    v___x_123_ = lean_nat_add(v_p_117_, v___x_122_);
    return v___x_123_;
}
pub unsafe fn l_String_Slice_Pos_Splits_rotateRight___boxed(
    mut v_s_124_: *mut LeanObject,
    mut v_p_125_: *mut LeanObject,
    mut v_t_u2081_126_: *mut LeanObject,
    mut v_t_u2082_127_: *mut LeanObject,
    mut v_t_u2083_128_: *mut LeanObject,
    mut v_h_129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_130_: *mut LeanObject = core::ptr::null_mut();
    v_res_130_ = l_String_Slice_Pos_Splits_rotateRight(
        v_s_124_,
        v_p_125_,
        v_t_u2081_126_,
        v_t_u2082_127_,
        v_t_u2083_128_,
        v_h_129_,
    );
    lean_dec_ref(v_t_u2083_128_);
    lean_dec_ref(v_t_u2082_127_);
    lean_dec_ref(v_t_u2081_126_);
    lean_dec(v_p_125_);
    lean_dec_ref(v_s_124_);
    return v_res_130_;
}
pub unsafe fn l_String_Slice_Pos_Splits_rotateLeft___redArg(
    mut v_t_u2081_131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
    v___x_132_ = lean_string_utf8_byte_size(v_t_u2081_131_);
    return v___x_132_;
}
pub unsafe fn l_String_Slice_Pos_Splits_rotateLeft___redArg___boxed(
    mut v_t_u2081_133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_134_: *mut LeanObject = core::ptr::null_mut();
    v_res_134_ = l_String_Slice_Pos_Splits_rotateLeft___redArg(v_t_u2081_133_);
    lean_dec_ref(v_t_u2081_133_);
    return v_res_134_;
}
pub unsafe fn l_String_Slice_Pos_Splits_rotateLeft(
    mut v_s_135_: *mut LeanObject,
    mut v_p_136_: *mut LeanObject,
    mut v_t_u2081_137_: *mut LeanObject,
    mut v_t_u2082_138_: *mut LeanObject,
    mut v_t_u2083_139_: *mut LeanObject,
    mut v_h_140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
    v___x_141_ = lean_string_utf8_byte_size(v_t_u2081_137_);
    return v___x_141_;
}
pub unsafe fn l_String_Slice_Pos_Splits_rotateLeft___boxed(
    mut v_s_142_: *mut LeanObject,
    mut v_p_143_: *mut LeanObject,
    mut v_t_u2081_144_: *mut LeanObject,
    mut v_t_u2082_145_: *mut LeanObject,
    mut v_t_u2083_146_: *mut LeanObject,
    mut v_h_147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_148_: *mut LeanObject = core::ptr::null_mut();
    v_res_148_ = l_String_Slice_Pos_Splits_rotateLeft(
        v_s_142_,
        v_p_143_,
        v_t_u2081_144_,
        v_t_u2082_145_,
        v_t_u2083_146_,
        v_h_147_,
    );
    lean_dec_ref(v_t_u2083_146_);
    lean_dec_ref(v_t_u2082_145_);
    lean_dec_ref(v_t_u2081_144_);
    lean_dec(v_p_143_);
    lean_dec_ref(v_s_142_);
    return v_res_148_;
}
pub unsafe fn l_String_Pos_Splits_rotateRight___redArg(
    mut v_p_149_: *mut LeanObject,
    mut v_t_u2082_150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut LeanObject = core::ptr::null_mut();
    v___x_151_ = lean_string_utf8_byte_size(v_t_u2082_150_);
    v___x_152_ = lean_nat_add(v_p_149_, v___x_151_);
    return v___x_152_;
}
pub unsafe fn l_String_Pos_Splits_rotateRight___redArg___boxed(
    mut v_p_153_: *mut LeanObject,
    mut v_t_u2082_154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_155_: *mut LeanObject = core::ptr::null_mut();
    v_res_155_ = l_String_Pos_Splits_rotateRight___redArg(v_p_153_, v_t_u2082_154_);
    lean_dec_ref(v_t_u2082_154_);
    lean_dec(v_p_153_);
    return v_res_155_;
}
pub unsafe fn l_String_Pos_Splits_rotateRight(
    mut v_s_156_: *mut LeanObject,
    mut v_p_157_: *mut LeanObject,
    mut v_t_u2081_158_: *mut LeanObject,
    mut v_t_u2082_159_: *mut LeanObject,
    mut v_t_u2083_160_: *mut LeanObject,
    mut v_h_161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
    v___x_162_ = lean_string_utf8_byte_size(v_t_u2082_159_);
    v___x_163_ = lean_nat_add(v_p_157_, v___x_162_);
    return v___x_163_;
}
pub unsafe fn l_String_Pos_Splits_rotateRight___boxed(
    mut v_s_164_: *mut LeanObject,
    mut v_p_165_: *mut LeanObject,
    mut v_t_u2081_166_: *mut LeanObject,
    mut v_t_u2082_167_: *mut LeanObject,
    mut v_t_u2083_168_: *mut LeanObject,
    mut v_h_169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_170_: *mut LeanObject = core::ptr::null_mut();
    v_res_170_ = l_String_Pos_Splits_rotateRight(
        v_s_164_,
        v_p_165_,
        v_t_u2081_166_,
        v_t_u2082_167_,
        v_t_u2083_168_,
        v_h_169_,
    );
    lean_dec_ref(v_t_u2083_168_);
    lean_dec_ref(v_t_u2082_167_);
    lean_dec_ref(v_t_u2081_166_);
    lean_dec(v_p_165_);
    lean_dec_ref(v_s_164_);
    return v_res_170_;
}
pub unsafe fn l_String_Pos_Splits_rotateLeft___redArg(
    mut v_t_u2081_171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
    v___x_172_ = lean_string_utf8_byte_size(v_t_u2081_171_);
    return v___x_172_;
}
pub unsafe fn l_String_Pos_Splits_rotateLeft___redArg___boxed(
    mut v_t_u2081_173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_174_: *mut LeanObject = core::ptr::null_mut();
    v_res_174_ = l_String_Pos_Splits_rotateLeft___redArg(v_t_u2081_173_);
    lean_dec_ref(v_t_u2081_173_);
    return v_res_174_;
}
pub unsafe fn l_String_Pos_Splits_rotateLeft(
    mut v_s_175_: *mut LeanObject,
    mut v_p_176_: *mut LeanObject,
    mut v_t_u2081_177_: *mut LeanObject,
    mut v_t_u2082_178_: *mut LeanObject,
    mut v_t_u2083_179_: *mut LeanObject,
    mut v_h_180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
    v___x_181_ = lean_string_utf8_byte_size(v_t_u2081_177_);
    return v___x_181_;
}
pub unsafe fn l_String_Pos_Splits_rotateLeft___boxed(
    mut v_s_182_: *mut LeanObject,
    mut v_p_183_: *mut LeanObject,
    mut v_t_u2081_184_: *mut LeanObject,
    mut v_t_u2082_185_: *mut LeanObject,
    mut v_t_u2083_186_: *mut LeanObject,
    mut v_h_187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_188_: *mut LeanObject = core::ptr::null_mut();
    v_res_188_ = l_String_Pos_Splits_rotateLeft(
        v_s_182_,
        v_p_183_,
        v_t_u2081_184_,
        v_t_u2082_185_,
        v_t_u2083_186_,
        v_h_187_,
    );
    lean_dec_ref(v_t_u2083_186_);
    lean_dec_ref(v_t_u2082_185_);
    lean_dec_ref(v_t_u2081_184_);
    lean_dec(v_p_183_);
    lean_dec_ref(v_s_182_);
    return v_res_188_;
}
pub unsafe fn l_String_Slice_Pos_ofEqAppend___redArg(
    mut v_t_u2081_189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    v___x_190_ = lean_string_utf8_byte_size(v_t_u2081_189_);
    return v___x_190_;
}
pub unsafe fn l_String_Slice_Pos_ofEqAppend___redArg___boxed(
    mut v_t_u2081_191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_192_: *mut LeanObject = core::ptr::null_mut();
    v_res_192_ = l_String_Slice_Pos_ofEqAppend___redArg(v_t_u2081_191_);
    lean_dec_ref(v_t_u2081_191_);
    return v_res_192_;
}
pub unsafe fn l_String_Slice_Pos_ofEqAppend(
    mut v_s_193_: *mut LeanObject,
    mut v_t_u2081_194_: *mut LeanObject,
    mut v_t_u2082_195_: *mut LeanObject,
    mut v_h_196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
    v___x_197_ = lean_string_utf8_byte_size(v_t_u2081_194_);
    return v___x_197_;
}
pub unsafe fn l_String_Slice_Pos_ofEqAppend___boxed(
    mut v_s_198_: *mut LeanObject,
    mut v_t_u2081_199_: *mut LeanObject,
    mut v_t_u2082_200_: *mut LeanObject,
    mut v_h_201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_202_: *mut LeanObject = core::ptr::null_mut();
    v_res_202_ = l_String_Slice_Pos_ofEqAppend(v_s_198_, v_t_u2081_199_, v_t_u2082_200_, v_h_201_);
    lean_dec_ref(v_t_u2082_200_);
    lean_dec_ref(v_t_u2081_199_);
    lean_dec_ref(v_s_198_);
    return v_res_202_;
}
pub unsafe fn l_String_Pos_ofEqAppend___redArg(
    mut v_t_u2081_203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    v___x_204_ = lean_string_utf8_byte_size(v_t_u2081_203_);
    return v___x_204_;
}
pub unsafe fn l_String_Pos_ofEqAppend___redArg___boxed(
    mut v_t_u2081_205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_206_: *mut LeanObject = core::ptr::null_mut();
    v_res_206_ = l_String_Pos_ofEqAppend___redArg(v_t_u2081_205_);
    lean_dec_ref(v_t_u2081_205_);
    return v_res_206_;
}
pub unsafe fn l_String_Pos_ofEqAppend(
    mut v_s_207_: *mut LeanObject,
    mut v_t_u2081_208_: *mut LeanObject,
    mut v_t_u2082_209_: *mut LeanObject,
    mut v_h_210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_211_: *mut LeanObject = core::ptr::null_mut();
    v___x_211_ = lean_string_utf8_byte_size(v_t_u2081_208_);
    return v___x_211_;
}
pub unsafe fn l_String_Pos_ofEqAppend___boxed(
    mut v_s_212_: *mut LeanObject,
    mut v_t_u2081_213_: *mut LeanObject,
    mut v_t_u2082_214_: *mut LeanObject,
    mut v_h_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_216_: *mut LeanObject = core::ptr::null_mut();
    v_res_216_ = l_String_Pos_ofEqAppend(v_s_212_, v_t_u2081_213_, v_t_u2082_214_, v_h_215_);
    lean_dec_ref(v_t_u2082_214_);
    lean_dec_ref(v_t_u2081_213_);
    lean_dec_ref(v_s_212_);
    return v_res_216_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Splits(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Splits(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Lemmas_Splits(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ByteArray_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_MinMax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Splits(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Splits(builtin);
}
