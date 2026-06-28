// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.VarRename
// Imports: Init.Grind.AC Lean.Meta.Tactic.Grind.VarRename
use crate::r#gen::Init::Grind::AC::{initialize_Init_Grind_AC, runtime_initialize_Init_Grind_AC};
use crate::r#gen::Lean::Meta::Tactic::Grind::VarRename::{
    initialize_Lean_Meta_Tactic_Grind_VarRename, l_Lean_Meta_Grind_collectVar,
    runtime_initialize_Lean_Meta_Tactic_Grind_VarRename,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_get_size, lean_nat_dec_eq};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_Lean_Grind_AC_Seq_renameVars___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Grind_AC_Seq_renameVars___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_Seq_renameVars___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_Expr_renameVars___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Grind_AC_Expr_renameVars___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_Expr_renameVars___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg(
    mut v_a_128_: *mut LeanObject,
    mut v_x_129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_134_: u8 = 0;
    let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_129_) == 0 {
                    v___x_130_ = lean_box(0);
                    return v___x_130_;
                } else {
                    v_key_131_ = lean_ctor_get(v_x_129_, 0);
                    v_value_132_ = lean_ctor_get(v_x_129_, 1);
                    v_tail_133_ = lean_ctor_get(v_x_129_, 2);
                    v___x_134_ = lean_nat_dec_eq(v_key_131_, v_a_128_);
                    if v___x_134_ == 0 {
                        v_x_129_ = v_tail_133_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_132_);
                        v___x_136_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_136_, 0, v_value_132_);
                        return v___x_136_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg___boxed(
    mut v_a_137_: *mut LeanObject,
    mut v_x_138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_139_: *mut LeanObject = core::ptr::null_mut();
    v_res_139_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg(v_a_137_, v_x_138_);
    lean_dec(v_x_138_);
    lean_dec(v_a_137_);
    return v_res_139_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(
    mut v_m_140_: *mut LeanObject,
    mut v_a_141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_144_: u64 = 0;
    let mut v___x_145_: u64 = 0;
    let mut v___x_146_: u64 = 0;
    let mut v_fold_147_: u64 = 0;
    let mut v___x_148_: u64 = 0;
    let mut v___x_149_: u64 = 0;
    let mut v___x_150_: u64 = 0;
    let mut v___x_151_: usize = 0;
    let mut v___x_152_: usize = 0;
    let mut v___x_153_: usize = 0;
    let mut v___x_154_: usize = 0;
    let mut v___x_155_: usize = 0;
    let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_142_ = lean_ctor_get(v_m_140_, 1);
    v___x_143_ = lean_array_get_size(v_buckets_142_);
    v___x_144_ = lean_uint64_of_nat(v_a_141_);
    v___x_145_ = 32u64;
    v___x_146_ = lean_uint64_shift_right(v___x_144_, v___x_145_);
    v_fold_147_ = lean_uint64_xor(v___x_144_, v___x_146_);
    v___x_148_ = 16u64;
    v___x_149_ = lean_uint64_shift_right(v_fold_147_, v___x_148_);
    v___x_150_ = lean_uint64_xor(v_fold_147_, v___x_149_);
    v___x_151_ = lean_uint64_to_usize(v___x_150_);
    v___x_152_ = lean_usize_of_nat(v___x_143_);
    v___x_153_ = 1usize;
    v___x_154_ = lean_usize_sub(v___x_152_, v___x_153_);
    v___x_155_ = lean_usize_land(v___x_151_, v___x_154_);
    v___x_156_ = lean_array_uget_borrowed(v_buckets_142_, v___x_155_);
    v___x_157_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg(v_a_141_, v___x_156_);
    return v___x_157_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg___boxed(
    mut v_m_158_: *mut LeanObject,
    mut v_a_159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_160_: *mut LeanObject = core::ptr::null_mut();
    v_res_160_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_m_158_, v_a_159_);
    lean_dec(v_a_159_);
    lean_dec_ref(v_m_158_);
    return v_res_160_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_renameVars(
    mut v_s_163_: *mut LeanObject,
    mut v_f_164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_168_: u8 = 0;
    let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_175_: u8 = 0;
    let mut v_x_176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_180_: u8 = 0;
    let mut v___y_182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_s_163_) == 0 {
                    v_x_165_ = lean_ctor_get(v_s_163_, 0);
                    v_isSharedCheck_175_ = (!lean_is_exclusive(v_s_163_)) as u8;
                    if v_isSharedCheck_175_ == 0 {
                        v___x_167_ = v_s_163_;
                        v_isShared_168_ = v_isSharedCheck_175_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_x_165_);
                        lean_dec(v_s_163_);
                        v___x_167_ = lean_box(0);
                        v_isShared_168_ = v_isSharedCheck_175_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_x_176_ = lean_ctor_get(v_s_163_, 0);
                    v_s_177_ = lean_ctor_get(v_s_163_, 1);
                    v_isSharedCheck_190_ = (!lean_is_exclusive(v_s_163_)) as u8;
                    if v_isSharedCheck_190_ == 0 {
                        v___x_179_ = v_s_163_;
                        v_isShared_180_ = v_isSharedCheck_190_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_s_177_);
                        lean_inc(v_x_176_);
                        lean_dec(v_s_163_);
                        v___x_179_ = lean_box(0);
                        v_isShared_180_ = v_isSharedCheck_190_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_169_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_f_164_, v_x_165_);
                lean_dec(v_x_165_);
                if lean_obj_tag(v___x_169_) == 0 {
                    lean_del_object(v___x_167_);
                    v___x_170_ = l_Lean_Grind_AC_Seq_renameVars___closed__0;
                    return v___x_170_;
                } else {
                    v_val_171_ = lean_ctor_get(v___x_169_, 0);
                    lean_inc(v_val_171_);
                    lean_dec_ref_known(v___x_169_, 1);
                    if v_isShared_168_ == 0 {
                        lean_ctor_set(v___x_167_, 0, v_val_171_);
                        v___x_173_ = v___x_167_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_174_, 0, v_val_171_);
                        v___x_173_ = v_reuseFailAlloc_174_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_173_;
            }
            3 => {
                v___x_187_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_f_164_, v_x_176_);
                lean_dec(v_x_176_);
                if lean_obj_tag(v___x_187_) == 0 {
                    v___x_188_ = lean_unsigned_to_nat(0);
                    v___y_182_ = v___x_188_;
                    state = 4;
                    continue;
                } else {
                    v_val_189_ = lean_ctor_get(v___x_187_, 0);
                    lean_inc(v_val_189_);
                    lean_dec_ref_known(v___x_187_, 1);
                    v___y_182_ = v_val_189_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_183_ = l_Lean_Grind_AC_Seq_renameVars(v_s_177_, v_f_164_);
                if v_isShared_180_ == 0 {
                    lean_ctor_set(v___x_179_, 1, v___x_183_);
                    lean_ctor_set(v___x_179_, 0, v___y_182_);
                    v___x_185_ = v___x_179_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_186_, 0, v___y_182_);
                    lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_183_);
                    v___x_185_ = v_reuseFailAlloc_186_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_185_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_renameVars___boxed(
    mut v_s_191_: *mut LeanObject,
    mut v_f_192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_193_: *mut LeanObject = core::ptr::null_mut();
    v_res_193_ = l_Lean_Grind_AC_Seq_renameVars(v_s_191_, v_f_192_);
    lean_dec_ref(v_f_192_);
    return v_res_193_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0(
    mut v_00_u03b2_194_: *mut LeanObject,
    mut v_m_195_: *mut LeanObject,
    mut v_a_196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
    v___x_197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_m_195_, v_a_196_);
    return v___x_197_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___boxed(
    mut v_00_u03b2_198_: *mut LeanObject,
    mut v_m_199_: *mut LeanObject,
    mut v_a_200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_201_: *mut LeanObject = core::ptr::null_mut();
    v_res_201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0(v_00_u03b2_198_, v_m_199_, v_a_200_);
    lean_dec(v_a_200_);
    lean_dec_ref(v_m_199_);
    return v_res_201_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0(
    mut v_00_u03b2_202_: *mut LeanObject,
    mut v_a_203_: *mut LeanObject,
    mut v_x_204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
    v___x_205_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg(v_a_203_, v_x_204_);
    return v___x_205_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___boxed(
    mut v_00_u03b2_206_: *mut LeanObject,
    mut v_a_207_: *mut LeanObject,
    mut v_x_208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_209_: *mut LeanObject = core::ptr::null_mut();
    v_res_209_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0(v_00_u03b2_206_, v_a_207_, v_x_208_);
    lean_dec(v_x_208_);
    lean_dec(v_a_207_);
    return v_res_209_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_renameVars(
    mut v_e_212_: *mut LeanObject,
    mut v_f_213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_217_: u8 = 0;
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_224_: u8 = 0;
    let mut v_lhs_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_229_: u8 = 0;
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_212_) == 0 {
                    v_x_214_ = lean_ctor_get(v_e_212_, 0);
                    v_isSharedCheck_224_ = (!lean_is_exclusive(v_e_212_)) as u8;
                    if v_isSharedCheck_224_ == 0 {
                        v___x_216_ = v_e_212_;
                        v_isShared_217_ = v_isSharedCheck_224_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_x_214_);
                        lean_dec(v_e_212_);
                        v___x_216_ = lean_box(0);
                        v_isShared_217_ = v_isSharedCheck_224_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_lhs_225_ = lean_ctor_get(v_e_212_, 0);
                    v_rhs_226_ = lean_ctor_get(v_e_212_, 1);
                    v_isSharedCheck_235_ = (!lean_is_exclusive(v_e_212_)) as u8;
                    if v_isSharedCheck_235_ == 0 {
                        v___x_228_ = v_e_212_;
                        v_isShared_229_ = v_isSharedCheck_235_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_rhs_226_);
                        lean_inc(v_lhs_225_);
                        lean_dec(v_e_212_);
                        v___x_228_ = lean_box(0);
                        v_isShared_229_ = v_isSharedCheck_235_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_218_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_f_213_, v_x_214_);
                lean_dec(v_x_214_);
                if lean_obj_tag(v___x_218_) == 0 {
                    lean_del_object(v___x_216_);
                    v___x_219_ = l_Lean_Grind_AC_Expr_renameVars___closed__0;
                    return v___x_219_;
                } else {
                    v_val_220_ = lean_ctor_get(v___x_218_, 0);
                    lean_inc(v_val_220_);
                    lean_dec_ref_known(v___x_218_, 1);
                    if v_isShared_217_ == 0 {
                        lean_ctor_set(v___x_216_, 0, v_val_220_);
                        v___x_222_ = v___x_216_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_223_, 0, v_val_220_);
                        v___x_222_ = v_reuseFailAlloc_223_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_222_;
            }
            3 => {
                v___x_230_ = l_Lean_Grind_AC_Expr_renameVars(v_lhs_225_, v_f_213_);
                v___x_231_ = l_Lean_Grind_AC_Expr_renameVars(v_rhs_226_, v_f_213_);
                if v_isShared_229_ == 0 {
                    lean_ctor_set(v___x_228_, 1, v___x_231_);
                    lean_ctor_set(v___x_228_, 0, v___x_230_);
                    v___x_233_ = v___x_228_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_230_);
                    lean_ctor_set(v_reuseFailAlloc_234_, 1, v___x_231_);
                    v___x_233_ = v_reuseFailAlloc_234_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Expr_renameVars___boxed(
    mut v_e_236_: *mut LeanObject,
    mut v_f_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_238_: *mut LeanObject = core::ptr::null_mut();
    v_res_238_ = l_Lean_Grind_AC_Expr_renameVars(v_e_236_, v_f_237_);
    lean_dec_ref(v_f_237_);
    return v_res_238_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_collectVars(
    mut v_s_239_: *mut LeanObject,
    mut v_a_240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_s_239_) == 0 {
                    v_x_241_ = lean_ctor_get(v_s_239_, 0);
                    lean_inc(v_x_241_);
                    lean_dec_ref_known(v_s_239_, 1);
                    v___x_242_ = l_Lean_Meta_Grind_collectVar(v_x_241_, v_a_240_);
                    return v___x_242_;
                } else {
                    v_x_243_ = lean_ctor_get(v_s_239_, 0);
                    lean_inc(v_x_243_);
                    v_s_244_ = lean_ctor_get(v_s_239_, 1);
                    lean_inc_ref(v_s_244_);
                    lean_dec_ref_known(v_s_239_, 2);
                    v___x_245_ = l_Lean_Meta_Grind_collectVar(v_x_243_, v_a_240_);
                    v_s_239_ = v_s_244_;
                    v_a_240_ = v___x_245_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Expr_collectVars(
    mut v_e_247_: *mut LeanObject,
    mut v_a_248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_247_) == 0 {
                    v_x_249_ = lean_ctor_get(v_e_247_, 0);
                    lean_inc(v_x_249_);
                    lean_dec_ref_known(v_e_247_, 1);
                    v___x_250_ = l_Lean_Meta_Grind_collectVar(v_x_249_, v_a_248_);
                    return v___x_250_;
                } else {
                    v_lhs_251_ = lean_ctor_get(v_e_247_, 0);
                    lean_inc_ref(v_lhs_251_);
                    v_rhs_252_ = lean_ctor_get(v_e_247_, 1);
                    lean_inc_ref(v_rhs_252_);
                    lean_dec_ref_known(v_e_247_, 2);
                    v___x_253_ = l_Lean_Grind_AC_Expr_collectVars(v_lhs_251_, v_a_248_);
                    v_e_247_ = v_rhs_252_;
                    v_a_248_ = v___x_253_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin);
}
