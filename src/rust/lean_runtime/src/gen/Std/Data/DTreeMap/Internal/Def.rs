// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Def
// Imports: Init.Data.SInt.Basic
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::SInt::Basic::{
    initialize_Init_Data_SInt_Basic, runtime_initialize_Init_Data_SInt_Basic,
};
use crate::lean_imports_rs::Init::Prelude::lean_nat_add;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_5, lean_box, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_mark_persistent, lean_obj_tag, lean_unsigned_to_nat,
};
pub static mut l_Std_DTreeMap_Internal_delta: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_DTreeMap_Internal_ratio: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ctorIdx___redArg(
    mut v_x_120_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_120_) == 0 {
        let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
        v___x_121_ = lean_unsigned_to_nat(0);
        return v___x_121_;
    } else {
        let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
        v___x_122_ = lean_unsigned_to_nat(1);
        return v___x_122_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ctorIdx___redArg___boxed(
    mut v_x_123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_124_: *mut LeanObject = core::ptr::null_mut();
    v_res_124_ = l_Std_DTreeMap_Internal_Impl_ctorIdx___redArg(v_x_123_);
    lean_dec(v_x_123_);
    return v_res_124_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ctorIdx(
    mut v_00_u03b1_125_: *mut LeanObject,
    mut v_00_u03b2_126_: *mut LeanObject,
    mut v_x_127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
    v___x_128_ = l_Std_DTreeMap_Internal_Impl_ctorIdx___redArg(v_x_127_);
    return v___x_128_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ctorIdx___boxed(
    mut v_00_u03b1_129_: *mut LeanObject,
    mut v_00_u03b2_130_: *mut LeanObject,
    mut v_x_131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_132_: *mut LeanObject = core::ptr::null_mut();
    v_res_132_ = l_Std_DTreeMap_Internal_Impl_ctorIdx(v_00_u03b1_129_, v_00_u03b2_130_, v_x_131_);
    lean_dec(v_x_131_);
    return v_res_132_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ctorElim___redArg(
    mut v_t_133_: *mut LeanObject,
    mut v_k_134_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_133_) == 0 {
        let mut v_size_135_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_136_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_137_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_138_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
        v_size_135_ = lean_ctor_get(v_t_133_, 0);
        lean_inc(v_size_135_);
        v_k_136_ = lean_ctor_get(v_t_133_, 1);
        lean_inc(v_k_136_);
        v_v_137_ = lean_ctor_get(v_t_133_, 2);
        lean_inc(v_v_137_);
        v_l_138_ = lean_ctor_get(v_t_133_, 3);
        lean_inc(v_l_138_);
        v_r_139_ = lean_ctor_get(v_t_133_, 4);
        lean_inc(v_r_139_);
        lean_dec_ref_known(v_t_133_, 5);
        v___x_140_ = lean_apply_5(
            v_k_134_,
            v_size_135_,
            v_k_136_,
            v_v_137_,
            v_l_138_,
            v_r_139_,
        );
        return v___x_140_;
    } else {
        return v_k_134_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ctorElim(
    mut v_00_u03b1_141_: *mut LeanObject,
    mut v_00_u03b2_142_: *mut LeanObject,
    mut v_motive_143_: *mut LeanObject,
    mut v_ctorIdx_144_: *mut LeanObject,
    mut v_t_145_: *mut LeanObject,
    mut v_h_146_: *mut LeanObject,
    mut v_k_147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_148_: *mut LeanObject = core::ptr::null_mut();
    v___x_148_ = l_Std_DTreeMap_Internal_Impl_ctorElim___redArg(v_t_145_, v_k_147_);
    return v___x_148_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_ctorElim___boxed(
    mut v_00_u03b1_149_: *mut LeanObject,
    mut v_00_u03b2_150_: *mut LeanObject,
    mut v_motive_151_: *mut LeanObject,
    mut v_ctorIdx_152_: *mut LeanObject,
    mut v_t_153_: *mut LeanObject,
    mut v_h_154_: *mut LeanObject,
    mut v_k_155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_156_: *mut LeanObject = core::ptr::null_mut();
    v_res_156_ = l_Std_DTreeMap_Internal_Impl_ctorElim(
        v_00_u03b1_149_,
        v_00_u03b2_150_,
        v_motive_151_,
        v_ctorIdx_152_,
        v_t_153_,
        v_h_154_,
        v_k_155_,
    );
    lean_dec(v_ctorIdx_152_);
    return v_res_156_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_inner_elim___redArg(
    mut v_t_157_: *mut LeanObject,
    mut v_inner_158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_159_: *mut LeanObject = core::ptr::null_mut();
    v___x_159_ = l_Std_DTreeMap_Internal_Impl_ctorElim___redArg(v_t_157_, v_inner_158_);
    return v___x_159_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_inner_elim(
    mut v_00_u03b1_160_: *mut LeanObject,
    mut v_00_u03b2_161_: *mut LeanObject,
    mut v_motive_162_: *mut LeanObject,
    mut v_t_163_: *mut LeanObject,
    mut v_h_164_: *mut LeanObject,
    mut v_inner_165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
    v___x_166_ = l_Std_DTreeMap_Internal_Impl_ctorElim___redArg(v_t_163_, v_inner_165_);
    return v___x_166_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_leaf_elim___redArg(
    mut v_t_167_: *mut LeanObject,
    mut v_leaf_168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
    v___x_169_ = l_Std_DTreeMap_Internal_Impl_ctorElim___redArg(v_t_167_, v_leaf_168_);
    return v___x_169_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_leaf_elim(
    mut v_00_u03b1_170_: *mut LeanObject,
    mut v_00_u03b2_171_: *mut LeanObject,
    mut v_motive_172_: *mut LeanObject,
    mut v_t_173_: *mut LeanObject,
    mut v_h_174_: *mut LeanObject,
    mut v_leaf_175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
    v___x_176_ = l_Std_DTreeMap_Internal_Impl_ctorElim___redArg(v_t_173_, v_leaf_175_);
    return v___x_176_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instInhabitedImpl_default(
    mut v_00_u03b1_177_: *mut LeanObject,
    mut v_00_u03b2_178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
    v___x_179_ = lean_box(1);
    return v___x_179_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instInhabitedImpl(
    mut v_a_180_: *mut LeanObject,
    mut v_a_181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
    v___x_182_ = lean_box(1);
    return v___x_182_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_delta() -> *mut LeanObject {
    let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
    v___x_183_ = lean_unsigned_to_nat(3);
    return v___x_183_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_ratio() -> *mut LeanObject {
    let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
    v___x_184_ = lean_unsigned_to_nat(2);
    return v___x_184_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_size___redArg(
    mut v_x_185_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_185_) == 0 {
        let mut v_size_186_: *mut LeanObject = core::ptr::null_mut();
        v_size_186_ = lean_ctor_get(v_x_185_, 0);
        lean_inc(v_size_186_);
        return v_size_186_;
    } else {
        let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
        v___x_187_ = lean_unsigned_to_nat(0);
        return v___x_187_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_size___redArg___boxed(
    mut v_x_188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_189_: *mut LeanObject = core::ptr::null_mut();
    v_res_189_ = l_Std_DTreeMap_Internal_Impl_size___redArg(v_x_188_);
    lean_dec(v_x_188_);
    return v_res_189_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_size(
    mut v_00_u03b1_190_: *mut LeanObject,
    mut v_00_u03b2_191_: *mut LeanObject,
    mut v_x_192_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_192_) == 0 {
        let mut v_size_193_: *mut LeanObject = core::ptr::null_mut();
        v_size_193_ = lean_ctor_get(v_x_192_, 0);
        lean_inc(v_size_193_);
        return v_size_193_;
    } else {
        let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
        v___x_194_ = lean_unsigned_to_nat(0);
        return v___x_194_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_size___boxed(
    mut v_00_u03b1_195_: *mut LeanObject,
    mut v_00_u03b2_196_: *mut LeanObject,
    mut v_x_197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_198_: *mut LeanObject = core::ptr::null_mut();
    v_res_198_ = l_Std_DTreeMap_Internal_Impl_size(v_00_u03b1_195_, v_00_u03b2_196_, v_x_197_);
    lean_dec(v_x_197_);
    return v_res_198_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_toListModel___redArg(
    mut v_x_199_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_199_) == 0 {
        let mut v_k_200_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_201_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_202_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_203_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
        v_k_200_ = lean_ctor_get(v_x_199_, 1);
        v_v_201_ = lean_ctor_get(v_x_199_, 2);
        v_l_202_ = lean_ctor_get(v_x_199_, 3);
        v_r_203_ = lean_ctor_get(v_x_199_, 4);
        v___x_204_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_202_);
        lean_inc(v_v_201_);
        lean_inc(v_k_200_);
        v___x_205_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_205_, 0, v_k_200_);
        lean_ctor_set(v___x_205_, 1, v_v_201_);
        v___x_206_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_203_);
        v___x_207_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_207_, 0, v___x_205_);
        lean_ctor_set(v___x_207_, 1, v___x_206_);
        v___x_208_ = l_List_appendTR___redArg(v___x_204_, v___x_207_);
        return v___x_208_;
    } else {
        let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
        v___x_209_ = lean_box(0);
        return v___x_209_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_toListModel___redArg___boxed(
    mut v_x_210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_211_: *mut LeanObject = core::ptr::null_mut();
    v_res_211_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_x_210_);
    lean_dec(v_x_210_);
    return v_res_211_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_toListModel(
    mut v_00_u03b1_212_: *mut LeanObject,
    mut v_00_u03b2_213_: *mut LeanObject,
    mut v_x_214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    v___x_215_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_x_214_);
    return v___x_215_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_toListModel___boxed(
    mut v_00_u03b1_216_: *mut LeanObject,
    mut v_00_u03b2_217_: *mut LeanObject,
    mut v_x_218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_219_: *mut LeanObject = core::ptr::null_mut();
    v_res_219_ =
        l_Std_DTreeMap_Internal_Impl_toListModel(v_00_u03b1_216_, v_00_u03b2_217_, v_x_218_);
    lean_dec(v_x_218_);
    return v_res_219_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_treeSize___redArg(
    mut v_x_220_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_220_) == 0 {
        let mut v_l_221_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
        v_l_221_ = lean_ctor_get(v_x_220_, 3);
        v_r_222_ = lean_ctor_get(v_x_220_, 4);
        v___x_223_ = lean_unsigned_to_nat(1);
        v___x_224_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_l_221_);
        v___x_225_ = lean_nat_add(v___x_223_, v___x_224_);
        lean_dec(v___x_224_);
        v___x_226_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_r_222_);
        v___x_227_ = lean_nat_add(v___x_225_, v___x_226_);
        lean_dec(v___x_226_);
        lean_dec(v___x_225_);
        return v___x_227_;
    } else {
        let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
        v___x_228_ = lean_unsigned_to_nat(0);
        return v___x_228_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_treeSize___redArg___boxed(
    mut v_x_229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_230_: *mut LeanObject = core::ptr::null_mut();
    v_res_230_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_x_229_);
    lean_dec(v_x_229_);
    return v_res_230_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_treeSize(
    mut v_00_u03b1_231_: *mut LeanObject,
    mut v_00_u03b2_232_: *mut LeanObject,
    mut v_x_233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    v___x_234_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_x_233_);
    return v___x_234_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_treeSize___boxed(
    mut v_00_u03b1_235_: *mut LeanObject,
    mut v_00_u03b2_236_: *mut LeanObject,
    mut v_x_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_238_: *mut LeanObject = core::ptr::null_mut();
    v_res_238_ = l_Std_DTreeMap_Internal_Impl_treeSize(v_00_u03b1_235_, v_00_u03b2_236_, v_x_237_);
    lean_dec(v_x_237_);
    return v_res_238_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Internal_Def(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_SInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_DTreeMap_Internal_delta = _init_l_Std_DTreeMap_Internal_delta();
    lean_mark_persistent(l_Std_DTreeMap_Internal_delta);
    l_Std_DTreeMap_Internal_ratio = _init_l_Std_DTreeMap_Internal_ratio();
    lean_mark_persistent(l_Std_DTreeMap_Internal_ratio);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Internal_Def(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DTreeMap_Internal_Def(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_SInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Def(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Internal_Def(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Internal_Def(builtin);
}
