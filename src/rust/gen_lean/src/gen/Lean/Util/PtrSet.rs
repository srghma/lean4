// Lean compiler output
// Module: Lean.Util.PtrSet
// Imports: Init.Data.Hashable Std.Data.HashSet.Basic
use crate::ffi::{
    lean_mk_array, lean_nat_div, lean_nat_mul, lean_ptr_addr, lean_uint64_mix_hash,
    lean_usize_dec_eq, lean_usize_to_uint64,
};
use crate::r#gen::Init::Data::Hashable::{
    initialize_Init_Data_Hashable, runtime_initialize_Init_Data_Hashable,
};
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
};
use crate::r#gen::Std::Data::HashSet::Basic::{
    initialize_Std_Data_HashSet_Basic, runtime_initialize_Std_Data_HashSet_Basic,
};
pub static l_Lean_instHashablePtr___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instHashablePtr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instHashablePtr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashablePtr___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_instBEqPtr___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instBEqPtr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqPtr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqPtr___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instHashablePtr___lam__0(mut v_a_151_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v___x_152_: usize = 0;
    let mut v___x_153_: u64 = 0;
    let mut v___x_154_: u64 = 0;
    let mut v___x_155_: u64 = 0;
    v___x_152_ = lean_ptr_addr(v_a_151_);
    v___x_153_ = lean_usize_to_uint64(v___x_152_);
    v___x_154_ = 11u64;
    v___x_155_ = lean_uint64_mix_hash(v___x_153_, v___x_154_);
    return v___x_155_;
}
pub unsafe fn l_Lean_instHashablePtr___lam__0___boxed(
    mut v_a_156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_157_: u64 = 0;
    let mut v_r_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_157_ = l_Lean_instHashablePtr___lam__0(v_a_156_);
    crate::leanh::lean_dec(v_a_156_);
    v_r_158_ = crate::leanh::lean_box_uint64(v_res_157_);
    return v_r_158_;
}
pub unsafe fn l_Lean_instHashablePtr(
    mut v_00_u03b1_160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_161_ = l_Lean_instHashablePtr___closed__0;
    return v___f_161_;
}
pub unsafe fn l_Lean_instBEqPtr___lam__0(
    mut v_a_162_: *mut crate::leanh::LeanObject,
    mut v_b_163_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_164_: usize = 0;
    let mut v___x_165_: usize = 0;
    let mut v___x_166_: u8 = 0;
    v___x_164_ = lean_ptr_addr(v_a_162_);
    v___x_165_ = lean_ptr_addr(v_b_163_);
    v___x_166_ = lean_usize_dec_eq(v___x_164_, v___x_165_);
    return v___x_166_;
}
pub unsafe fn l_Lean_instBEqPtr___lam__0___boxed(
    mut v_a_167_: *mut crate::leanh::LeanObject,
    mut v_b_168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_169_: u8 = 0;
    let mut v_r_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_169_ = l_Lean_instBEqPtr___lam__0(v_a_167_, v_b_168_);
    crate::leanh::lean_dec(v_b_168_);
    crate::leanh::lean_dec(v_a_167_);
    v_r_170_ = crate::leanh::lean_box((v_res_169_) as usize);
    return v_r_170_;
}
pub unsafe fn l_Lean_instBEqPtr(
    mut v_00_u03b1_172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_173_ = l_Lean_instBEqPtr___closed__0;
    return v___f_173_;
}
pub unsafe fn l_Lean_mkPtrSet___redArg(
    mut v_capacity_174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_175_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_176_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_177_ = lean_nat_mul(v_capacity_174_, v___x_176_);
    v___x_178_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_179_ = lean_nat_div(v___x_177_, v___x_178_);
    crate::leanh::lean_dec(v___x_177_);
    v___x_180_ = l_Nat_nextPowerOfTwo(v___x_179_);
    crate::leanh::lean_dec(v___x_179_);
    v___x_181_ = crate::leanh::lean_box(0);
    v___x_182_ = lean_mk_array(v___x_180_, v___x_181_);
    v___x_183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_183_, 0, v___x_175_);
    crate::leanh::lean_ctor_set(v___x_183_, 1, v___x_182_);
    return v___x_183_;
}
pub unsafe fn l_Lean_mkPtrSet___redArg___boxed(
    mut v_capacity_184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_185_ = l_Lean_mkPtrSet___redArg(v_capacity_184_);
    crate::leanh::lean_dec(v_capacity_184_);
    return v_res_185_;
}
pub unsafe fn l_Lean_mkPtrSet(
    mut v_00_u03b1_186_: *mut crate::leanh::LeanObject,
    mut v_capacity_187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_188_ = l_Lean_mkPtrSet___redArg(v_capacity_187_);
    return v___x_188_;
}
pub unsafe fn l_Lean_mkPtrSet___boxed(
    mut v_00_u03b1_189_: *mut crate::leanh::LeanObject,
    mut v_capacity_190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_191_ = l_Lean_mkPtrSet(v_00_u03b1_189_, v_capacity_190_);
    crate::leanh::lean_dec(v_capacity_190_);
    return v_res_191_;
}
pub unsafe fn l_Lean_PtrSet_insert___redArg(
    mut v_s_192_: *mut crate::leanh::LeanObject,
    mut v_a_193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_194_ = l_Lean_instBEqPtr___closed__0;
    v___f_195_ = l_Lean_instHashablePtr___closed__0;
    v___x_196_ = crate::leanh::lean_box(0);
    v___x_197_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v___f_194_, v___f_195_, v_s_192_, v_a_193_, v___x_196_,
    );
    return v___x_197_;
}
pub unsafe fn l_Lean_PtrSet_insert(
    mut v_00_u03b1_198_: *mut crate::leanh::LeanObject,
    mut v_s_199_: *mut crate::leanh::LeanObject,
    mut v_a_200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_201_ = l_Lean_instBEqPtr___closed__0;
    v___f_202_ = l_Lean_instHashablePtr___closed__0;
    v___x_203_ = crate::leanh::lean_box(0);
    v___x_204_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v___f_201_, v___f_202_, v_s_199_, v_a_200_, v___x_203_,
    );
    return v___x_204_;
}
pub unsafe fn l_Lean_PtrSet_contains___redArg(
    mut v_s_205_: *mut crate::leanh::LeanObject,
    mut v_a_206_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: u8 = 0;
    v___f_207_ = l_Lean_instBEqPtr___closed__0;
    v___f_208_ = l_Lean_instHashablePtr___closed__0;
    v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___f_207_, v___f_208_, v_s_205_, v_a_206_,
    );
    return v___x_209_;
}
pub unsafe fn l_Lean_PtrSet_contains___redArg___boxed(
    mut v_s_210_: *mut crate::leanh::LeanObject,
    mut v_a_211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_212_: u8 = 0;
    let mut v_r_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_212_ = l_Lean_PtrSet_contains___redArg(v_s_210_, v_a_211_);
    crate::leanh::lean_dec_ref(v_s_210_);
    v_r_213_ = crate::leanh::lean_box((v_res_212_) as usize);
    return v_r_213_;
}
pub unsafe fn l_Lean_PtrSet_contains(
    mut v_00_u03b1_214_: *mut crate::leanh::LeanObject,
    mut v_s_215_: *mut crate::leanh::LeanObject,
    mut v_a_216_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: u8 = 0;
    v___f_217_ = l_Lean_instBEqPtr___closed__0;
    v___f_218_ = l_Lean_instHashablePtr___closed__0;
    v___x_219_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___f_217_, v___f_218_, v_s_215_, v_a_216_,
    );
    return v___x_219_;
}
pub unsafe fn l_Lean_PtrSet_contains___boxed(
    mut v_00_u03b1_220_: *mut crate::leanh::LeanObject,
    mut v_s_221_: *mut crate::leanh::LeanObject,
    mut v_a_222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_223_: u8 = 0;
    let mut v_r_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_223_ = l_Lean_PtrSet_contains(v_00_u03b1_220_, v_s_221_, v_a_222_);
    crate::leanh::lean_dec_ref(v_s_221_);
    v_r_224_ = crate::leanh::lean_box((v_res_223_) as usize);
    return v_r_224_;
}
pub unsafe fn l_Lean_mkPtrMap___redArg(
    mut v_capacity_225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_226_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_227_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_228_ = lean_nat_mul(v_capacity_225_, v___x_227_);
    v___x_229_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_230_ = lean_nat_div(v___x_228_, v___x_229_);
    crate::leanh::lean_dec(v___x_228_);
    v___x_231_ = l_Nat_nextPowerOfTwo(v___x_230_);
    crate::leanh::lean_dec(v___x_230_);
    v___x_232_ = crate::leanh::lean_box(0);
    v___x_233_ = lean_mk_array(v___x_231_, v___x_232_);
    v___x_234_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_234_, 0, v___x_226_);
    crate::leanh::lean_ctor_set(v___x_234_, 1, v___x_233_);
    return v___x_234_;
}
pub unsafe fn l_Lean_mkPtrMap___redArg___boxed(
    mut v_capacity_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_236_ = l_Lean_mkPtrMap___redArg(v_capacity_235_);
    crate::leanh::lean_dec(v_capacity_235_);
    return v_res_236_;
}
pub unsafe fn l_Lean_mkPtrMap(
    mut v_00_u03b1_237_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_238_: *mut crate::leanh::LeanObject,
    mut v_capacity_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_240_ = l_Lean_mkPtrMap___redArg(v_capacity_239_);
    return v___x_240_;
}
pub unsafe fn l_Lean_mkPtrMap___boxed(
    mut v_00_u03b1_241_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_242_: *mut crate::leanh::LeanObject,
    mut v_capacity_243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_244_ = l_Lean_mkPtrMap(v_00_u03b1_241_, v_00_u03b2_242_, v_capacity_243_);
    crate::leanh::lean_dec(v_capacity_243_);
    return v_res_244_;
}
pub unsafe fn l_Lean_PtrMap_insert___redArg(
    mut v_s_245_: *mut crate::leanh::LeanObject,
    mut v_a_246_: *mut crate::leanh::LeanObject,
    mut v_b_247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_248_ = l_Lean_instBEqPtr___closed__0;
    v___f_249_ = l_Lean_instHashablePtr___closed__0;
    v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v___f_248_, v___f_249_, v_s_245_, v_a_246_, v_b_247_,
    );
    return v___x_250_;
}
pub unsafe fn l_Lean_PtrMap_insert(
    mut v_00_u03b1_251_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_252_: *mut crate::leanh::LeanObject,
    mut v_s_253_: *mut crate::leanh::LeanObject,
    mut v_a_254_: *mut crate::leanh::LeanObject,
    mut v_b_255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_256_ = l_Lean_instBEqPtr___closed__0;
    v___f_257_ = l_Lean_instHashablePtr___closed__0;
    v___x_258_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v___f_256_, v___f_257_, v_s_253_, v_a_254_, v_b_255_,
    );
    return v___x_258_;
}
pub unsafe fn l_Lean_PtrMap_contains___redArg(
    mut v_s_259_: *mut crate::leanh::LeanObject,
    mut v_a_260_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: u8 = 0;
    v___f_261_ = l_Lean_instBEqPtr___closed__0;
    v___f_262_ = l_Lean_instHashablePtr___closed__0;
    v___x_263_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___f_261_, v___f_262_, v_s_259_, v_a_260_,
    );
    return v___x_263_;
}
pub unsafe fn l_Lean_PtrMap_contains___redArg___boxed(
    mut v_s_264_: *mut crate::leanh::LeanObject,
    mut v_a_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_266_: u8 = 0;
    let mut v_r_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_266_ = l_Lean_PtrMap_contains___redArg(v_s_264_, v_a_265_);
    crate::leanh::lean_dec_ref(v_s_264_);
    v_r_267_ = crate::leanh::lean_box((v_res_266_) as usize);
    return v_r_267_;
}
pub unsafe fn l_Lean_PtrMap_contains(
    mut v_00_u03b1_268_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_269_: *mut crate::leanh::LeanObject,
    mut v_s_270_: *mut crate::leanh::LeanObject,
    mut v_a_271_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: u8 = 0;
    v___f_272_ = l_Lean_instBEqPtr___closed__0;
    v___f_273_ = l_Lean_instHashablePtr___closed__0;
    v___x_274_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___f_272_, v___f_273_, v_s_270_, v_a_271_,
    );
    return v___x_274_;
}
pub unsafe fn l_Lean_PtrMap_contains___boxed(
    mut v_00_u03b1_275_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_276_: *mut crate::leanh::LeanObject,
    mut v_s_277_: *mut crate::leanh::LeanObject,
    mut v_a_278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_279_: u8 = 0;
    let mut v_r_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_279_ = l_Lean_PtrMap_contains(v_00_u03b1_275_, v_00_u03b2_276_, v_s_277_, v_a_278_);
    crate::leanh::lean_dec_ref(v_s_277_);
    v_r_280_ = crate::leanh::lean_box((v_res_279_) as usize);
    return v_r_280_;
}
pub unsafe fn l_Lean_PtrMap_find_x3f___redArg(
    mut v_s_281_: *mut crate::leanh::LeanObject,
    mut v_a_282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_283_ = l_Lean_instBEqPtr___closed__0;
    v___f_284_ = l_Lean_instHashablePtr___closed__0;
    v___x_285_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v___f_283_, v___f_284_, v_s_281_, v_a_282_,
    );
    return v___x_285_;
}
pub unsafe fn l_Lean_PtrMap_find_x3f___redArg___boxed(
    mut v_s_286_: *mut crate::leanh::LeanObject,
    mut v_a_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_288_ = l_Lean_PtrMap_find_x3f___redArg(v_s_286_, v_a_287_);
    crate::leanh::lean_dec_ref(v_s_286_);
    return v_res_288_;
}
pub unsafe fn l_Lean_PtrMap_find_x3f(
    mut v_00_u03b1_289_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_290_: *mut crate::leanh::LeanObject,
    mut v_s_291_: *mut crate::leanh::LeanObject,
    mut v_a_292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_293_ = l_Lean_instBEqPtr___closed__0;
    v___f_294_ = l_Lean_instHashablePtr___closed__0;
    v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v___f_293_, v___f_294_, v_s_291_, v_a_292_,
    );
    return v___x_295_;
}
pub unsafe fn l_Lean_PtrMap_find_x3f___boxed(
    mut v_00_u03b1_296_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_297_: *mut crate::leanh::LeanObject,
    mut v_s_298_: *mut crate::leanh::LeanObject,
    mut v_a_299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_300_ = l_Lean_PtrMap_find_x3f(v_00_u03b1_296_, v_00_u03b2_297_, v_s_298_, v_a_299_);
    crate::leanh::lean_dec_ref(v_s_298_);
    return v_res_300_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_PtrSet(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_PtrSet(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_PtrSet(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashSet_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_PtrSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_PtrSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_PtrSet(builtin);
}
