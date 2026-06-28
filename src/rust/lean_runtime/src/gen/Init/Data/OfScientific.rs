// Lean compiler output
// Module: Init.Data.OfScientific
// Imports: Init.Data.Float32 Init.Data.Nat.Log2 Init.Meta
use crate::r#gen::Init::Data::Float32::{
    initialize_Init_Data_Float32, runtime_initialize_Init_Data_Float32,
};
use crate::r#gen::Init::Data::Nat::Log2::{
    initialize_Init_Data_Nat_Log2, runtime_initialize_Init_Data_Nat_Log2,
};
use crate::r#gen::Init::Meta::{initialize_Init_Meta, runtime_initialize_Init_Meta};
use crate::lean_imports_rs::Init::Data::Float::{
    lean_float_negate, lean_float_scaleb, lean_uint64_to_float,
};
use crate::lean_imports_rs::Init::Data::Float32::{
    lean_float32_negate, lean_float32_scaleb, lean_uint64_to_float32,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_lt, lean_int_mul, lean_int_neg, lean_int_sub, lean_nat_abs,
    lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{lean_nat_shiftl, lean_nat_shiftr};
use crate::lean_imports_rs::Init::Data::Nat::Log2::lean_nat_log2;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint64_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_div, lean_nat_mul, lean_nat_pow, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_box_float, lean_box_float32, lean_dec,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_unbox,
    lean_unsigned_to_nat,
};
static mut l_Float_ofScientific___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Float_ofScientific___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Float_ofScientific___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Float_ofScientific___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_instOfScientificFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float_ofScientific___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instOfScientificFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instOfScientificFloat___closed__0_value) as *mut LeanObject;
pub static mut l_instOfScientificFloat: *mut LeanObject =
    core::ptr::addr_of!(l_instOfScientificFloat___closed__0_value) as *mut LeanObject;
static mut l_Float_ofInt___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Float_ofInt___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_instOfScientificFloat32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float32_ofScientific___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instOfScientificFloat32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instOfScientificFloat32___closed__0_value) as *mut LeanObject;
pub static mut l_instOfScientificFloat32: *mut LeanObject =
    core::ptr::addr_of!(l_instOfScientificFloat32___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Nat_cast___at___00Float_ofBinaryScientific_spec__0(
    mut v_a_165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
    v___x_166_ = lean_nat_to_int(v_a_165_);
    return v___x_166_;
}
pub unsafe fn l_Float_ofBinaryScientific(
    mut v_m_167_: *mut LeanObject,
    mut v_e_168_: *mut LeanObject,
) -> f64 {
    let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_173_: u64 = 0;
    let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_176_: f64 = 0.0;
    let mut v___x_177_: f64 = 0.0;
    v___x_169_ = lean_nat_log2(v_m_167_);
    v___x_170_ = lean_unsigned_to_nat(63);
    v_s_171_ = lean_nat_sub(v___x_169_, v___x_170_);
    lean_dec(v___x_169_);
    v___x_172_ = lean_nat_shiftr(v_m_167_, v_s_171_);
    v_m_173_ = lean_uint64_of_nat(v___x_172_);
    lean_dec(v___x_172_);
    v___x_174_ = lean_nat_to_int(v_s_171_);
    v_e_175_ = lean_int_add(v_e_168_, v___x_174_);
    lean_dec(v___x_174_);
    v___x_176_ = lean_uint64_to_float(v_m_173_);
    v___x_177_ = lean_float_scaleb(v___x_176_, v_e_175_);
    lean_dec(v_e_175_);
    return v___x_177_;
}
pub unsafe fn l_Float_ofBinaryScientific___boxed(
    mut v_m_178_: *mut LeanObject,
    mut v_e_179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_180_: f64 = 0.0;
    let mut v_r_181_: *mut LeanObject = core::ptr::null_mut();
    v_res_180_ = l_Float_ofBinaryScientific(v_m_178_, v_e_179_);
    lean_dec(v_e_179_);
    lean_dec(v_m_178_);
    v_r_181_ = lean_box_float(v_res_180_);
    return v_r_181_;
}
pub unsafe fn _init_l_Float_ofScientific___closed__0() -> *mut LeanObject {
    let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
    v___x_182_ = lean_unsigned_to_nat(4);
    v___x_183_ = lean_nat_to_int(v___x_182_);
    return v___x_183_;
}
pub unsafe fn _init_l_Float_ofScientific___closed__1() -> *mut LeanObject {
    let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
    v___x_184_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Float_ofScientific___closed__0),
        core::ptr::addr_of_mut!(l_Float_ofScientific___closed__0_once),
        _init_l_Float_ofScientific___closed__0,
    );
    v___x_185_ = lean_int_neg(v___x_184_);
    return v___x_185_;
}
pub unsafe fn l_Float_ofScientific(
    mut v_m_186_: *mut LeanObject,
    mut v_s_187_: u8,
    mut v_e_188_: *mut LeanObject,
) -> f64 {
    if v_s_187_ == 0 {
        let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_193_: f64 = 0.0;
        v___x_189_ = lean_unsigned_to_nat(5);
        v___x_190_ = lean_nat_pow(v___x_189_, v_e_188_);
        v___x_191_ = lean_nat_mul(v_m_186_, v___x_190_);
        lean_dec(v___x_190_);
        v___x_192_ = lean_nat_to_int(v_e_188_);
        v___x_193_ = l_Float_ofBinaryScientific(v___x_191_, v___x_192_);
        lean_dec(v___x_192_);
        lean_dec(v___x_191_);
        return v___x_193_;
    } else {
        let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_195_: *mut LeanObject = core::ptr::null_mut();
        let mut v_s_196_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
        let mut v_m_203_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_209_: f64 = 0.0;
        v___x_194_ = lean_unsigned_to_nat(64);
        v___x_195_ = lean_nat_log2(v_m_186_);
        v_s_196_ = lean_nat_sub(v___x_194_, v___x_195_);
        lean_dec(v___x_195_);
        v___x_197_ = lean_unsigned_to_nat(3);
        v___x_198_ = lean_nat_mul(v___x_197_, v_e_188_);
        v___x_199_ = lean_nat_add(v___x_198_, v_s_196_);
        lean_dec(v___x_198_);
        v___x_200_ = lean_nat_shiftl(v_m_186_, v___x_199_);
        lean_dec(v___x_199_);
        v___x_201_ = lean_unsigned_to_nat(5);
        v___x_202_ = lean_nat_pow(v___x_201_, v_e_188_);
        v_m_203_ = lean_nat_div(v___x_200_, v___x_202_);
        lean_dec(v___x_202_);
        lean_dec(v___x_200_);
        v___x_204_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Float_ofScientific___closed__1),
            core::ptr::addr_of_mut!(l_Float_ofScientific___closed__1_once),
            _init_l_Float_ofScientific___closed__1,
        );
        v___x_205_ = lean_nat_to_int(v_e_188_);
        v___x_206_ = lean_int_mul(v___x_204_, v___x_205_);
        lean_dec(v___x_205_);
        v___x_207_ = lean_nat_to_int(v_s_196_);
        v___x_208_ = lean_int_sub(v___x_206_, v___x_207_);
        lean_dec(v___x_207_);
        lean_dec(v___x_206_);
        v___x_209_ = l_Float_ofBinaryScientific(v_m_203_, v___x_208_);
        lean_dec(v___x_208_);
        lean_dec(v_m_203_);
        return v___x_209_;
    }
}
pub unsafe fn l_Float_ofScientific___boxed(
    mut v_m_210_: *mut LeanObject,
    mut v_s_211_: *mut LeanObject,
    mut v_e_212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_213_: u8 = 0;
    let mut v_res_214_: f64 = 0.0;
    let mut v_r_215_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_213_ = (lean_unbox(v_s_211_) as u8);
    v_res_214_ = l_Float_ofScientific(v_m_210_, v_s_boxed_213_, v_e_212_);
    lean_dec(v_m_210_);
    v_r_215_ = lean_box_float(v_res_214_);
    return v_r_215_;
}
pub unsafe fn lean_float_of_nat(mut v_n_218_: *mut LeanObject) -> f64 {
    let mut v___x_219_: u8 = 0;
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_221_: f64 = 0.0;
    v___x_219_ = 0;
    v___x_220_ = lean_unsigned_to_nat(0);
    v___x_221_ = l_Float_ofScientific(v_n_218_, v___x_219_, v___x_220_);
    lean_dec(v_n_218_);
    return v___x_221_;
}
pub unsafe fn l_Float_ofNat___boxed(mut v_n_222_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_223_: f64 = 0.0;
    let mut v_r_224_: *mut LeanObject = core::ptr::null_mut();
    v_res_223_ = lean_float_of_nat(v_n_222_);
    v_r_224_ = lean_box_float(v_res_223_);
    return v_r_224_;
}
pub unsafe fn _init_l_Float_ofInt___closed__0() -> *mut LeanObject {
    let mut v_natZero_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_226_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_225_ = lean_unsigned_to_nat(0);
    v_intZero_226_ = lean_nat_to_int(v_natZero_225_);
    return v_intZero_226_;
}
pub unsafe fn l_Float_ofInt(mut v_x_227_: *mut LeanObject) -> f64 {
    let mut v_intZero_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_229_: u8 = 0;
    v_intZero_228_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Float_ofInt___closed__0),
        core::ptr::addr_of_mut!(l_Float_ofInt___closed__0_once),
        _init_l_Float_ofInt___closed__0,
    );
    v_isNeg_229_ = lean_int_dec_lt(v_x_227_, v_intZero_228_);
    if v_isNeg_229_ == 0 {
        let mut v_a_230_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_231_: f64 = 0.0;
        v_a_230_ = lean_nat_abs(v_x_227_);
        v___x_231_ = lean_float_of_nat(v_a_230_);
        return v___x_231_;
    } else {
        let mut v_abs_232_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_233_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_234_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_236_: f64 = 0.0;
        let mut v___x_237_: f64 = 0.0;
        v_abs_232_ = lean_nat_abs(v_x_227_);
        v_one_233_ = lean_unsigned_to_nat(1);
        v_a_234_ = lean_nat_sub(v_abs_232_, v_one_233_);
        lean_dec(v_abs_232_);
        v___x_235_ = lean_nat_add(v_a_234_, v_one_233_);
        lean_dec(v_a_234_);
        v___x_236_ = lean_float_of_nat(v___x_235_);
        v___x_237_ = lean_float_negate(v___x_236_);
        return v___x_237_;
    }
}
pub unsafe fn l_Float_ofInt___boxed(mut v_x_238_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_239_: f64 = 0.0;
    let mut v_r_240_: *mut LeanObject = core::ptr::null_mut();
    v_res_239_ = l_Float_ofInt(v_x_238_);
    lean_dec(v_x_238_);
    v_r_240_ = lean_box_float(v_res_239_);
    return v_r_240_;
}
pub unsafe fn l_instOfNatFloat(mut v_n_241_: *mut LeanObject) -> f64 {
    let mut v___x_242_: f64 = 0.0;
    v___x_242_ = lean_float_of_nat(v_n_241_);
    return v___x_242_;
}
pub unsafe fn l_instOfNatFloat___boxed(mut v_n_243_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_244_: f64 = 0.0;
    let mut v_r_245_: *mut LeanObject = core::ptr::null_mut();
    v_res_244_ = l_instOfNatFloat(v_n_243_);
    v_r_245_ = lean_box_float(v_res_244_);
    return v_r_245_;
}
pub unsafe fn l_Nat_toFloat(mut v_n_246_: *mut LeanObject) -> f64 {
    let mut v___x_247_: f64 = 0.0;
    v___x_247_ = lean_float_of_nat(v_n_246_);
    return v___x_247_;
}
pub unsafe fn l_Nat_toFloat___boxed(mut v_n_248_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_249_: f64 = 0.0;
    let mut v_r_250_: *mut LeanObject = core::ptr::null_mut();
    v_res_249_ = l_Nat_toFloat(v_n_248_);
    v_r_250_ = lean_box_float(v_res_249_);
    return v_r_250_;
}
pub unsafe fn l_Float32_ofBinaryScientific(
    mut v_m_251_: *mut LeanObject,
    mut v_e_252_: *mut LeanObject,
) -> f32 {
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_257_: u64 = 0;
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_260_: f32 = 0.0f32;
    let mut v___x_261_: f32 = 0.0f32;
    v___x_253_ = lean_nat_log2(v_m_251_);
    v___x_254_ = lean_unsigned_to_nat(63);
    v_s_255_ = lean_nat_sub(v___x_253_, v___x_254_);
    lean_dec(v___x_253_);
    v___x_256_ = lean_nat_shiftr(v_m_251_, v_s_255_);
    v_m_257_ = lean_uint64_of_nat(v___x_256_);
    lean_dec(v___x_256_);
    v___x_258_ = lean_nat_to_int(v_s_255_);
    v_e_259_ = lean_int_add(v_e_252_, v___x_258_);
    lean_dec(v___x_258_);
    v___x_260_ = lean_uint64_to_float32(v_m_257_);
    v___x_261_ = lean_float32_scaleb(v___x_260_, v_e_259_);
    lean_dec(v_e_259_);
    return v___x_261_;
}
pub unsafe fn l_Float32_ofBinaryScientific___boxed(
    mut v_m_262_: *mut LeanObject,
    mut v_e_263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_264_: f32 = 0.0f32;
    let mut v_r_265_: *mut LeanObject = core::ptr::null_mut();
    v_res_264_ = l_Float32_ofBinaryScientific(v_m_262_, v_e_263_);
    lean_dec(v_e_263_);
    lean_dec(v_m_262_);
    v_r_265_ = lean_box_float32(v_res_264_);
    return v_r_265_;
}
pub unsafe fn l_Float32_ofScientific(
    mut v_m_266_: *mut LeanObject,
    mut v_s_267_: u8,
    mut v_e_268_: *mut LeanObject,
) -> f32 {
    if v_s_267_ == 0 {
        let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_273_: f32 = 0.0f32;
        v___x_269_ = lean_unsigned_to_nat(5);
        v___x_270_ = lean_nat_pow(v___x_269_, v_e_268_);
        v___x_271_ = lean_nat_mul(v_m_266_, v___x_270_);
        lean_dec(v___x_270_);
        v___x_272_ = lean_nat_to_int(v_e_268_);
        v___x_273_ = l_Float32_ofBinaryScientific(v___x_271_, v___x_272_);
        lean_dec(v___x_272_);
        lean_dec(v___x_271_);
        return v___x_273_;
    } else {
        let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
        let mut v_s_276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
        let mut v_m_283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_289_: f32 = 0.0f32;
        v___x_274_ = lean_unsigned_to_nat(64);
        v___x_275_ = lean_nat_log2(v_m_266_);
        v_s_276_ = lean_nat_sub(v___x_274_, v___x_275_);
        lean_dec(v___x_275_);
        v___x_277_ = lean_unsigned_to_nat(3);
        v___x_278_ = lean_nat_mul(v___x_277_, v_e_268_);
        v___x_279_ = lean_nat_add(v___x_278_, v_s_276_);
        lean_dec(v___x_278_);
        v___x_280_ = lean_nat_shiftl(v_m_266_, v___x_279_);
        lean_dec(v___x_279_);
        v___x_281_ = lean_unsigned_to_nat(5);
        v___x_282_ = lean_nat_pow(v___x_281_, v_e_268_);
        v_m_283_ = lean_nat_div(v___x_280_, v___x_282_);
        lean_dec(v___x_282_);
        lean_dec(v___x_280_);
        v___x_284_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Float_ofScientific___closed__1),
            core::ptr::addr_of_mut!(l_Float_ofScientific___closed__1_once),
            _init_l_Float_ofScientific___closed__1,
        );
        v___x_285_ = lean_nat_to_int(v_e_268_);
        v___x_286_ = lean_int_mul(v___x_284_, v___x_285_);
        lean_dec(v___x_285_);
        v___x_287_ = lean_nat_to_int(v_s_276_);
        v___x_288_ = lean_int_sub(v___x_286_, v___x_287_);
        lean_dec(v___x_287_);
        lean_dec(v___x_286_);
        v___x_289_ = l_Float32_ofBinaryScientific(v_m_283_, v___x_288_);
        lean_dec(v___x_288_);
        lean_dec(v_m_283_);
        return v___x_289_;
    }
}
pub unsafe fn l_Float32_ofScientific___boxed(
    mut v_m_290_: *mut LeanObject,
    mut v_s_291_: *mut LeanObject,
    mut v_e_292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_293_: u8 = 0;
    let mut v_res_294_: f32 = 0.0f32;
    let mut v_r_295_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_293_ = (lean_unbox(v_s_291_) as u8);
    v_res_294_ = l_Float32_ofScientific(v_m_290_, v_s_boxed_293_, v_e_292_);
    lean_dec(v_m_290_);
    v_r_295_ = lean_box_float32(v_res_294_);
    return v_r_295_;
}
pub unsafe fn lean_float32_of_nat(mut v_n_298_: *mut LeanObject) -> f32 {
    let mut v___x_299_: u8 = 0;
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_301_: f32 = 0.0f32;
    v___x_299_ = 0;
    v___x_300_ = lean_unsigned_to_nat(0);
    v___x_301_ = l_Float32_ofScientific(v_n_298_, v___x_299_, v___x_300_);
    lean_dec(v_n_298_);
    return v___x_301_;
}
pub unsafe fn l_Float32_ofNat___boxed(mut v_n_302_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_303_: f32 = 0.0f32;
    let mut v_r_304_: *mut LeanObject = core::ptr::null_mut();
    v_res_303_ = lean_float32_of_nat(v_n_302_);
    v_r_304_ = lean_box_float32(v_res_303_);
    return v_r_304_;
}
pub unsafe fn l_Float32_ofInt(mut v_x_305_: *mut LeanObject) -> f32 {
    let mut v_intZero_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_307_: u8 = 0;
    v_intZero_306_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Float_ofInt___closed__0),
        core::ptr::addr_of_mut!(l_Float_ofInt___closed__0_once),
        _init_l_Float_ofInt___closed__0,
    );
    v_isNeg_307_ = lean_int_dec_lt(v_x_305_, v_intZero_306_);
    if v_isNeg_307_ == 0 {
        let mut v_a_308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_309_: f32 = 0.0f32;
        v_a_308_ = lean_nat_abs(v_x_305_);
        v___x_309_ = lean_float32_of_nat(v_a_308_);
        return v___x_309_;
    } else {
        let mut v_abs_310_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_311_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_312_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_314_: f32 = 0.0f32;
        let mut v___x_315_: f32 = 0.0f32;
        v_abs_310_ = lean_nat_abs(v_x_305_);
        v_one_311_ = lean_unsigned_to_nat(1);
        v_a_312_ = lean_nat_sub(v_abs_310_, v_one_311_);
        lean_dec(v_abs_310_);
        v___x_313_ = lean_nat_add(v_a_312_, v_one_311_);
        lean_dec(v_a_312_);
        v___x_314_ = lean_float32_of_nat(v___x_313_);
        v___x_315_ = lean_float32_negate(v___x_314_);
        return v___x_315_;
    }
}
pub unsafe fn l_Float32_ofInt___boxed(mut v_x_316_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_317_: f32 = 0.0f32;
    let mut v_r_318_: *mut LeanObject = core::ptr::null_mut();
    v_res_317_ = l_Float32_ofInt(v_x_316_);
    lean_dec(v_x_316_);
    v_r_318_ = lean_box_float32(v_res_317_);
    return v_r_318_;
}
pub unsafe fn l_instOfNatFloat32(mut v_n_319_: *mut LeanObject) -> f32 {
    let mut v___x_320_: f32 = 0.0f32;
    v___x_320_ = lean_float32_of_nat(v_n_319_);
    return v___x_320_;
}
pub unsafe fn l_instOfNatFloat32___boxed(mut v_n_321_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_322_: f32 = 0.0f32;
    let mut v_r_323_: *mut LeanObject = core::ptr::null_mut();
    v_res_322_ = l_instOfNatFloat32(v_n_321_);
    v_r_323_ = lean_box_float32(v_res_322_);
    return v_r_323_;
}
pub unsafe fn l_Nat_toFloat32(mut v_n_324_: *mut LeanObject) -> f32 {
    let mut v___x_325_: f32 = 0.0f32;
    v___x_325_ = lean_float32_of_nat(v_n_324_);
    return v___x_325_;
}
pub unsafe fn l_Nat_toFloat32___boxed(mut v_n_326_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_327_: f32 = 0.0f32;
    let mut v_r_328_: *mut LeanObject = core::ptr::null_mut();
    v_res_327_ = l_Nat_toFloat32(v_n_326_);
    v_r_328_ = lean_box_float32(v_res_327_);
    return v_r_328_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_OfScientific(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Float32(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Log2(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_OfScientific(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_OfScientific(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Float32(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Log2(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_OfScientific(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_OfScientific(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_OfScientific(builtin);
}
