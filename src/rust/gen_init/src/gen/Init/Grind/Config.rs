// Lean compiler output
// Module: Init.Grind.Config
// Imports: Init.Core
use crate::ffi::lean_nat_dec_eq;
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
pub static l_Lean_Grind_instInhabitedConfig_default___closed__0_value:
    leanh::LeanCtorObject<17> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 13
            + 32) as u16,
        other: 13,
        tag: 0,
    },
    m_objs: [
        (((9 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((5 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((8 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((8 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1000 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1000 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((100000 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1000 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1048576 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((10 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        72340168526266368 as *mut leanh::LeanObject,
        72340172821299200 as *mut leanh::LeanObject,
        72340172838076417 as *mut leanh::LeanObject,
        72339073326448897 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_instInhabitedConfig_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instInhabitedConfig_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Grind_instInhabitedConfig_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instInhabitedConfig_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Grind_instInhabitedConfig: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instInhabitedConfig_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_instBEqConfig___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_instBEqConfig_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instBEqConfig___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instBEqConfig___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Grind_instBEqConfig: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instBEqConfig___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(
    mut v_x_191_: *mut leanh::LeanObject,
    mut v_x_192_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_191_) == 0 {
        if leanh::lean_obj_tag(v_x_192_) == 0 {
            let mut v___x_193_: u8 = 0;
            v___x_193_ = 1;
            return v___x_193_;
        } else {
            let mut v___x_194_: u8 = 0;
            v___x_194_ = 0;
            return v___x_194_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_192_) == 0 {
            let mut v___x_195_: u8 = 0;
            v___x_195_ = 0;
            return v___x_195_;
        } else {
            let mut v_val_196_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_197_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_198_: u8 = 0;
            v_val_196_ = leanh::lean_ctor_get(v_x_191_, 0);
            v_val_197_ = leanh::lean_ctor_get(v_x_192_, 0);
            v___x_198_ = lean_nat_dec_eq(v_val_196_, v_val_197_);
            return v___x_198_;
        }
    }
}
pub unsafe fn l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0___boxed(
    mut v_x_199_: *mut leanh::LeanObject,
    mut v_x_200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_201_: u8 = 0;
    let mut v_r_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_201_ =
        l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_x_199_, v_x_200_);
    leanh::lean_dec(v_x_200_);
    leanh::lean_dec(v_x_199_);
    v_r_202_ = leanh::lean_box((v_res_201_) as usize);
    return v_r_202_;
}
pub unsafe fn l_Lean_Grind_instBEqConfig_beq(
    mut v_x_203_: *mut leanh::LeanObject,
    mut v_x_204_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_trace_205_: u8 = 0;
    let mut v_markInstances_206_: u8 = 0;
    let mut v_lax_207_: u8 = 0;
    let mut v_suggestions_208_: u8 = 0;
    let mut v_locals_209_: u8 = 0;
    let mut v_splits_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_genLocal_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_instances_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_matchEqs_215_: u8 = 0;
    let mut v_splitMatch_216_: u8 = 0;
    let mut v_splitIte_217_: u8 = 0;
    let mut v_splitIndPred_218_: u8 = 0;
    let mut v_splitImp_219_: u8 = 0;
    let mut v_canonHeartbeats_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_221_: u8 = 0;
    let mut v_extAll_222_: u8 = 0;
    let mut v_etaStruct_223_: u8 = 0;
    let mut v_funext_224_: u8 = 0;
    let mut v_lookahead_225_: u8 = 0;
    let mut v_verbose_226_: u8 = 0;
    let mut v_clean_227_: u8 = 0;
    let mut v_qlia_228_: u8 = 0;
    let mut v_mbtc_229_: u8 = 0;
    let mut v_zetaDelta_230_: u8 = 0;
    let mut v_zeta_231_: u8 = 0;
    let mut v_ring_232_: u8 = 0;
    let mut v_ringSteps_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringMaxDegree_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linarith_235_: u8 = 0;
    let mut v_lia_236_: u8 = 0;
    let mut v_ac_237_: u8 = 0;
    let mut v_acSteps_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exp_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abstractProof_240_: u8 = 0;
    let mut v_inj_241_: u8 = 0;
    let mut v_order_242_: u8 = 0;
    let mut v_min_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_detailed_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_useSorry_245_: u8 = 0;
    let mut v_revert_246_: u8 = 0;
    let mut v_funCC_247_: u8 = 0;
    let mut v_reducible_248_: u8 = 0;
    let mut v_maxSuggestions_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_250_: u8 = 0;
    let mut v_markInstances_251_: u8 = 0;
    let mut v_lax_252_: u8 = 0;
    let mut v_suggestions_253_: u8 = 0;
    let mut v_locals_254_: u8 = 0;
    let mut v_splits_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_genLocal_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_instances_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_matchEqs_260_: u8 = 0;
    let mut v_splitMatch_261_: u8 = 0;
    let mut v_splitIte_262_: u8 = 0;
    let mut v_splitIndPred_263_: u8 = 0;
    let mut v_splitImp_264_: u8 = 0;
    let mut v_canonHeartbeats_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_266_: u8 = 0;
    let mut v_extAll_267_: u8 = 0;
    let mut v_etaStruct_268_: u8 = 0;
    let mut v_funext_269_: u8 = 0;
    let mut v_lookahead_270_: u8 = 0;
    let mut v_verbose_271_: u8 = 0;
    let mut v_clean_272_: u8 = 0;
    let mut v_qlia_273_: u8 = 0;
    let mut v_mbtc_274_: u8 = 0;
    let mut v_zetaDelta_275_: u8 = 0;
    let mut v_zeta_276_: u8 = 0;
    let mut v_ring_277_: u8 = 0;
    let mut v_ringSteps_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringMaxDegree_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linarith_280_: u8 = 0;
    let mut v_lia_281_: u8 = 0;
    let mut v_ac_282_: u8 = 0;
    let mut v_acSteps_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exp_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abstractProof_285_: u8 = 0;
    let mut v_inj_286_: u8 = 0;
    let mut v_order_287_: u8 = 0;
    let mut v_min_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_detailed_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_useSorry_290_: u8 = 0;
    let mut v_revert_291_: u8 = 0;
    let mut v_funCC_292_: u8 = 0;
    let mut v_reducible_293_: u8 = 0;
    let mut v_maxSuggestions_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: u8 = 0;
    let mut v___x_297_: u8 = 0;
    let mut v___y_300_: u8 = 0;
    let mut v___x_302_: u8 = 0;
    let mut v___x_303_: u8 = 0;
    let mut v___y_306_: u8 = 0;
    let mut v___x_308_: u8 = 0;
    let mut v___x_309_: u8 = 0;
    let mut v___y_312_: u8 = 0;
    let mut v___x_314_: u8 = 0;
    let mut v___x_315_: u8 = 0;
    let mut v___y_327_: u8 = 0;
    let mut v___x_329_: u8 = 0;
    let mut v___y_334_: u8 = 0;
    let mut v___x_336_: u8 = 0;
    let mut v___x_337_: u8 = 0;
    let mut v___x_338_: u8 = 0;
    let mut v___x_339_: u8 = 0;
    let mut v___x_340_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_trace_205_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_markInstances_206_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_lax_207_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 2) as u32,
                );
                v_suggestions_208_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 3) as u32,
                );
                v_locals_209_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 4) as u32,
                );
                v_splits_210_ = leanh::lean_ctor_get(v_x_203_, 0);
                v_ematch_211_ = leanh::lean_ctor_get(v_x_203_, 1);
                v_gen_212_ = leanh::lean_ctor_get(v_x_203_, 2);
                v_genLocal_213_ = leanh::lean_ctor_get(v_x_203_, 3);
                v_instances_214_ = leanh::lean_ctor_get(v_x_203_, 4);
                v_matchEqs_215_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 5) as u32,
                );
                v_splitMatch_216_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 6) as u32,
                );
                v_splitIte_217_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 7) as u32,
                );
                v_splitIndPred_218_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 8) as u32,
                );
                v_splitImp_219_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 9) as u32,
                );
                v_canonHeartbeats_220_ = leanh::lean_ctor_get(v_x_203_, 5);
                v_ext_221_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 10) as u32,
                );
                v_extAll_222_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 11) as u32,
                );
                v_etaStruct_223_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 12) as u32,
                );
                v_funext_224_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 13) as u32,
                );
                v_lookahead_225_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 14) as u32,
                );
                v_verbose_226_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 15) as u32,
                );
                v_clean_227_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 16) as u32,
                );
                v_qlia_228_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 17) as u32,
                );
                v_mbtc_229_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 18) as u32,
                );
                v_zetaDelta_230_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 19) as u32,
                );
                v_zeta_231_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 20) as u32,
                );
                v_ring_232_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 21) as u32,
                );
                v_ringSteps_233_ = leanh::lean_ctor_get(v_x_203_, 6);
                v_ringMaxDegree_234_ = leanh::lean_ctor_get(v_x_203_, 7);
                v_linarith_235_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 22) as u32,
                );
                v_lia_236_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 23) as u32,
                );
                v_ac_237_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 24) as u32,
                );
                v_acSteps_238_ = leanh::lean_ctor_get(v_x_203_, 8);
                v_exp_239_ = leanh::lean_ctor_get(v_x_203_, 9);
                v_abstractProof_240_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 25) as u32,
                );
                v_inj_241_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 26) as u32,
                );
                v_order_242_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 27) as u32,
                );
                v_min_243_ = leanh::lean_ctor_get(v_x_203_, 10);
                v_detailed_244_ = leanh::lean_ctor_get(v_x_203_, 11);
                v_useSorry_245_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 28) as u32,
                );
                v_revert_246_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 29) as u32,
                );
                v_funCC_247_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 30) as u32,
                );
                v_reducible_248_ = leanh::lean_ctor_get_uint8(
                    v_x_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 31) as u32,
                );
                v_maxSuggestions_249_ = leanh::lean_ctor_get(v_x_203_, 12);
                v_trace_250_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_markInstances_251_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_lax_252_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 2) as u32,
                );
                v_suggestions_253_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 3) as u32,
                );
                v_locals_254_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 4) as u32,
                );
                v_splits_255_ = leanh::lean_ctor_get(v_x_204_, 0);
                v_ematch_256_ = leanh::lean_ctor_get(v_x_204_, 1);
                v_gen_257_ = leanh::lean_ctor_get(v_x_204_, 2);
                v_genLocal_258_ = leanh::lean_ctor_get(v_x_204_, 3);
                v_instances_259_ = leanh::lean_ctor_get(v_x_204_, 4);
                v_matchEqs_260_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 5) as u32,
                );
                v_splitMatch_261_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 6) as u32,
                );
                v_splitIte_262_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 7) as u32,
                );
                v_splitIndPred_263_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 8) as u32,
                );
                v_splitImp_264_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 9) as u32,
                );
                v_canonHeartbeats_265_ = leanh::lean_ctor_get(v_x_204_, 5);
                v_ext_266_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 10) as u32,
                );
                v_extAll_267_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 11) as u32,
                );
                v_etaStruct_268_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 12) as u32,
                );
                v_funext_269_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 13) as u32,
                );
                v_lookahead_270_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 14) as u32,
                );
                v_verbose_271_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 15) as u32,
                );
                v_clean_272_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 16) as u32,
                );
                v_qlia_273_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 17) as u32,
                );
                v_mbtc_274_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 18) as u32,
                );
                v_zetaDelta_275_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 19) as u32,
                );
                v_zeta_276_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 20) as u32,
                );
                v_ring_277_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 21) as u32,
                );
                v_ringSteps_278_ = leanh::lean_ctor_get(v_x_204_, 6);
                v_ringMaxDegree_279_ = leanh::lean_ctor_get(v_x_204_, 7);
                v_linarith_280_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 22) as u32,
                );
                v_lia_281_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 23) as u32,
                );
                v_ac_282_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 24) as u32,
                );
                v_acSteps_283_ = leanh::lean_ctor_get(v_x_204_, 8);
                v_exp_284_ = leanh::lean_ctor_get(v_x_204_, 9);
                v_abstractProof_285_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 25) as u32,
                );
                v_inj_286_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 26) as u32,
                );
                v_order_287_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 27) as u32,
                );
                v_min_288_ = leanh::lean_ctor_get(v_x_204_, 10);
                v_detailed_289_ = leanh::lean_ctor_get(v_x_204_, 11);
                v_useSorry_290_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 28) as u32,
                );
                v_revert_291_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 29) as u32,
                );
                v_funCC_292_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 30) as u32,
                );
                v_reducible_293_ = leanh::lean_ctor_get_uint8(
                    v_x_204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 31) as u32,
                );
                v_maxSuggestions_294_ = leanh::lean_ctor_get(v_x_204_, 12);
                if v_trace_205_ == 0 {
                    if v_trace_250_ == 0 {
                        state = 31;
                        continue;
                    } else {
                        return v_trace_205_;
                    }
                } else {
                    if v_trace_250_ == 0 {
                        return v_trace_250_;
                    } else {
                        state = 31;
                        continue;
                    }
                }
            }
            1 => {
                if v_reducible_248_ == 0 {
                    if v_reducible_293_ == 0 {
                        v___x_296_ =
                            l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(
                                v_maxSuggestions_249_,
                                v_maxSuggestions_294_,
                            );
                        return v___x_296_;
                    } else {
                        return v_reducible_248_;
                    }
                } else {
                    if v_reducible_293_ == 0 {
                        return v_reducible_293_;
                    } else {
                        v___x_297_ =
                            l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(
                                v_maxSuggestions_249_,
                                v_maxSuggestions_294_,
                            );
                        return v___x_297_;
                    }
                }
            }
            2 => {
                if v_funCC_247_ == 0 {
                    if v_funCC_292_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        return v_funCC_247_;
                    }
                } else {
                    if v_funCC_292_ == 0 {
                        return v_funCC_292_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                if v___y_300_ == 0 {
                    return v___y_300_;
                } else {
                    if v_revert_246_ == 0 {
                        if v_revert_291_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            return v_revert_246_;
                        }
                    } else {
                        if v_revert_291_ == 0 {
                            return v_revert_291_;
                        } else {
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_302_ = lean_nat_dec_eq(v_min_243_, v_min_288_);
                if v___x_302_ == 0 {
                    return v___x_302_;
                } else {
                    v___x_303_ = lean_nat_dec_eq(v_detailed_244_, v_detailed_289_);
                    if v___x_303_ == 0 {
                        return v___x_303_;
                    } else {
                        if v_useSorry_245_ == 0 {
                            if v_useSorry_290_ == 0 {
                                v___y_300_ = v___x_303_;
                                state = 3;
                                continue;
                            } else {
                                return v_useSorry_245_;
                            }
                        } else {
                            v___y_300_ = v_useSorry_290_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_order_242_ == 0 {
                    if v_order_287_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        return v_order_242_;
                    }
                } else {
                    if v_order_287_ == 0 {
                        return v_order_287_;
                    } else {
                        state = 4;
                        continue;
                    }
                }
            }
            6 => {
                if v___y_306_ == 0 {
                    return v___y_306_;
                } else {
                    if v_inj_241_ == 0 {
                        if v_inj_286_ == 0 {
                            state = 5;
                            continue;
                        } else {
                            return v_inj_241_;
                        }
                    } else {
                        if v_inj_286_ == 0 {
                            return v_inj_286_;
                        } else {
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_308_ = lean_nat_dec_eq(v_acSteps_238_, v_acSteps_283_);
                if v___x_308_ == 0 {
                    return v___x_308_;
                } else {
                    v___x_309_ = lean_nat_dec_eq(v_exp_239_, v_exp_284_);
                    if v___x_309_ == 0 {
                        return v___x_309_;
                    } else {
                        if v_abstractProof_240_ == 0 {
                            if v_abstractProof_285_ == 0 {
                                v___y_306_ = v___x_309_;
                                state = 6;
                                continue;
                            } else {
                                return v_abstractProof_240_;
                            }
                        } else {
                            v___y_306_ = v_abstractProof_285_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            8 => {
                if v_ac_237_ == 0 {
                    if v_ac_282_ == 0 {
                        state = 7;
                        continue;
                    } else {
                        return v_ac_237_;
                    }
                } else {
                    if v_ac_282_ == 0 {
                        return v_ac_282_;
                    } else {
                        state = 7;
                        continue;
                    }
                }
            }
            9 => {
                if v___y_312_ == 0 {
                    return v___y_312_;
                } else {
                    if v_lia_236_ == 0 {
                        if v_lia_281_ == 0 {
                            state = 8;
                            continue;
                        } else {
                            return v_lia_236_;
                        }
                    } else {
                        if v_lia_281_ == 0 {
                            return v_lia_281_;
                        } else {
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            10 => {
                v___x_314_ = lean_nat_dec_eq(v_ringSteps_233_, v_ringSteps_278_);
                if v___x_314_ == 0 {
                    return v___x_314_;
                } else {
                    v___x_315_ = lean_nat_dec_eq(v_ringMaxDegree_234_, v_ringMaxDegree_279_);
                    if v___x_315_ == 0 {
                        return v___x_315_;
                    } else {
                        if v_linarith_235_ == 0 {
                            if v_linarith_280_ == 0 {
                                v___y_312_ = v___x_315_;
                                state = 9;
                                continue;
                            } else {
                                return v_linarith_235_;
                            }
                        } else {
                            v___y_312_ = v_linarith_280_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            11 => {
                if v_ring_232_ == 0 {
                    if v_ring_277_ == 0 {
                        state = 10;
                        continue;
                    } else {
                        return v_ring_232_;
                    }
                } else {
                    if v_ring_277_ == 0 {
                        return v_ring_277_;
                    } else {
                        state = 10;
                        continue;
                    }
                }
            }
            12 => {
                if v_zeta_231_ == 0 {
                    if v_zeta_276_ == 0 {
                        state = 11;
                        continue;
                    } else {
                        return v_zeta_231_;
                    }
                } else {
                    if v_zeta_276_ == 0 {
                        return v_zeta_276_;
                    } else {
                        state = 11;
                        continue;
                    }
                }
            }
            13 => {
                if v_zetaDelta_230_ == 0 {
                    if v_zetaDelta_275_ == 0 {
                        state = 12;
                        continue;
                    } else {
                        return v_zetaDelta_230_;
                    }
                } else {
                    if v_zetaDelta_275_ == 0 {
                        return v_zetaDelta_275_;
                    } else {
                        state = 12;
                        continue;
                    }
                }
            }
            14 => {
                if v_mbtc_229_ == 0 {
                    if v_mbtc_274_ == 0 {
                        state = 13;
                        continue;
                    } else {
                        return v_mbtc_229_;
                    }
                } else {
                    if v_mbtc_274_ == 0 {
                        return v_mbtc_274_;
                    } else {
                        state = 13;
                        continue;
                    }
                }
            }
            15 => {
                if v_qlia_228_ == 0 {
                    if v_qlia_273_ == 0 {
                        state = 14;
                        continue;
                    } else {
                        return v_qlia_228_;
                    }
                } else {
                    if v_qlia_273_ == 0 {
                        return v_qlia_273_;
                    } else {
                        state = 14;
                        continue;
                    }
                }
            }
            16 => {
                if v_clean_227_ == 0 {
                    if v_clean_272_ == 0 {
                        state = 15;
                        continue;
                    } else {
                        return v_clean_227_;
                    }
                } else {
                    if v_clean_272_ == 0 {
                        return v_clean_272_;
                    } else {
                        state = 15;
                        continue;
                    }
                }
            }
            17 => {
                if v_verbose_226_ == 0 {
                    if v_verbose_271_ == 0 {
                        state = 16;
                        continue;
                    } else {
                        return v_verbose_226_;
                    }
                } else {
                    if v_verbose_271_ == 0 {
                        return v_verbose_271_;
                    } else {
                        state = 16;
                        continue;
                    }
                }
            }
            18 => {
                if v_lookahead_225_ == 0 {
                    if v_lookahead_270_ == 0 {
                        state = 17;
                        continue;
                    } else {
                        return v_lookahead_225_;
                    }
                } else {
                    if v_lookahead_270_ == 0 {
                        return v_lookahead_270_;
                    } else {
                        state = 17;
                        continue;
                    }
                }
            }
            19 => {
                if v_funext_224_ == 0 {
                    if v_funext_269_ == 0 {
                        state = 18;
                        continue;
                    } else {
                        return v_funext_224_;
                    }
                } else {
                    if v_funext_269_ == 0 {
                        return v_funext_269_;
                    } else {
                        state = 18;
                        continue;
                    }
                }
            }
            20 => {
                if v_etaStruct_223_ == 0 {
                    if v_etaStruct_268_ == 0 {
                        state = 19;
                        continue;
                    } else {
                        return v_etaStruct_223_;
                    }
                } else {
                    if v_etaStruct_268_ == 0 {
                        return v_etaStruct_268_;
                    } else {
                        state = 19;
                        continue;
                    }
                }
            }
            21 => {
                if v___y_327_ == 0 {
                    return v___y_327_;
                } else {
                    if v_extAll_222_ == 0 {
                        if v_extAll_267_ == 0 {
                            state = 20;
                            continue;
                        } else {
                            return v_extAll_222_;
                        }
                    } else {
                        if v_extAll_267_ == 0 {
                            return v_extAll_267_;
                        } else {
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            22 => {
                v___x_329_ = lean_nat_dec_eq(v_canonHeartbeats_220_, v_canonHeartbeats_265_);
                if v___x_329_ == 0 {
                    return v___x_329_;
                } else {
                    if v_ext_221_ == 0 {
                        if v_ext_266_ == 0 {
                            v___y_327_ = v___x_329_;
                            state = 21;
                            continue;
                        } else {
                            return v_ext_221_;
                        }
                    } else {
                        v___y_327_ = v_ext_266_;
                        state = 21;
                        continue;
                    }
                }
            }
            23 => {
                if v_splitImp_219_ == 0 {
                    if v_splitImp_264_ == 0 {
                        state = 22;
                        continue;
                    } else {
                        return v_splitImp_219_;
                    }
                } else {
                    if v_splitImp_264_ == 0 {
                        return v_splitImp_264_;
                    } else {
                        state = 22;
                        continue;
                    }
                }
            }
            24 => {
                if v_splitIndPred_218_ == 0 {
                    if v_splitIndPred_263_ == 0 {
                        state = 23;
                        continue;
                    } else {
                        return v_splitIndPred_218_;
                    }
                } else {
                    if v_splitIndPred_263_ == 0 {
                        return v_splitIndPred_263_;
                    } else {
                        state = 23;
                        continue;
                    }
                }
            }
            25 => {
                if v_splitIte_217_ == 0 {
                    if v_splitIte_262_ == 0 {
                        state = 24;
                        continue;
                    } else {
                        return v_splitIte_217_;
                    }
                } else {
                    if v_splitIte_262_ == 0 {
                        return v_splitIte_262_;
                    } else {
                        state = 24;
                        continue;
                    }
                }
            }
            26 => {
                if v___y_334_ == 0 {
                    return v___y_334_;
                } else {
                    if v_splitMatch_216_ == 0 {
                        if v_splitMatch_261_ == 0 {
                            state = 25;
                            continue;
                        } else {
                            return v_splitMatch_216_;
                        }
                    } else {
                        if v_splitMatch_261_ == 0 {
                            return v_splitMatch_261_;
                        } else {
                            state = 25;
                            continue;
                        }
                    }
                }
            }
            27 => {
                v___x_336_ = lean_nat_dec_eq(v_splits_210_, v_splits_255_);
                if v___x_336_ == 0 {
                    return v___x_336_;
                } else {
                    v___x_337_ = lean_nat_dec_eq(v_ematch_211_, v_ematch_256_);
                    if v___x_337_ == 0 {
                        return v___x_337_;
                    } else {
                        v___x_338_ = lean_nat_dec_eq(v_gen_212_, v_gen_257_);
                        if v___x_338_ == 0 {
                            return v___x_338_;
                        } else {
                            v___x_339_ = lean_nat_dec_eq(v_genLocal_213_, v_genLocal_258_);
                            if v___x_339_ == 0 {
                                return v___x_339_;
                            } else {
                                v___x_340_ = lean_nat_dec_eq(v_instances_214_, v_instances_259_);
                                if v___x_340_ == 0 {
                                    return v___x_340_;
                                } else {
                                    if v_matchEqs_215_ == 0 {
                                        if v_matchEqs_260_ == 0 {
                                            v___y_334_ = v___x_340_;
                                            state = 26;
                                            continue;
                                        } else {
                                            return v_matchEqs_215_;
                                        }
                                    } else {
                                        v___y_334_ = v_matchEqs_260_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            28 => {
                if v_locals_209_ == 0 {
                    if v_locals_254_ == 0 {
                        state = 27;
                        continue;
                    } else {
                        return v_locals_209_;
                    }
                } else {
                    if v_locals_254_ == 0 {
                        return v_locals_254_;
                    } else {
                        state = 27;
                        continue;
                    }
                }
            }
            29 => {
                if v_suggestions_208_ == 0 {
                    if v_suggestions_253_ == 0 {
                        state = 28;
                        continue;
                    } else {
                        return v_suggestions_208_;
                    }
                } else {
                    if v_suggestions_253_ == 0 {
                        return v_suggestions_253_;
                    } else {
                        state = 28;
                        continue;
                    }
                }
            }
            30 => {
                if v_lax_207_ == 0 {
                    if v_lax_252_ == 0 {
                        state = 29;
                        continue;
                    } else {
                        return v_lax_207_;
                    }
                } else {
                    if v_lax_252_ == 0 {
                        return v_lax_252_;
                    } else {
                        state = 29;
                        continue;
                    }
                }
            }
            31 => {
                if v_markInstances_206_ == 0 {
                    if v_markInstances_251_ == 0 {
                        state = 30;
                        continue;
                    } else {
                        return v_markInstances_206_;
                    }
                } else {
                    if v_markInstances_251_ == 0 {
                        return v_markInstances_251_;
                    } else {
                        state = 30;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_instBEqConfig_beq___boxed(
    mut v_x_345_: *mut leanh::LeanObject,
    mut v_x_346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_347_: u8 = 0;
    let mut v_r_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_347_ = l_Lean_Grind_instBEqConfig_beq(v_x_345_, v_x_346_);
    leanh::lean_dec_ref(v_x_346_);
    leanh::lean_dec_ref(v_x_345_);
    v_r_348_ = leanh::lean_box((v_res_347_) as usize);
    return v_r_348_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Config(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Config(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Config(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Config(builtin);
}