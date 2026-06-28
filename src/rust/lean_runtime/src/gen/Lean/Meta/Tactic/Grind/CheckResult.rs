// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CheckResult
// Imports: Init.Data.Repr Init.MetaTypes
use crate::r#gen::Init::Data::Repr::{
    initialize_Init_Data_Repr, l_Repr_addAppParen, runtime_initialize_Init_Data_Repr,
};
use crate::r#gen::Init::MetaTypes::{initialize_Init_MetaTypes, runtime_initialize_Init_MetaTypes};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_dec_le};
pub static l_Lean_Meta_Grind_instBEqCheckResult___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_instBEqCheckResult_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instBEqCheckResult___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqCheckResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instBEqCheckResult: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqCheckResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instInhabitedCheckResult_default: u8 = 0;
pub static mut l_Lean_Meta_Grind_instInhabitedCheckResult: u8 = 0;
pub static l_Lean_Meta_Grind_instReprCheckResult_repr___closed__0_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 67, 104, 101, 99,
        107, 82, 101, 115, 117, 108, 116, 46, 110, 111, 110, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprCheckResult_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCheckResult_repr___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprCheckResult_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCheckResult_repr___closed__2_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 67, 104, 101, 99,
        107, 82, 101, 115, 117, 108, 116, 46, 112, 114, 111, 103, 114, 101, 115, 115, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprCheckResult_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCheckResult_repr___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprCheckResult_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCheckResult_repr___closed__4_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 67, 104, 101, 99,
        107, 82, 101, 115, 117, 108, 116, 46, 112, 114, 111, 112, 97, 103, 97, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprCheckResult_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCheckResult_repr___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprCheckResult_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCheckResult_repr___closed__6_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 67, 104, 101, 99,
        107, 82, 101, 115, 117, 108, 116, 46, 99, 108, 111, 115, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_instReprCheckResult_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_instReprCheckResult_repr___closed__7_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instReprCheckResult_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCheckResult_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instReprCheckResult___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_instReprCheckResult_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instReprCheckResult___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCheckResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instReprCheckResult: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instReprCheckResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_CheckResult_ctorIdx(
    mut v_x_201_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_201_ {
        0 => {
            let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_202_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_202_;
        }
        1 => {
            let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_203_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_203_;
        }
        2 => {
            let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_204_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_204_;
        }
        _ => {
            let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_205_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_205_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_ctorIdx___boxed(
    mut v_x_206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_207_: u8 = 0;
    let mut v_res_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_207_ = (crate::leanh::lean_unbox(v_x_206_) as u8);
    v_res_208_ = l_Lean_Meta_Grind_CheckResult_ctorIdx(v_x_boxed_207_);
    return v_res_208_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_toCtorIdx(
    mut v_x_209_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_210_ = l_Lean_Meta_Grind_CheckResult_ctorIdx(v_x_209_);
    return v___x_210_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_toCtorIdx___boxed(
    mut v_x_211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_212_: u8 = 0;
    let mut v_res_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_212_ = (crate::leanh::lean_unbox(v_x_211_) as u8);
    v_res_213_ = l_Lean_Meta_Grind_CheckResult_toCtorIdx(v_x_4__boxed_212_);
    return v_res_213_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_ctorElim___redArg(
    mut v_k_214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_214_);
    return v_k_214_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_ctorElim___redArg___boxed(
    mut v_k_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_216_ = l_Lean_Meta_Grind_CheckResult_ctorElim___redArg(v_k_215_);
    crate::leanh::lean_dec(v_k_215_);
    return v_res_216_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_ctorElim(
    mut v_motive_217_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_218_: *mut crate::leanh::LeanObject,
    mut v_t_219_: u8,
    mut v_h_220_: *mut crate::leanh::LeanObject,
    mut v_k_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_221_);
    return v_k_221_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_ctorElim___boxed(
    mut v_motive_222_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_223_: *mut crate::leanh::LeanObject,
    mut v_t_224_: *mut crate::leanh::LeanObject,
    mut v_h_225_: *mut crate::leanh::LeanObject,
    mut v_k_226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_227_: u8 = 0;
    let mut v_res_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_227_ = (crate::leanh::lean_unbox(v_t_224_) as u8);
    v_res_228_ = l_Lean_Meta_Grind_CheckResult_ctorElim(
        v_motive_222_,
        v_ctorIdx_223_,
        v_t_boxed_227_,
        v_h_225_,
        v_k_226_,
    );
    crate::leanh::lean_dec(v_k_226_);
    crate::leanh::lean_dec(v_ctorIdx_223_);
    return v_res_228_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_none_elim___redArg(
    mut v_none_229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_none_229_);
    return v_none_229_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_none_elim___redArg___boxed(
    mut v_none_230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_231_ = l_Lean_Meta_Grind_CheckResult_none_elim___redArg(v_none_230_);
    crate::leanh::lean_dec(v_none_230_);
    return v_res_231_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_none_elim(
    mut v_motive_232_: *mut crate::leanh::LeanObject,
    mut v_t_233_: u8,
    mut v_h_234_: *mut crate::leanh::LeanObject,
    mut v_none_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_none_235_);
    return v_none_235_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_none_elim___boxed(
    mut v_motive_236_: *mut crate::leanh::LeanObject,
    mut v_t_237_: *mut crate::leanh::LeanObject,
    mut v_h_238_: *mut crate::leanh::LeanObject,
    mut v_none_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_240_: u8 = 0;
    let mut v_res_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_240_ = (crate::leanh::lean_unbox(v_t_237_) as u8);
    v_res_241_ = l_Lean_Meta_Grind_CheckResult_none_elim(
        v_motive_236_,
        v_t_boxed_240_,
        v_h_238_,
        v_none_239_,
    );
    crate::leanh::lean_dec(v_none_239_);
    return v_res_241_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_progress_elim___redArg(
    mut v_progress_242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_progress_242_);
    return v_progress_242_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_progress_elim___redArg___boxed(
    mut v_progress_243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_244_ = l_Lean_Meta_Grind_CheckResult_progress_elim___redArg(v_progress_243_);
    crate::leanh::lean_dec(v_progress_243_);
    return v_res_244_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_progress_elim(
    mut v_motive_245_: *mut crate::leanh::LeanObject,
    mut v_t_246_: u8,
    mut v_h_247_: *mut crate::leanh::LeanObject,
    mut v_progress_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_progress_248_);
    return v_progress_248_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_progress_elim___boxed(
    mut v_motive_249_: *mut crate::leanh::LeanObject,
    mut v_t_250_: *mut crate::leanh::LeanObject,
    mut v_h_251_: *mut crate::leanh::LeanObject,
    mut v_progress_252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_253_: u8 = 0;
    let mut v_res_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_253_ = (crate::leanh::lean_unbox(v_t_250_) as u8);
    v_res_254_ = l_Lean_Meta_Grind_CheckResult_progress_elim(
        v_motive_249_,
        v_t_boxed_253_,
        v_h_251_,
        v_progress_252_,
    );
    crate::leanh::lean_dec(v_progress_252_);
    return v_res_254_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg(
    mut v_propagated_255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_propagated_255_);
    return v_propagated_255_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg___boxed(
    mut v_propagated_256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_257_ = l_Lean_Meta_Grind_CheckResult_propagated_elim___redArg(v_propagated_256_);
    crate::leanh::lean_dec(v_propagated_256_);
    return v_res_257_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_propagated_elim(
    mut v_motive_258_: *mut crate::leanh::LeanObject,
    mut v_t_259_: u8,
    mut v_h_260_: *mut crate::leanh::LeanObject,
    mut v_propagated_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_propagated_261_);
    return v_propagated_261_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_propagated_elim___boxed(
    mut v_motive_262_: *mut crate::leanh::LeanObject,
    mut v_t_263_: *mut crate::leanh::LeanObject,
    mut v_h_264_: *mut crate::leanh::LeanObject,
    mut v_propagated_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_266_: u8 = 0;
    let mut v_res_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_266_ = (crate::leanh::lean_unbox(v_t_263_) as u8);
    v_res_267_ = l_Lean_Meta_Grind_CheckResult_propagated_elim(
        v_motive_262_,
        v_t_boxed_266_,
        v_h_264_,
        v_propagated_265_,
    );
    crate::leanh::lean_dec(v_propagated_265_);
    return v_res_267_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_closed_elim___redArg(
    mut v_closed_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_closed_268_);
    return v_closed_268_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_closed_elim___redArg___boxed(
    mut v_closed_269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_270_ = l_Lean_Meta_Grind_CheckResult_closed_elim___redArg(v_closed_269_);
    crate::leanh::lean_dec(v_closed_269_);
    return v_res_270_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_closed_elim(
    mut v_motive_271_: *mut crate::leanh::LeanObject,
    mut v_t_272_: u8,
    mut v_h_273_: *mut crate::leanh::LeanObject,
    mut v_closed_274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_closed_274_);
    return v_closed_274_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_closed_elim___boxed(
    mut v_motive_275_: *mut crate::leanh::LeanObject,
    mut v_t_276_: *mut crate::leanh::LeanObject,
    mut v_h_277_: *mut crate::leanh::LeanObject,
    mut v_closed_278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_279_: u8 = 0;
    let mut v_res_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_279_ = (crate::leanh::lean_unbox(v_t_276_) as u8);
    v_res_280_ = l_Lean_Meta_Grind_CheckResult_closed_elim(
        v_motive_275_,
        v_t_boxed_279_,
        v_h_277_,
        v_closed_278_,
    );
    crate::leanh::lean_dec(v_closed_278_);
    return v_res_280_;
}
pub unsafe fn l_Lean_Meta_Grind_instBEqCheckResult_beq(mut v_x_281_: u8, mut v_y_282_: u8) -> u8 {
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: u8 = 0;
    v___x_283_ = l_Lean_Meta_Grind_CheckResult_ctorIdx(v_x_281_);
    v___x_284_ = l_Lean_Meta_Grind_CheckResult_ctorIdx(v_y_282_);
    v___x_285_ = lean_nat_dec_eq(v___x_283_, v___x_284_);
    crate::leanh::lean_dec(v___x_284_);
    crate::leanh::lean_dec(v___x_283_);
    return v___x_285_;
}
pub unsafe fn l_Lean_Meta_Grind_instBEqCheckResult_beq___boxed(
    mut v_x_286_: *mut crate::leanh::LeanObject,
    mut v_y_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_288_: u8 = 0;
    let mut v_y_18__boxed_289_: u8 = 0;
    let mut v_res_290_: u8 = 0;
    let mut v_r_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_288_ = (crate::leanh::lean_unbox(v_x_286_) as u8);
    v_y_18__boxed_289_ = (crate::leanh::lean_unbox(v_y_287_) as u8);
    v_res_290_ = l_Lean_Meta_Grind_instBEqCheckResult_beq(v_x_17__boxed_288_, v_y_18__boxed_289_);
    v_r_291_ = crate::leanh::lean_box((v_res_290_) as usize);
    return v_r_291_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCheckResult_default() -> u8 {
    let mut v___x_294_: u8 = 0;
    v___x_294_ = 0;
    return v___x_294_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedCheckResult() -> u8 {
    let mut v___x_295_: u8 = 0;
    v___x_295_ = 0;
    return v___x_295_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_308_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_309_ = lean_nat_to_int(v___x_308_);
    return v___x_309_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_310_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_311_ = lean_nat_to_int(v___x_310_);
    return v___x_311_;
}
pub unsafe fn l_Lean_Meta_Grind_instReprCheckResult_repr(
    mut v_x_312_: u8,
    mut v_prec_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: u8 = 0;
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: u8 = 0;
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: u8 = 0;
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: u8 = 0;
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: u8 = 0;
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: u8 = 0;
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: u8 = 0;
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: u8 = 0;
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_312_ {
                0 => {
                    v___x_342_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_343_ = lean_nat_dec_le(v___x_342_, v_prec_313_);
                    if v___x_343_ == 0 {
                        v___x_344_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once
                            ),
                            _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8,
                        );
                        v___y_315_ = v___x_344_;
                        state = 1;
                        continue;
                    } else {
                        v___x_345_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once
                            ),
                            _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9,
                        );
                        v___y_315_ = v___x_345_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_346_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_347_ = lean_nat_dec_le(v___x_346_, v_prec_313_);
                    if v___x_347_ == 0 {
                        v___x_348_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once
                            ),
                            _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8,
                        );
                        v___y_322_ = v___x_348_;
                        state = 2;
                        continue;
                    } else {
                        v___x_349_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once
                            ),
                            _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9,
                        );
                        v___y_322_ = v___x_349_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_350_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_351_ = lean_nat_dec_le(v___x_350_, v_prec_313_);
                    if v___x_351_ == 0 {
                        v___x_352_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once
                            ),
                            _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8,
                        );
                        v___y_329_ = v___x_352_;
                        state = 3;
                        continue;
                    } else {
                        v___x_353_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once
                            ),
                            _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9,
                        );
                        v___y_329_ = v___x_353_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_354_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_355_ = lean_nat_dec_le(v___x_354_, v_prec_313_);
                    if v___x_355_ == 0 {
                        v___x_356_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8_once
                            ),
                            _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__8,
                        );
                        v___y_336_ = v___x_356_;
                        state = 4;
                        continue;
                    } else {
                        v___x_357_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9_once
                            ),
                            _init_l_Lean_Meta_Grind_instReprCheckResult_repr___closed__9,
                        );
                        v___y_336_ = v___x_357_;
                        state = 4;
                        continue;
                    }
                }
            },
            1 => {
                v___x_316_ = l_Lean_Meta_Grind_instReprCheckResult_repr___closed__1;
                crate::leanh::lean_inc(v___y_315_);
                v___x_317_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_317_, 0, v___y_315_);
                crate::leanh::lean_ctor_set(v___x_317_, 1, v___x_316_);
                v___x_318_ = 0;
                v___x_319_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_319_, 0, v___x_317_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_319_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_318_,
                );
                v___x_320_ = l_Repr_addAppParen(v___x_319_, v_prec_313_);
                return v___x_320_;
            }
            2 => {
                v___x_323_ = l_Lean_Meta_Grind_instReprCheckResult_repr___closed__3;
                crate::leanh::lean_inc(v___y_322_);
                v___x_324_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_324_, 0, v___y_322_);
                crate::leanh::lean_ctor_set(v___x_324_, 1, v___x_323_);
                v___x_325_ = 0;
                v___x_326_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_326_, 0, v___x_324_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_326_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_325_,
                );
                v___x_327_ = l_Repr_addAppParen(v___x_326_, v_prec_313_);
                return v___x_327_;
            }
            3 => {
                v___x_330_ = l_Lean_Meta_Grind_instReprCheckResult_repr___closed__5;
                crate::leanh::lean_inc(v___y_329_);
                v___x_331_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_331_, 0, v___y_329_);
                crate::leanh::lean_ctor_set(v___x_331_, 1, v___x_330_);
                v___x_332_ = 0;
                v___x_333_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_333_, 0, v___x_331_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_333_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_332_,
                );
                v___x_334_ = l_Repr_addAppParen(v___x_333_, v_prec_313_);
                return v___x_334_;
            }
            4 => {
                v___x_337_ = l_Lean_Meta_Grind_instReprCheckResult_repr___closed__7;
                crate::leanh::lean_inc(v___y_336_);
                v___x_338_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_338_, 0, v___y_336_);
                crate::leanh::lean_ctor_set(v___x_338_, 1, v___x_337_);
                v___x_339_ = 0;
                v___x_340_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_340_, 0, v___x_338_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_340_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_339_,
                );
                v___x_341_ = l_Repr_addAppParen(v___x_340_, v_prec_313_);
                return v___x_341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_instReprCheckResult_repr___boxed(
    mut v_x_358_: *mut crate::leanh::LeanObject,
    mut v_prec_359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_233__boxed_360_: u8 = 0;
    let mut v_res_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_233__boxed_360_ = (crate::leanh::lean_unbox(v_x_358_) as u8);
    v_res_361_ = l_Lean_Meta_Grind_instReprCheckResult_repr(v_x_233__boxed_360_, v_prec_359_);
    crate::leanh::lean_dec(v_prec_359_);
    return v_res_361_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_lt(
    mut v_r_u2081_364_: u8,
    mut v_r_u2082_365_: u8,
) -> u8 {
    match v_r_u2082_365_ {
        0 => {
            let mut v___x_366_: u8 = 0;
            v___x_366_ = 0;
            return v___x_366_;
        }
        1 => match v_r_u2081_364_ {
            0 => {
                let mut v___x_367_: u8 = 0;
                v___x_367_ = 1;
                return v___x_367_;
            }
            1 => {
                let mut v___x_368_: u8 = 0;
                v___x_368_ = 0;
                return v___x_368_;
            }
            2 => {
                let mut v___x_369_: u8 = 0;
                v___x_369_ = 0;
                return v___x_369_;
            }
            _ => {
                let mut v___x_370_: u8 = 0;
                v___x_370_ = 0;
                return v___x_370_;
            }
        },
        2 => match v_r_u2081_364_ {
            0 => {
                let mut v___x_371_: u8 = 0;
                v___x_371_ = 1;
                return v___x_371_;
            }
            1 => {
                let mut v___x_372_: u8 = 0;
                v___x_372_ = 1;
                return v___x_372_;
            }
            2 => {
                let mut v___x_373_: u8 = 0;
                v___x_373_ = 0;
                return v___x_373_;
            }
            _ => {
                let mut v___x_374_: u8 = 0;
                v___x_374_ = 0;
                return v___x_374_;
            }
        },
        _ => {
            if v_r_u2081_364_ == 3 {
                let mut v___x_375_: u8 = 0;
                v___x_375_ = 0;
                return v___x_375_;
            } else {
                let mut v___x_376_: u8 = 0;
                v___x_376_ = 1;
                return v___x_376_;
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_lt___boxed(
    mut v_r_u2081_377_: *mut crate::leanh::LeanObject,
    mut v_r_u2082_378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_u2081_boxed_379_: u8 = 0;
    let mut v_r_u2082_boxed_380_: u8 = 0;
    let mut v_res_381_: u8 = 0;
    let mut v_r_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_u2081_boxed_379_ = (crate::leanh::lean_unbox(v_r_u2081_377_) as u8);
    v_r_u2082_boxed_380_ = (crate::leanh::lean_unbox(v_r_u2082_378_) as u8);
    v_res_381_ = l_Lean_Meta_Grind_CheckResult_lt(v_r_u2081_boxed_379_, v_r_u2082_boxed_380_);
    v_r_382_ = crate::leanh::lean_box((v_res_381_) as usize);
    return v_r_382_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_le(
    mut v_r_u2081_383_: u8,
    mut v_r_u2082_384_: u8,
) -> u8 {
    let mut v___x_385_: u8 = 0;
    v___x_385_ = l_Lean_Meta_Grind_instBEqCheckResult_beq(v_r_u2081_383_, v_r_u2082_384_);
    if v___x_385_ == 0 {
        let mut v___x_386_: u8 = 0;
        v___x_386_ = l_Lean_Meta_Grind_CheckResult_lt(v_r_u2081_383_, v_r_u2082_384_);
        return v___x_386_;
    } else {
        return v___x_385_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_le___boxed(
    mut v_r_u2081_387_: *mut crate::leanh::LeanObject,
    mut v_r_u2082_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_u2081_boxed_389_: u8 = 0;
    let mut v_r_u2082_boxed_390_: u8 = 0;
    let mut v_res_391_: u8 = 0;
    let mut v_r_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_u2081_boxed_389_ = (crate::leanh::lean_unbox(v_r_u2081_387_) as u8);
    v_r_u2082_boxed_390_ = (crate::leanh::lean_unbox(v_r_u2082_388_) as u8);
    v_res_391_ = l_Lean_Meta_Grind_CheckResult_le(v_r_u2081_boxed_389_, v_r_u2082_boxed_390_);
    v_r_392_ = crate::leanh::lean_box((v_res_391_) as usize);
    return v_r_392_;
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_join(
    mut v_r_u2081_393_: u8,
    mut v_r_u2082_394_: u8,
) -> u8 {
    match v_r_u2081_393_ {
        0 => {
            return v_r_u2082_394_;
        }
        1 => match v_r_u2082_394_ {
            0 => {
                return v_r_u2081_393_;
            }
            1 => {
                return v_r_u2082_394_;
            }
            2 => {
                return v_r_u2082_394_;
            }
            _ => {
                return v_r_u2082_394_;
            }
        },
        2 => match v_r_u2082_394_ {
            0 => {
                return v_r_u2081_393_;
            }
            1 => {
                return v_r_u2081_393_;
            }
            2 => {
                return v_r_u2082_394_;
            }
            _ => {
                return v_r_u2082_394_;
            }
        },
        _ => {
            if v_r_u2082_394_ == 3 {
                return v_r_u2082_394_;
            } else {
                return v_r_u2081_393_;
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_CheckResult_join___boxed(
    mut v_r_u2081_395_: *mut crate::leanh::LeanObject,
    mut v_r_u2082_396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_u2081_boxed_397_: u8 = 0;
    let mut v_r_u2082_boxed_398_: u8 = 0;
    let mut v_res_399_: u8 = 0;
    let mut v_r_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_u2081_boxed_397_ = (crate::leanh::lean_unbox(v_r_u2081_395_) as u8);
    v_r_u2082_boxed_398_ = (crate::leanh::lean_unbox(v_r_u2082_396_) as u8);
    v_res_399_ = l_Lean_Meta_Grind_CheckResult_join(v_r_u2081_boxed_397_, v_r_u2082_boxed_398_);
    v_r_400_ = crate::leanh::lean_box((v_res_399_) as usize);
    return v_r_400_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_CheckResult(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_instInhabitedCheckResult_default =
        _init_l_Lean_Meta_Grind_instInhabitedCheckResult_default();
    l_Lean_Meta_Grind_instInhabitedCheckResult = _init_l_Lean_Meta_Grind_instInhabitedCheckResult();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_CheckResult(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_MetaTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_CheckResult(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_MetaTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_CheckResult(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_CheckResult(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_CheckResult(builtin);
}
