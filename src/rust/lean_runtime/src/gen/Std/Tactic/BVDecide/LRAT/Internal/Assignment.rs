// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Assignment
// Imports: Std.Tactic.BVDecide.LRAT.Internal.Entails Std.Tactic.BVDecide.LRAT.Internal.PosFin Init.Grind
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Entails::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::PosFin::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_dec_le};
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment_default: u8 = 0;
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment: u8 = 0;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment___closed__0_value:
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
    m_fun: l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [112, 111, 115, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [98, 111, 116, 104, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__3_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [117, 110, 97, 115, 115, 105, 103, 110, 101, 100, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___closed__0_value:
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
    m_fun: l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___closed__0_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(
    mut v_x_261_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_261_ {
        0 => {
            let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_262_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_262_;
        }
        1 => {
            let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_263_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_263_;
        }
        2 => {
            let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_264_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_264_;
        }
        _ => {
            let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_265_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_265_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx___boxed(
    mut v_x_266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_267_: u8 = 0;
    let mut v_res_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_267_ = (crate::leanh::lean_unbox(v_x_266_) as u8);
    v_res_268_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_x_boxed_267_);
    return v_res_268_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCtorIdx(
    mut v_x_269_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_270_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_x_269_);
    return v___x_270_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCtorIdx___boxed(
    mut v_x_271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_272_: u8 = 0;
    let mut v_res_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_272_ = (crate::leanh::lean_unbox(v_x_271_) as u8);
    v_res_273_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_toCtorIdx(v_x_4__boxed_272_);
    return v_res_273_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___redArg(
    mut v_k_274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_274_);
    return v_k_274_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___redArg___boxed(
    mut v_k_275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_276_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___redArg(v_k_275_);
    crate::leanh::lean_dec(v_k_275_);
    return v_res_276_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim(
    mut v_motive_277_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_278_: *mut crate::leanh::LeanObject,
    mut v_t_279_: u8,
    mut v_h_280_: *mut crate::leanh::LeanObject,
    mut v_k_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_281_);
    return v_k_281_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim___boxed(
    mut v_motive_282_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_283_: *mut crate::leanh::LeanObject,
    mut v_t_284_: *mut crate::leanh::LeanObject,
    mut v_h_285_: *mut crate::leanh::LeanObject,
    mut v_k_286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_287_: u8 = 0;
    let mut v_res_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_287_ = (crate::leanh::lean_unbox(v_t_284_) as u8);
    v_res_288_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorElim(
        v_motive_282_,
        v_ctorIdx_283_,
        v_t_boxed_287_,
        v_h_285_,
        v_k_286_,
    );
    crate::leanh::lean_dec(v_k_286_);
    crate::leanh::lean_dec(v_ctorIdx_283_);
    return v_res_288_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___redArg(
    mut v_pos_289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_289_);
    return v_pos_289_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___redArg___boxed(
    mut v_pos_290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_291_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___redArg(v_pos_290_);
    crate::leanh::lean_dec(v_pos_290_);
    return v_res_291_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim(
    mut v_motive_292_: *mut crate::leanh::LeanObject,
    mut v_t_293_: u8,
    mut v_h_294_: *mut crate::leanh::LeanObject,
    mut v_pos_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pos_295_);
    return v_pos_295_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim___boxed(
    mut v_motive_296_: *mut crate::leanh::LeanObject,
    mut v_t_297_: *mut crate::leanh::LeanObject,
    mut v_h_298_: *mut crate::leanh::LeanObject,
    mut v_pos_299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_300_: u8 = 0;
    let mut v_res_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_300_ = (crate::leanh::lean_unbox(v_t_297_) as u8);
    v_res_301_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_pos_elim(
        v_motive_296_,
        v_t_boxed_300_,
        v_h_298_,
        v_pos_299_,
    );
    crate::leanh::lean_dec(v_pos_299_);
    return v_res_301_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___redArg(
    mut v_neg_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_neg_302_);
    return v_neg_302_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___redArg___boxed(
    mut v_neg_303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_304_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___redArg(v_neg_303_);
    crate::leanh::lean_dec(v_neg_303_);
    return v_res_304_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim(
    mut v_motive_305_: *mut crate::leanh::LeanObject,
    mut v_t_306_: u8,
    mut v_h_307_: *mut crate::leanh::LeanObject,
    mut v_neg_308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_neg_308_);
    return v_neg_308_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim___boxed(
    mut v_motive_309_: *mut crate::leanh::LeanObject,
    mut v_t_310_: *mut crate::leanh::LeanObject,
    mut v_h_311_: *mut crate::leanh::LeanObject,
    mut v_neg_312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_313_: u8 = 0;
    let mut v_res_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_313_ = (crate::leanh::lean_unbox(v_t_310_) as u8);
    v_res_314_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_neg_elim(
        v_motive_309_,
        v_t_boxed_313_,
        v_h_311_,
        v_neg_312_,
    );
    crate::leanh::lean_dec(v_neg_312_);
    return v_res_314_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___redArg(
    mut v_both_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_both_315_);
    return v_both_315_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___redArg___boxed(
    mut v_both_316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_317_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___redArg(v_both_316_);
    crate::leanh::lean_dec(v_both_316_);
    return v_res_317_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim(
    mut v_motive_318_: *mut crate::leanh::LeanObject,
    mut v_t_319_: u8,
    mut v_h_320_: *mut crate::leanh::LeanObject,
    mut v_both_321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_both_321_);
    return v_both_321_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim___boxed(
    mut v_motive_322_: *mut crate::leanh::LeanObject,
    mut v_t_323_: *mut crate::leanh::LeanObject,
    mut v_h_324_: *mut crate::leanh::LeanObject,
    mut v_both_325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_326_: u8 = 0;
    let mut v_res_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_326_ = (crate::leanh::lean_unbox(v_t_323_) as u8);
    v_res_327_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_both_elim(
        v_motive_322_,
        v_t_boxed_326_,
        v_h_324_,
        v_both_325_,
    );
    crate::leanh::lean_dec(v_both_325_);
    return v_res_327_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___redArg(
    mut v_unassigned_328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unassigned_328_);
    return v_unassigned_328_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___redArg___boxed(
    mut v_unassigned_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_330_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___redArg(v_unassigned_329_);
    crate::leanh::lean_dec(v_unassigned_329_);
    return v_res_330_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim(
    mut v_motive_331_: *mut crate::leanh::LeanObject,
    mut v_t_332_: u8,
    mut v_h_333_: *mut crate::leanh::LeanObject,
    mut v_unassigned_334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unassigned_334_);
    return v_unassigned_334_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim___boxed(
    mut v_motive_335_: *mut crate::leanh::LeanObject,
    mut v_t_336_: *mut crate::leanh::LeanObject,
    mut v_h_337_: *mut crate::leanh::LeanObject,
    mut v_unassigned_338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_339_: u8 = 0;
    let mut v_res_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_339_ = (crate::leanh::lean_unbox(v_t_336_) as u8);
    v_res_340_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_unassigned_elim(
        v_motive_335_,
        v_t_boxed_339_,
        v_h_337_,
        v_unassigned_338_,
    );
    crate::leanh::lean_dec(v_unassigned_338_);
    return v_res_340_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment_default() -> u8 {
    let mut v___x_341_: u8 = 0;
    v___x_341_ = 0;
    return v___x_341_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment() -> u8 {
    let mut v___x_342_: u8 = 0;
    v___x_342_ = 0;
    return v___x_342_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofNat(
    mut v_n_343_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: u8 = 0;
    v___x_344_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_345_ = lean_nat_dec_le(v_n_343_, v___x_344_);
    if v___x_345_ == 0 {
        let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_347_: u8 = 0;
        v___x_346_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_347_ = lean_nat_dec_le(v_n_343_, v___x_346_);
        if v___x_347_ == 0 {
            let mut v___x_348_: u8 = 0;
            v___x_348_ = 3;
            return v___x_348_;
        } else {
            let mut v___x_349_: u8 = 0;
            v___x_349_ = 2;
            return v___x_349_;
        }
    } else {
        let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_351_: u8 = 0;
        v___x_350_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_351_ = lean_nat_dec_le(v_n_343_, v___x_350_);
        if v___x_351_ == 0 {
            let mut v___x_352_: u8 = 0;
            v___x_352_ = 1;
            return v___x_352_;
        } else {
            let mut v___x_353_: u8 = 0;
            v___x_353_ = 0;
            return v___x_353_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofNat___boxed(
    mut v_n_354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_355_: u8 = 0;
    let mut v_r_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_355_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ofNat(v_n_354_);
    crate::leanh::lean_dec(v_n_354_);
    v_r_356_ = crate::leanh::lean_box((v_res_355_) as usize);
    return v_r_356_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqAssignment(
    mut v_x_357_: u8,
    mut v_y_358_: u8,
) -> u8 {
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: u8 = 0;
    v___x_359_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_x_357_);
    v___x_360_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_y_358_);
    v___x_361_ = lean_nat_dec_eq(v___x_359_, v___x_360_);
    crate::leanh::lean_dec(v___x_360_);
    crate::leanh::lean_dec(v___x_359_);
    return v___x_361_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqAssignment___boxed(
    mut v_x_362_: *mut crate::leanh::LeanObject,
    mut v_y_363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_364_: u8 = 0;
    let mut v_y_14__boxed_365_: u8 = 0;
    let mut v_res_366_: u8 = 0;
    let mut v_r_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_364_ = (crate::leanh::lean_unbox(v_x_362_) as u8);
    v_y_14__boxed_365_ = (crate::leanh::lean_unbox(v_y_363_) as u8);
    v_res_366_ = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqAssignment(
        v_x_13__boxed_364_,
        v_y_14__boxed_365_,
    );
    v_r_367_ = crate::leanh::lean_box((v_res_366_) as usize);
    return v_r_367_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq(
    mut v_x_368_: u8,
    mut v_y_369_: u8,
) -> u8 {
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: u8 = 0;
    v___x_370_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_x_368_);
    v___x_371_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_ctorIdx(v_y_369_);
    v___x_372_ = lean_nat_dec_eq(v___x_370_, v___x_371_);
    crate::leanh::lean_dec(v___x_371_);
    crate::leanh::lean_dec(v___x_370_);
    return v___x_372_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq___boxed(
    mut v_x_373_: *mut crate::leanh::LeanObject,
    mut v_y_374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_375_: u8 = 0;
    let mut v_y_18__boxed_376_: u8 = 0;
    let mut v_res_377_: u8 = 0;
    let mut v_r_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_375_ = (crate::leanh::lean_unbox(v_x_373_) as u8);
    v_y_18__boxed_376_ = (crate::leanh::lean_unbox(v_y_374_) as u8);
    v_res_377_ = l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq(
        v_x_17__boxed_375_,
        v_y_18__boxed_376_,
    );
    v_r_378_ = crate::leanh::lean_box((v_res_377_) as usize);
    return v_r_378_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0(
    mut v_a_385_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_a_385_ {
        0 => {
            let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_386_ =
                l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__0;
            return v___x_386_;
        }
        1 => {
            let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_387_ =
                l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__1;
            return v___x_387_;
        }
        2 => {
            let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_388_ =
                l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__2;
            return v___x_388_;
        }
        _ => {
            let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_389_ =
                l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___closed__3;
            return v___x_389_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0___boxed(
    mut v_a_390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_391_: u8 = 0;
    let mut v_res_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_391_ = (crate::leanh::lean_unbox(v_a_390_) as u8);
    v_res_392_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString___lam__0(v_a_boxed_391_);
    return v_res_392_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasPosAssignment(
    mut v_assignment_395_: u8,
) -> u8 {
    match v_assignment_395_ {
        1 => {
            let mut v___x_396_: u8 = 0;
            v___x_396_ = 0;
            return v___x_396_;
        }
        3 => {
            let mut v___x_397_: u8 = 0;
            v___x_397_ = 0;
            return v___x_397_;
        }
        _ => {
            let mut v___x_398_: u8 = 0;
            v___x_398_ = 1;
            return v___x_398_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasPosAssignment___boxed(
    mut v_assignment_399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_assignment_boxed_400_: u8 = 0;
    let mut v_res_401_: u8 = 0;
    let mut v_r_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_assignment_boxed_400_ = (crate::leanh::lean_unbox(v_assignment_399_) as u8);
    v_res_401_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasPosAssignment(v_assignment_boxed_400_);
    v_r_402_ = crate::leanh::lean_box((v_res_401_) as usize);
    return v_r_402_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasNegAssignment(
    mut v_assignment_403_: u8,
) -> u8 {
    match v_assignment_403_ {
        1 => {
            let mut v___x_404_: u8 = 0;
            v___x_404_ = 1;
            return v___x_404_;
        }
        2 => {
            let mut v___x_405_: u8 = 0;
            v___x_405_ = 1;
            return v___x_405_;
        }
        _ => {
            let mut v___x_406_: u8 = 0;
            v___x_406_ = 0;
            return v___x_406_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasNegAssignment___boxed(
    mut v_assignment_407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_assignment_boxed_408_: u8 = 0;
    let mut v_res_409_: u8 = 0;
    let mut v_r_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_assignment_boxed_408_ = (crate::leanh::lean_unbox(v_assignment_407_) as u8);
    v_res_409_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasNegAssignment(v_assignment_boxed_408_);
    v_r_410_ = crate::leanh::lean_box((v_res_409_) as usize);
    return v_r_410_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addPosAssignment(
    mut v_oldAssignment_411_: u8,
) -> u8 {
    match v_oldAssignment_411_ {
        1 => {
            let mut v___x_412_: u8 = 0;
            v___x_412_ = 2;
            return v___x_412_;
        }
        3 => {
            let mut v___x_413_: u8 = 0;
            v___x_413_ = 0;
            return v___x_413_;
        }
        _ => {
            return v_oldAssignment_411_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addPosAssignment___boxed(
    mut v_oldAssignment_414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_oldAssignment_boxed_415_: u8 = 0;
    let mut v_res_416_: u8 = 0;
    let mut v_r_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_oldAssignment_boxed_415_ = (crate::leanh::lean_unbox(v_oldAssignment_414_) as u8);
    v_res_416_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addPosAssignment(v_oldAssignment_boxed_415_);
    v_r_417_ = crate::leanh::lean_box((v_res_416_) as usize);
    return v_r_417_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removePosAssignment(
    mut v_oldAssignment_418_: u8,
) -> u8 {
    match v_oldAssignment_418_ {
        0 => {
            let mut v___x_419_: u8 = 0;
            v___x_419_ = 3;
            return v___x_419_;
        }
        2 => {
            let mut v___x_420_: u8 = 0;
            v___x_420_ = 1;
            return v___x_420_;
        }
        _ => {
            return v_oldAssignment_418_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removePosAssignment___boxed(
    mut v_oldAssignment_421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_oldAssignment_boxed_422_: u8 = 0;
    let mut v_res_423_: u8 = 0;
    let mut v_r_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_oldAssignment_boxed_422_ = (crate::leanh::lean_unbox(v_oldAssignment_421_) as u8);
    v_res_423_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removePosAssignment(
        v_oldAssignment_boxed_422_,
    );
    v_r_424_ = crate::leanh::lean_box((v_res_423_) as usize);
    return v_r_424_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addNegAssignment(
    mut v_oldAssignment_425_: u8,
) -> u8 {
    match v_oldAssignment_425_ {
        0 => {
            let mut v___x_426_: u8 = 0;
            v___x_426_ = 2;
            return v___x_426_;
        }
        3 => {
            let mut v___x_427_: u8 = 0;
            v___x_427_ = 1;
            return v___x_427_;
        }
        _ => {
            return v_oldAssignment_425_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addNegAssignment___boxed(
    mut v_oldAssignment_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_oldAssignment_boxed_429_: u8 = 0;
    let mut v_res_430_: u8 = 0;
    let mut v_r_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_oldAssignment_boxed_429_ = (crate::leanh::lean_unbox(v_oldAssignment_428_) as u8);
    v_res_430_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addNegAssignment(v_oldAssignment_boxed_429_);
    v_r_431_ = crate::leanh::lean_box((v_res_430_) as usize);
    return v_r_431_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeNegAssignment(
    mut v_oldAssignment_432_: u8,
) -> u8 {
    match v_oldAssignment_432_ {
        1 => {
            let mut v___x_433_: u8 = 0;
            v___x_433_ = 3;
            return v___x_433_;
        }
        2 => {
            let mut v___x_434_: u8 = 0;
            v___x_434_ = 0;
            return v___x_434_;
        }
        _ => {
            return v_oldAssignment_432_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeNegAssignment___boxed(
    mut v_oldAssignment_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_oldAssignment_boxed_436_: u8 = 0;
    let mut v_res_437_: u8 = 0;
    let mut v_r_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_oldAssignment_boxed_436_ = (crate::leanh::lean_unbox(v_oldAssignment_435_) as u8);
    v_res_437_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeNegAssignment(
        v_oldAssignment_boxed_436_,
    );
    v_r_438_ = crate::leanh::lean_box((v_res_437_) as usize);
    return v_r_438_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(
    mut v_a_439_: u8,
    mut v_h__1_440_: *mut crate::leanh::LeanObject,
    mut v_h__2_441_: *mut crate::leanh::LeanObject,
    mut v_h__3_442_: *mut crate::leanh::LeanObject,
    mut v_h__4_443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_a_439_ {
        0 => {
            let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_443_);
            crate::leanh::lean_dec(v_h__3_442_);
            crate::leanh::lean_dec(v_h__2_441_);
            v___x_444_ = crate::leanh::lean_box(0);
            v___x_445_ = crate::leanh::lean_apply_1(v_h__1_440_, v___x_444_);
            return v___x_445_;
        }
        1 => {
            let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_443_);
            crate::leanh::lean_dec(v_h__3_442_);
            crate::leanh::lean_dec(v_h__1_440_);
            v___x_446_ = crate::leanh::lean_box(0);
            v___x_447_ = crate::leanh::lean_apply_1(v_h__2_441_, v___x_446_);
            return v___x_447_;
        }
        2 => {
            let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_443_);
            crate::leanh::lean_dec(v_h__2_441_);
            crate::leanh::lean_dec(v_h__1_440_);
            v___x_448_ = crate::leanh::lean_box(0);
            v___x_449_ = crate::leanh::lean_apply_1(v_h__3_442_, v___x_448_);
            return v___x_449_;
        }
        _ => {
            let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_442_);
            crate::leanh::lean_dec(v_h__2_441_);
            crate::leanh::lean_dec(v_h__1_440_);
            v___x_450_ = crate::leanh::lean_box(0);
            v___x_451_ = crate::leanh::lean_apply_1(v_h__4_443_, v___x_450_);
            return v___x_451_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg___boxed(
    mut v_a_452_: *mut crate::leanh::LeanObject,
    mut v_h__1_453_: *mut crate::leanh::LeanObject,
    mut v_h__2_454_: *mut crate::leanh::LeanObject,
    mut v_h__3_455_: *mut crate::leanh::LeanObject,
    mut v_h__4_456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_46__boxed_457_: u8 = 0;
    let mut v_res_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_46__boxed_457_ = (crate::leanh::lean_unbox(v_a_452_) as u8);
    v_res_458_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(v_a_46__boxed_457_, v_h__1_453_, v_h__2_454_, v_h__3_455_, v_h__4_456_);
    return v_res_458_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(
    mut v_motive_459_: *mut crate::leanh::LeanObject,
    mut v_a_460_: u8,
    mut v_h__1_461_: *mut crate::leanh::LeanObject,
    mut v_h__2_462_: *mut crate::leanh::LeanObject,
    mut v_h__3_463_: *mut crate::leanh::LeanObject,
    mut v_h__4_464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_a_460_ {
        0 => {
            let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_464_);
            crate::leanh::lean_dec(v_h__3_463_);
            crate::leanh::lean_dec(v_h__2_462_);
            v___x_465_ = crate::leanh::lean_box(0);
            v___x_466_ = crate::leanh::lean_apply_1(v_h__1_461_, v___x_465_);
            return v___x_466_;
        }
        1 => {
            let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_464_);
            crate::leanh::lean_dec(v_h__3_463_);
            crate::leanh::lean_dec(v_h__1_461_);
            v___x_467_ = crate::leanh::lean_box(0);
            v___x_468_ = crate::leanh::lean_apply_1(v_h__2_462_, v___x_467_);
            return v___x_468_;
        }
        2 => {
            let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_464_);
            crate::leanh::lean_dec(v_h__2_462_);
            crate::leanh::lean_dec(v_h__1_461_);
            v___x_469_ = crate::leanh::lean_box(0);
            v___x_470_ = crate::leanh::lean_apply_1(v_h__3_463_, v___x_469_);
            return v___x_470_;
        }
        _ => {
            let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_463_);
            crate::leanh::lean_dec(v_h__2_462_);
            crate::leanh::lean_dec(v_h__1_461_);
            v___x_471_ = crate::leanh::lean_box(0);
            v___x_472_ = crate::leanh::lean_apply_1(v_h__4_464_, v___x_471_);
            return v___x_472_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___boxed(
    mut v_motive_473_: *mut crate::leanh::LeanObject,
    mut v_a_474_: *mut crate::leanh::LeanObject,
    mut v_h__1_475_: *mut crate::leanh::LeanObject,
    mut v_h__2_476_: *mut crate::leanh::LeanObject,
    mut v_h__3_477_: *mut crate::leanh::LeanObject,
    mut v_h__4_478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_65__boxed_479_: u8 = 0;
    let mut v_res_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_65__boxed_479_ = (crate::leanh::lean_unbox(v_a_474_) as u8);
    v_res_480_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Assignment_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(v_motive_473_, v_a_65__boxed_479_, v_h__1_475_, v_h__2_476_, v_h__3_477_, v_h__4_478_);
    return v_res_480_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(
    mut v_b_481_: u8,
    mut v_a_482_: u8,
) -> u8 {
    if v_b_481_ == 0 {
        match v_a_482_ {
            0 => {
                let mut v___x_483_: u8 = 0;
                v___x_483_ = 2;
                return v___x_483_;
            }
            3 => {
                let mut v___x_484_: u8 = 0;
                v___x_484_ = 1;
                return v___x_484_;
            }
            _ => {
                return v_a_482_;
            }
        }
    } else {
        match v_a_482_ {
            1 => {
                let mut v___x_485_: u8 = 0;
                v___x_485_ = 2;
                return v___x_485_;
            }
            3 => {
                let mut v___x_486_: u8 = 0;
                v___x_486_ = 0;
                return v___x_486_;
            }
            _ => {
                return v_a_482_;
            }
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment___boxed(
    mut v_b_487_: *mut crate::leanh::LeanObject,
    mut v_a_488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_489_: u8 = 0;
    let mut v_a_boxed_490_: u8 = 0;
    let mut v_res_491_: u8 = 0;
    let mut v_r_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_489_ = (crate::leanh::lean_unbox(v_b_487_) as u8);
    v_a_boxed_490_ = (crate::leanh::lean_unbox(v_a_488_) as u8);
    v_res_491_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(
        v_b_boxed_489_,
        v_a_boxed_490_,
    );
    v_r_492_ = crate::leanh::lean_box((v_res_491_) as usize);
    return v_r_492_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(
    mut v_b_493_: u8,
    mut v_a_494_: u8,
) -> u8 {
    if v_b_493_ == 0 {
        match v_a_494_ {
            1 => {
                let mut v___x_495_: u8 = 0;
                v___x_495_ = 3;
                return v___x_495_;
            }
            2 => {
                let mut v___x_496_: u8 = 0;
                v___x_496_ = 0;
                return v___x_496_;
            }
            _ => {
                return v_a_494_;
            }
        }
    } else {
        match v_a_494_ {
            0 => {
                let mut v___x_497_: u8 = 0;
                v___x_497_ = 3;
                return v___x_497_;
            }
            2 => {
                let mut v___x_498_: u8 = 0;
                v___x_498_ = 1;
                return v___x_498_;
            }
            _ => {
                return v_a_494_;
            }
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment___boxed(
    mut v_b_499_: *mut crate::leanh::LeanObject,
    mut v_a_500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_501_: u8 = 0;
    let mut v_a_boxed_502_: u8 = 0;
    let mut v_res_503_: u8 = 0;
    let mut v_r_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_501_ = (crate::leanh::lean_unbox(v_b_499_) as u8);
    v_a_boxed_502_ = (crate::leanh::lean_unbox(v_a_500_) as u8);
    v_res_503_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(
        v_b_boxed_501_,
        v_a_boxed_502_,
    );
    v_r_504_ = crate::leanh::lean_box((v_res_503_) as usize);
    return v_r_504_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(
    mut v_b_505_: u8,
    mut v_a_506_: u8,
) -> u8 {
    if v_b_505_ == 0 {
        match v_a_506_ {
            1 => {
                let mut v___x_507_: u8 = 0;
                v___x_507_ = 1;
                return v___x_507_;
            }
            2 => {
                let mut v___x_508_: u8 = 0;
                v___x_508_ = 1;
                return v___x_508_;
            }
            _ => {
                return v_b_505_;
            }
        }
    } else {
        match v_a_506_ {
            1 => {
                let mut v___x_509_: u8 = 0;
                v___x_509_ = 0;
                return v___x_509_;
            }
            3 => {
                let mut v___x_510_: u8 = 0;
                v___x_510_ = 0;
                return v___x_510_;
            }
            _ => {
                return v_b_505_;
            }
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment___boxed(
    mut v_b_511_: *mut crate::leanh::LeanObject,
    mut v_a_512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_513_: u8 = 0;
    let mut v_a_boxed_514_: u8 = 0;
    let mut v_res_515_: u8 = 0;
    let mut v_r_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_513_ = (crate::leanh::lean_unbox(v_b_511_) as u8);
    v_a_boxed_514_ = (crate::leanh::lean_unbox(v_a_512_) as u8);
    v_res_515_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(
        v_b_boxed_513_,
        v_a_boxed_514_,
    );
    v_r_516_ = crate::leanh::lean_box((v_res_515_) as usize);
    return v_r_516_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instEntailsPosFinArray(
    mut v_n_517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_518_ = crate::leanh::lean_box(0);
    return v___x_518_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instEntailsPosFinArray___boxed(
    mut v_n_519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_520_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_instEntailsPosFinArray(v_n_519_);
    crate::leanh::lean_dec(v_n_519_);
    return v_res_520_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment_default =
        _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment_default();
    l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment =
        _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedAssignment();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_PosFin(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin);
}
