// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.ToIntInfo
// Imports: Lean.Meta.Tactic.Grind.Arith.Util Lean.Meta.LitValues
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_emod, lean_int_sub, lean_nat_to_int, lean_st_ref_get,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_mkIntAdd, l_Lean_mkIntLit, l_Lean_mkIntMod,
    l_Lean_mkIntSub,
};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::LitValues::{
    initialize_Lean_Meta_LitValues, l_Lean_Meta_getIntValue_x3f,
    runtime_initialize_Lean_Meta_LitValues,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Util,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util,
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms_default___closed__0_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__0_value
        ) as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__1_value:
    leanh::LeanStringObject<76> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 76,
    m_capacity: 76,
    m_length: 75,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114,
        114, 111, 114, 44, 32, 96, 46, 99, 105, 96, 32, 105, 110, 116, 101, 114, 118, 97, 108, 32,
        115, 117, 112, 112, 111, 114, 116, 32, 104, 97, 115, 32, 110, 111, 116, 32, 98, 101, 101,
        110, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 32, 121, 101, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__3_value:
    leanh::LeanStringObject<76> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 76,
    m_capacity: 76,
    m_length: 75,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114,
        114, 111, 114, 44, 32, 96, 46, 105, 111, 96, 32, 105, 110, 116, 101, 114, 118, 97, 108, 32,
        115, 117, 112, 112, 111, 114, 116, 32, 104, 97, 115, 32, 110, 111, 116, 32, 98, 101, 101,
        110, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 32, 121, 101, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_286_ = leanh::lean_box(0);
    v___x_287_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__1;
    v___x_288_ = l_Lean_Expr_const___override(v___x_287_, v___x_286_);
    return v___x_288_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_289_ = leanh::lean_box(0);
    v___x_290_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2,
    );
    v___x_291_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_291_, 0, v___x_290_);
    leanh::lean_ctor_set(v___x_291_, 1, v___x_289_);
    return v___x_291_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default()
-> *mut leanh::LeanObject {
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_292_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__3,
    );
    return v___x_292_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound()
-> *mut leanh::LeanObject {
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_293_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default;
    return v___x_293_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isNumeral(
    mut v_b_294_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_ival_x3f_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ival_x3f_295_ = leanh::lean_ctor_get(v_b_294_, 1);
    if leanh::lean_obj_tag(v_ival_x3f_295_) == 0 {
        let mut v___x_296_: u8 = 0;
        v___x_296_ = 0;
        return v___x_296_;
    } else {
        let mut v___x_297_: u8 = 0;
        v___x_297_ = 1;
        return v___x_297_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isNumeral___boxed(
    mut v_b_298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_299_: u8 = 0;
    let mut v_r_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_299_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isNumeral(v_b_298_);
    leanh::lean_dec_ref(v_b_298_);
    v_r_300_ = leanh::lean_box((v_res_299_) as usize);
    return v_r_300_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorIdx(
    mut v_x_301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_301_) {
        0 => {
            let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_302_ = leanh::lean_unsigned_to_nat(0);
            return v___x_302_;
        }
        1 => {
            let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_303_ = leanh::lean_unsigned_to_nat(1);
            return v___x_303_;
        }
        2 => {
            let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_304_ = leanh::lean_unsigned_to_nat(2);
            return v___x_304_;
        }
        _ => {
            let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_305_ = leanh::lean_unsigned_to_nat(3);
            return v___x_305_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorIdx___boxed(
    mut v_x_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_307_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorIdx(v_x_306_);
    leanh::lean_dec(v_x_306_);
    return v_res_307_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(
    mut v_t_308_: *mut leanh::LeanObject,
    mut v_k_309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_308_) {
        0 => {
            let mut v_lo_310_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_hi_311_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lo_310_ = leanh::lean_ctor_get(v_t_308_, 0);
            leanh::lean_inc_ref(v_lo_310_);
            v_hi_311_ = leanh::lean_ctor_get(v_t_308_, 1);
            leanh::lean_inc_ref(v_hi_311_);
            leanh::lean_dec_ref_known(v_t_308_, 2);
            v___x_312_ = leanh::lean_apply_2(v_k_309_, v_lo_310_, v_hi_311_);
            return v___x_312_;
        }
        3 => {
            return v_k_309_;
        }
        _ => {
            let mut v_lo_313_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lo_313_ = leanh::lean_ctor_get(v_t_308_, 0);
            leanh::lean_inc_ref(v_lo_313_);
            leanh::lean_dec(v_t_308_);
            v___x_314_ = leanh::lean_apply_1(v_k_309_, v_lo_313_);
            return v___x_314_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim(
    mut v_motive_315_: *mut leanh::LeanObject,
    mut v_ctorIdx_316_: *mut leanh::LeanObject,
    mut v_t_317_: *mut leanh::LeanObject,
    mut v_h_318_: *mut leanh::LeanObject,
    mut v_k_319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_320_ =
        l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_317_, v_k_319_);
    return v___x_320_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___boxed(
    mut v_motive_321_: *mut leanh::LeanObject,
    mut v_ctorIdx_322_: *mut leanh::LeanObject,
    mut v_t_323_: *mut leanh::LeanObject,
    mut v_h_324_: *mut leanh::LeanObject,
    mut v_k_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim(
        v_motive_321_,
        v_ctorIdx_322_,
        v_t_323_,
        v_h_324_,
        v_k_325_,
    );
    leanh::lean_dec(v_ctorIdx_322_);
    return v_res_326_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_co_elim___redArg(
    mut v_t_327_: *mut leanh::LeanObject,
    mut v_co_328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_329_ =
        l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_327_, v_co_328_);
    return v___x_329_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_co_elim(
    mut v_motive_330_: *mut leanh::LeanObject,
    mut v_t_331_: *mut leanh::LeanObject,
    mut v_h_332_: *mut leanh::LeanObject,
    mut v_co_333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_334_ =
        l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_331_, v_co_333_);
    return v___x_334_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ci_elim___redArg(
    mut v_t_335_: *mut leanh::LeanObject,
    mut v_ci_336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_337_ =
        l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_335_, v_ci_336_);
    return v___x_337_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ci_elim(
    mut v_motive_338_: *mut leanh::LeanObject,
    mut v_t_339_: *mut leanh::LeanObject,
    mut v_h_340_: *mut leanh::LeanObject,
    mut v_ci_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ =
        l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_339_, v_ci_341_);
    return v___x_342_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_io_elim___redArg(
    mut v_t_343_: *mut leanh::LeanObject,
    mut v_io_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_345_ =
        l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_343_, v_io_344_);
    return v___x_345_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_io_elim(
    mut v_motive_346_: *mut leanh::LeanObject,
    mut v_t_347_: *mut leanh::LeanObject,
    mut v_h_348_: *mut leanh::LeanObject,
    mut v_io_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ =
        l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_347_, v_io_349_);
    return v___x_350_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ii_elim___redArg(
    mut v_t_351_: *mut leanh::LeanObject,
    mut v_ii_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_353_ =
        l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_351_, v_ii_352_);
    return v___x_353_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ii_elim(
    mut v_motive_354_: *mut leanh::LeanObject,
    mut v_t_355_: *mut leanh::LeanObject,
    mut v_h_356_: *mut leanh::LeanObject,
    mut v_ii_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ =
        l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_ctorElim___redArg(v_t_355_, v_ii_357_);
    return v___x_358_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_359_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default;
    v___x_360_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_360_, 0, v___x_359_);
    leanh::lean_ctor_set(v___x_360_, 1, v___x_359_);
    return v___x_360_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default()
-> *mut leanh::LeanObject {
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_361_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default___closed__0);
    return v___x_361_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval()
-> *mut leanh::LeanObject {
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default;
    return v___x_362_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_isFinite(
    mut v_i_363_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_i_363_) {
        0 => {
            let mut v___x_364_: u8 = 0;
            v___x_364_ = 1;
            return v___x_364_;
        }
        3 => {
            let mut v___x_365_: u8 = 0;
            v___x_365_ = 0;
            return v___x_365_;
        }
        _ => {
            let mut v___x_366_: u8 = 0;
            v___x_366_ = 0;
            return v___x_366_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_isFinite___boxed(
    mut v_i_367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_368_: u8 = 0;
    let mut v_r_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_368_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_isFinite(v_i_367_);
    leanh::lean_dec(v_i_367_);
    v_r_369_ = leanh::lean_box((v_res_368_) as usize);
    return v_r_369_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_lo_x3f(
    mut v_i_370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lo_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_376_: u8 = 0;
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_380_: u8 = 0;
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_i_370_) {
                0 => {
                    v_lo_371_ = leanh::lean_ctor_get(v_i_370_, 0);
                    leanh::lean_inc_ref(v_lo_371_);
                    leanh::lean_dec_ref_known(v_i_370_, 2);
                    v___x_372_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_372_, 0, v_lo_371_);
                    return v___x_372_;
                }
                1 => {
                    v_lo_373_ = leanh::lean_ctor_get(v_i_370_, 0);
                    v_isSharedCheck_380_ = (!leanh::lean_is_exclusive(v_i_370_)) as u8;
                    if v_isSharedCheck_380_ == 0 {
                        v___x_375_ = v_i_370_;
                        v_isShared_376_ = v_isSharedCheck_380_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_lo_373_);
                        leanh::lean_dec(v_i_370_);
                        v___x_375_ = leanh::lean_box(0);
                        v_isShared_376_ = v_isSharedCheck_380_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_i_370_);
                    v___x_381_ = leanh::lean_box(0);
                    return v___x_381_;
                }
            },
            1 => {
                if v_isShared_376_ == 0 {
                    v___x_378_ = v___x_375_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_379_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_379_, 0, v_lo_373_);
                    v___x_378_ = v_reuseFailAlloc_379_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_hi_x3f(
    mut v_i_382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hi_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hi_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_388_: u8 = 0;
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_392_: u8 = 0;
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_i_382_) {
                0 => {
                    v_hi_383_ = leanh::lean_ctor_get(v_i_382_, 1);
                    leanh::lean_inc_ref(v_hi_383_);
                    leanh::lean_dec_ref_known(v_i_382_, 2);
                    v___x_384_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_384_, 0, v_hi_383_);
                    return v___x_384_;
                }
                2 => {
                    v_hi_385_ = leanh::lean_ctor_get(v_i_382_, 0);
                    v_isSharedCheck_392_ = (!leanh::lean_is_exclusive(v_i_382_)) as u8;
                    if v_isSharedCheck_392_ == 0 {
                        v___x_387_ = v_i_382_;
                        v_isShared_388_ = v_isSharedCheck_392_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_hi_385_);
                        leanh::lean_dec(v_i_382_);
                        v___x_387_ = leanh::lean_box(0);
                        v_isShared_388_ = v_isSharedCheck_392_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_i_382_);
                    v___x_393_ = leanh::lean_box(0);
                    return v___x_393_;
                }
            },
            1 => {
                if v_isShared_388_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_387_, 1);
                    v___x_390_ = v___x_387_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_391_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_391_, 0, v_hi_385_);
                    v___x_390_ = v_reuseFailAlloc_391_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_390_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0_spec__0(
    mut v_msgData_394_: *mut leanh::LeanObject,
    mut v___y_395_: *mut leanh::LeanObject,
    mut v___y_396_: *mut leanh::LeanObject,
    mut v___y_397_: *mut leanh::LeanObject,
    mut v___y_398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_400_ = lean_st_ref_get(v___y_398_);
    v_env_401_ = leanh::lean_ctor_get(v___x_400_, 0);
    leanh::lean_inc_ref(v_env_401_);
    leanh::lean_dec(v___x_400_);
    v___x_402_ = lean_st_ref_get(v___y_396_);
    v_mctx_403_ = leanh::lean_ctor_get(v___x_402_, 0);
    leanh::lean_inc_ref(v_mctx_403_);
    leanh::lean_dec(v___x_402_);
    v_lctx_404_ = leanh::lean_ctor_get(v___y_395_, 2);
    v_options_405_ = leanh::lean_ctor_get(v___y_397_, 2);
    leanh::lean_inc_ref(v_options_405_);
    leanh::lean_inc_ref(v_lctx_404_);
    v___x_406_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_406_, 0, v_env_401_);
    leanh::lean_ctor_set(v___x_406_, 1, v_mctx_403_);
    leanh::lean_ctor_set(v___x_406_, 2, v_lctx_404_);
    leanh::lean_ctor_set(v___x_406_, 3, v_options_405_);
    v___x_407_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_407_, 0, v___x_406_);
    leanh::lean_ctor_set(v___x_407_, 1, v_msgData_394_);
    v___x_408_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_408_, 0, v___x_407_);
    return v___x_408_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0_spec__0___boxed(
    mut v_msgData_409_: *mut leanh::LeanObject,
    mut v___y_410_: *mut leanh::LeanObject,
    mut v___y_411_: *mut leanh::LeanObject,
    mut v___y_412_: *mut leanh::LeanObject,
    mut v___y_413_: *mut leanh::LeanObject,
    mut v___y_414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_415_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0_spec__0(v_msgData_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
    leanh::lean_dec(v___y_413_);
    leanh::lean_dec_ref(v___y_412_);
    leanh::lean_dec(v___y_411_);
    leanh::lean_dec_ref(v___y_410_);
    return v_res_415_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___redArg(
    mut v_msg_416_: *mut leanh::LeanObject,
    mut v___y_417_: *mut leanh::LeanObject,
    mut v___y_418_: *mut leanh::LeanObject,
    mut v___y_419_: *mut leanh::LeanObject,
    mut v___y_420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_427_: u8 = 0;
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_432_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_422_ = leanh::lean_ctor_get(v___y_419_, 5);
                v___x_423_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0_spec__0(v_msg_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
                v_a_424_ = leanh::lean_ctor_get(v___x_423_, 0);
                v_isSharedCheck_432_ = (!leanh::lean_is_exclusive(v___x_423_)) as u8;
                if v_isSharedCheck_432_ == 0 {
                    v___x_426_ = v___x_423_;
                    v_isShared_427_ = v_isSharedCheck_432_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_424_);
                    leanh::lean_dec(v___x_423_);
                    v___x_426_ = leanh::lean_box(0);
                    v_isShared_427_ = v_isSharedCheck_432_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_422_);
                v___x_428_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_428_, 0, v_ref_422_);
                leanh::lean_ctor_set(v___x_428_, 1, v_a_424_);
                if v_isShared_427_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_426_, 1);
                    leanh::lean_ctor_set(v___x_426_, 0, v___x_428_);
                    v___x_430_ = v___x_426_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_431_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
                    v___x_430_ = v_reuseFailAlloc_431_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___redArg___boxed(
    mut v_msg_433_: *mut leanh::LeanObject,
    mut v___y_434_: *mut leanh::LeanObject,
    mut v___y_435_: *mut leanh::LeanObject,
    mut v___y_436_: *mut leanh::LeanObject,
    mut v___y_437_: *mut leanh::LeanObject,
    mut v___y_438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_439_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___redArg(v_msg_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
    leanh::lean_dec(v___y_437_);
    leanh::lean_dec_ref(v___y_436_);
    leanh::lean_dec(v___y_435_);
    leanh::lean_dec_ref(v___y_434_);
    return v_res_439_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_440_ = leanh::lean_unsigned_to_nat(0);
    v___x_441_ = lean_nat_to_int(v___x_440_);
    return v___x_441_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_443_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__1;
    v___x_444_ = l_Lean_stringToMessageData(v___x_443_);
    return v___x_444_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_446_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__3;
    v___x_447_ = l_Lean_stringToMessageData(v___x_446_);
    return v___x_447_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap(
    mut v_i_448_: *mut leanh::LeanObject,
    mut v_x_449_: *mut leanh::LeanObject,
    mut v_a_450_: *mut leanh::LeanObject,
    mut v_a_451_: *mut leanh::LeanObject,
    mut v_a_452_: *mut leanh::LeanObject,
    mut v_a_453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hi_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ival_x3f_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ival_x3f_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_474_: u8 = 0;
    let mut v_val_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: u8 = 0;
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_499_: u8 = 0;
    let mut v_a_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_503_: u8 = 0;
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_507_: u8 = 0;
    let mut v_val_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_511_: u8 = 0;
    let mut v_val_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: u8 = 0;
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_519_: u8 = 0;
    let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_i_448_) {
                0 => {
                    v_lo_455_ = leanh::lean_ctor_get(v_i_448_, 0);
                    leanh::lean_inc_ref(v_lo_455_);
                    v_hi_456_ = leanh::lean_ctor_get(v_i_448_, 1);
                    leanh::lean_inc_ref(v_hi_456_);
                    leanh::lean_dec_ref_known(v_i_448_, 2);
                    v_val_457_ = leanh::lean_ctor_get(v_lo_455_, 0);
                    leanh::lean_inc_ref(v_val_457_);
                    v_ival_x3f_458_ = leanh::lean_ctor_get(v_lo_455_, 1);
                    leanh::lean_inc(v_ival_x3f_458_);
                    leanh::lean_dec_ref(v_lo_455_);
                    if leanh::lean_obj_tag(v_ival_x3f_458_) == 1 {
                        v_ival_x3f_466_ = leanh::lean_ctor_get(v_hi_456_, 1);
                        if leanh::lean_obj_tag(v_ival_x3f_466_) == 1 {
                            leanh::lean_inc_ref(v_ival_x3f_466_);
                            leanh::lean_dec_ref(v_val_457_);
                            v_val_467_ = leanh::lean_ctor_get(v_ival_x3f_458_, 0);
                            leanh::lean_inc(v_val_467_);
                            leanh::lean_dec_ref_known(v_ival_x3f_458_, 1);
                            v_val_468_ = leanh::lean_ctor_get(v_hi_456_, 0);
                            leanh::lean_inc_ref(v_val_468_);
                            leanh::lean_dec_ref(v_hi_456_);
                            v_val_469_ = leanh::lean_ctor_get(v_ival_x3f_466_, 0);
                            leanh::lean_inc(v_val_469_);
                            leanh::lean_dec_ref_known(v_ival_x3f_466_, 1);
                            leanh::lean_inc_ref(v_x_449_);
                            v___x_470_ = l_Lean_Meta_getIntValue_x3f(
                                v_x_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_,
                            );
                            if leanh::lean_obj_tag(v___x_470_) == 0 {
                                v_a_471_ = leanh::lean_ctor_get(v___x_470_, 0);
                                v_isSharedCheck_499_ =
                                    (!leanh::lean_is_exclusive(v___x_470_)) as u8;
                                if v_isSharedCheck_499_ == 0 {
                                    v___x_473_ = v___x_470_;
                                    v_isShared_474_ = v_isSharedCheck_499_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_471_);
                                    leanh::lean_dec(v___x_470_);
                                    v___x_473_ = leanh::lean_box(0);
                                    v_isShared_474_ = v_isSharedCheck_499_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_val_469_);
                                leanh::lean_dec_ref(v_val_468_);
                                leanh::lean_dec(v_val_467_);
                                leanh::lean_dec_ref(v_x_449_);
                                v_a_500_ = leanh::lean_ctor_get(v___x_470_, 0);
                                v_isSharedCheck_507_ =
                                    (!leanh::lean_is_exclusive(v___x_470_)) as u8;
                                if v_isSharedCheck_507_ == 0 {
                                    v___x_502_ = v___x_470_;
                                    v_isShared_503_ = v_isSharedCheck_507_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_500_);
                                    leanh::lean_dec(v___x_470_);
                                    v___x_502_ = leanh::lean_box(0);
                                    v_isShared_503_ = v_isSharedCheck_507_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            v_val_508_ = leanh::lean_ctor_get(v_ival_x3f_458_, 0);
                            v_isSharedCheck_519_ =
                                (!leanh::lean_is_exclusive(v_ival_x3f_458_)) as u8;
                            if v_isSharedCheck_519_ == 0 {
                                v___x_510_ = v_ival_x3f_458_;
                                v_isShared_511_ = v_isSharedCheck_519_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_508_);
                                leanh::lean_dec(v_ival_x3f_458_);
                                v___x_510_ = leanh::lean_box(0);
                                v_isShared_511_ = v_isSharedCheck_519_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_ival_x3f_458_);
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_dec_ref_known(v_i_448_, 1);
                    leanh::lean_dec_ref(v_x_449_);
                    v___x_520_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__2_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__2);
                    v___x_521_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___redArg(v___x_520_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
                    return v___x_521_;
                }
                2 => {
                    leanh::lean_dec_ref_known(v_i_448_, 1);
                    leanh::lean_dec_ref(v_x_449_);
                    v___x_522_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__4_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__4);
                    v___x_523_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___redArg(v___x_522_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
                    return v___x_523_;
                }
                _ => {
                    v___x_524_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_524_, 0, v_x_449_);
                    return v___x_524_;
                }
            },
            1 => {
                v_val_460_ = leanh::lean_ctor_get(v_hi_456_, 0);
                leanh::lean_inc_ref(v_val_460_);
                leanh::lean_dec_ref(v_hi_456_);
                leanh::lean_inc_ref_n(v_val_457_, 2);
                v___x_461_ = l_Lean_mkIntSub(v_x_449_, v_val_457_);
                v___x_462_ = l_Lean_mkIntSub(v_val_460_, v_val_457_);
                v___x_463_ = l_Lean_mkIntMod(v___x_461_, v___x_462_);
                v___x_464_ = l_Lean_mkIntAdd(v___x_463_, v_val_457_);
                v___x_465_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_465_, 0, v___x_464_);
                return v___x_465_;
            }
            2 => {
                if leanh::lean_obj_tag(v_a_471_) == 1 {
                    leanh::lean_dec_ref(v_val_468_);
                    leanh::lean_dec_ref(v_x_449_);
                    v_val_475_ = leanh::lean_ctor_get(v_a_471_, 0);
                    leanh::lean_inc(v_val_475_);
                    leanh::lean_dec_ref_known(v_a_471_, 1);
                    v___x_476_ = lean_int_sub(v_val_475_, v_val_467_);
                    leanh::lean_dec(v_val_475_);
                    v___x_477_ = lean_int_sub(v_val_469_, v_val_467_);
                    leanh::lean_dec(v_val_469_);
                    v___x_478_ = lean_int_emod(v___x_476_, v___x_477_);
                    leanh::lean_dec(v___x_477_);
                    leanh::lean_dec(v___x_476_);
                    v___x_479_ = lean_int_add(v___x_478_, v_val_467_);
                    leanh::lean_dec(v_val_467_);
                    leanh::lean_dec(v___x_478_);
                    v___x_480_ = l_Lean_mkIntLit(v___x_479_);
                    leanh::lean_dec(v___x_479_);
                    if v_isShared_474_ == 0 {
                        leanh::lean_ctor_set(v___x_473_, 0, v___x_480_);
                        v___x_482_ = v___x_473_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_483_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
                        v___x_482_ = v_reuseFailAlloc_483_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_471_);
                    v___x_484_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0);
                    v___x_485_ = lean_int_dec_eq(v_val_467_, v___x_484_);
                    if v___x_485_ == 0 {
                        leanh::lean_dec_ref(v_val_468_);
                        v___x_486_ = l_Lean_mkIntLit(v_val_467_);
                        leanh::lean_inc_ref(v___x_486_);
                        v___x_487_ = l_Lean_mkIntSub(v_x_449_, v___x_486_);
                        v___x_488_ = lean_int_sub(v_val_469_, v_val_467_);
                        leanh::lean_dec(v_val_467_);
                        leanh::lean_dec(v_val_469_);
                        v___x_489_ = l_Lean_mkIntLit(v___x_488_);
                        leanh::lean_dec(v___x_488_);
                        v___x_490_ = l_Lean_mkIntMod(v___x_487_, v___x_489_);
                        v___x_491_ = l_Lean_mkIntAdd(v___x_490_, v___x_486_);
                        if v_isShared_474_ == 0 {
                            leanh::lean_ctor_set(v___x_473_, 0, v___x_491_);
                            v___x_493_ = v___x_473_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_494_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
                            v___x_493_ = v_reuseFailAlloc_494_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_469_);
                        leanh::lean_dec(v_val_467_);
                        v___x_495_ = l_Lean_mkIntMod(v_x_449_, v_val_468_);
                        if v_isShared_474_ == 0 {
                            leanh::lean_ctor_set(v___x_473_, 0, v___x_495_);
                            v___x_497_ = v___x_473_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_498_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
                            v___x_497_ = v_reuseFailAlloc_498_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_482_;
            }
            4 => {
                return v___x_493_;
            }
            5 => {
                return v___x_497_;
            }
            6 => {
                if v_isShared_503_ == 0 {
                    v___x_505_ = v___x_502_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_506_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
                    v___x_505_ = v_reuseFailAlloc_506_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_505_;
            }
            8 => {
                v_val_512_ = leanh::lean_ctor_get(v_hi_456_, 0);
                v___x_513_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___closed__0,
                );
                v___x_514_ = lean_int_dec_eq(v_val_508_, v___x_513_);
                leanh::lean_dec(v_val_508_);
                if v___x_514_ == 0 {
                    leanh::lean_del_object(v___x_510_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_val_512_);
                    leanh::lean_dec_ref(v_val_457_);
                    leanh::lean_dec_ref(v_hi_456_);
                    v___x_515_ = l_Lean_mkIntMod(v_x_449_, v_val_512_);
                    if v_isShared_511_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_510_, 0);
                        leanh::lean_ctor_set(v___x_510_, 0, v___x_515_);
                        v___x_517_ = v___x_510_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_518_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
                        v___x_517_ = v_reuseFailAlloc_518_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_517_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap___boxed(
    mut v_i_525_: *mut leanh::LeanObject,
    mut v_x_526_: *mut leanh::LeanObject,
    mut v_a_527_: *mut leanh::LeanObject,
    mut v_a_528_: *mut leanh::LeanObject,
    mut v_a_529_: *mut leanh::LeanObject,
    mut v_a_530_: *mut leanh::LeanObject,
    mut v_a_531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_532_ = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap(
        v_i_525_, v_x_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_,
    );
    leanh::lean_dec(v_a_530_);
    leanh::lean_dec_ref(v_a_529_);
    leanh::lean_dec(v_a_528_);
    leanh::lean_dec_ref(v_a_527_);
    return v_res_532_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0(
    mut v_00_u03b1_533_: *mut leanh::LeanObject,
    mut v_msg_534_: *mut leanh::LeanObject,
    mut v___y_535_: *mut leanh::LeanObject,
    mut v___y_536_: *mut leanh::LeanObject,
    mut v___y_537_: *mut leanh::LeanObject,
    mut v___y_538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_540_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___redArg(v_msg_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
    return v___x_540_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0___boxed(
    mut v_00_u03b1_541_: *mut leanh::LeanObject,
    mut v_msg_542_: *mut leanh::LeanObject,
    mut v___y_543_: *mut leanh::LeanObject,
    mut v___y_544_: *mut leanh::LeanObject,
    mut v___y_545_: *mut leanh::LeanObject,
    mut v___y_546_: *mut leanh::LeanObject,
    mut v___y_547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_548_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap_spec__0(
            v_00_u03b1_541_,
            v_msg_542_,
            v___y_543_,
            v___y_544_,
            v___y_545_,
            v___y_546_,
        );
    leanh::lean_dec(v___y_546_);
    leanh::lean_dec_ref(v___y_545_);
    leanh::lean_dec(v___y_544_);
    leanh::lean_dec_ref(v___y_543_);
    return v_res_548_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_549_ = leanh::lean_box(0);
    v___x_550_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default;
    v___x_551_ = leanh::lean_box(0);
    v___x_552_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default___closed__2,
    );
    v___x_553_ = leanh::lean_unsigned_to_nat(0);
    v___x_554_ = leanh::lean_alloc_ctor(0, 26, (0) as u32);
    leanh::lean_ctor_set(v___x_554_, 0, v___x_553_);
    leanh::lean_ctor_set(v___x_554_, 1, v___x_552_);
    leanh::lean_ctor_set(v___x_554_, 2, v___x_551_);
    leanh::lean_ctor_set(v___x_554_, 3, v___x_552_);
    leanh::lean_ctor_set(v___x_554_, 4, v___x_552_);
    leanh::lean_ctor_set(v___x_554_, 5, v___x_550_);
    leanh::lean_ctor_set(v___x_554_, 6, v___x_552_);
    leanh::lean_ctor_set(v___x_554_, 7, v___x_552_);
    leanh::lean_ctor_set(v___x_554_, 8, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 9, v___x_552_);
    leanh::lean_ctor_set(v___x_554_, 10, v___x_552_);
    leanh::lean_ctor_set(v___x_554_, 11, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 12, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 13, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 14, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 15, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 16, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 17, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 18, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 19, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 20, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 21, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 22, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 23, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 24, v___x_549_);
    leanh::lean_ctor_set(v___x_554_, 25, v___x_549_);
    return v___x_554_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default()
-> *mut leanh::LeanObject {
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_555_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default___closed__0,
    );
    return v___x_555_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo()
-> *mut leanh::LeanObject {
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
    return v___x_556_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LitValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default();
    leanh::lean_mark_persistent(
        l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound_default,
    );
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicBound);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default();
    leanh::lean_mark_persistent(
        l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval_default,
    );
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval();
    leanh::lean_mark_persistent(
        l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedSymbolicIntInterval,
    );
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default();
    leanh::lean_mark_persistent(
        l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default,
    );
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_LitValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(builtin);
}