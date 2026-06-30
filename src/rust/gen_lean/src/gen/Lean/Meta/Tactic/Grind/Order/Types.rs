// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.Types
// Imports: Lean.Meta.Tactic.Grind.Types
use crate::ffi::{lean_mk_empty_array_with_capacity, lean_nat_to_int};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::l_Lean_Expr_const___override;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types,
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_SolverExtension_getState___redArg,
    l_Lean_Meta_Grind_registerSolverExtension___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
pub static mut l_Lean_Meta_Grind_Order_instInhabitedCnstrKind_default: u8 = 0;
pub static mut l_Lean_Meta_Grind_Order_instInhabitedCnstrKind: u8 = 0;
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__1_value:
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
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2_value:
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
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__1_value
        ) as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedWeight_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedWeight: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedProofInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedStruct: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedState_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedState: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_orderExt: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx(
    mut v_x_270_: u8,
) -> *mut leanh::LeanObject {
    if v_x_270_ == 0 {
        let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_271_ = leanh::lean_unsigned_to_nat(0);
        return v___x_271_;
    } else {
        let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_272_ = leanh::lean_unsigned_to_nat(1);
        return v___x_272_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx___boxed(
    mut v_x_273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_274_: u8 = 0;
    let mut v_res_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_274_ = (leanh::lean_unbox(v_x_273_) as u8);
    v_res_275_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx(v_x_boxed_274_);
    return v_res_275_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_toCtorIdx(
    mut v_x_276_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_277_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx(v_x_276_);
    return v___x_277_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_toCtorIdx___boxed(
    mut v_x_278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_279_: u8 = 0;
    let mut v_res_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_279_ = (leanh::lean_unbox(v_x_278_) as u8);
    v_res_280_ = l_Lean_Meta_Grind_Order_CnstrKind_toCtorIdx(v_x_4__boxed_279_);
    return v_res_280_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___redArg(
    mut v_k_281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_281_);
    return v_k_281_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___redArg___boxed(
    mut v_k_282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_283_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___redArg(v_k_282_);
    leanh::lean_dec(v_k_282_);
    return v_res_283_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorElim(
    mut v_motive_284_: *mut leanh::LeanObject,
    mut v_ctorIdx_285_: *mut leanh::LeanObject,
    mut v_t_286_: u8,
    mut v_h_287_: *mut leanh::LeanObject,
    mut v_k_288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_288_);
    return v_k_288_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___boxed(
    mut v_motive_289_: *mut leanh::LeanObject,
    mut v_ctorIdx_290_: *mut leanh::LeanObject,
    mut v_t_291_: *mut leanh::LeanObject,
    mut v_h_292_: *mut leanh::LeanObject,
    mut v_k_293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_294_: u8 = 0;
    let mut v_res_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_294_ = (leanh::lean_unbox(v_t_291_) as u8);
    v_res_295_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorElim(
        v_motive_289_,
        v_ctorIdx_290_,
        v_t_boxed_294_,
        v_h_292_,
        v_k_293_,
    );
    leanh::lean_dec(v_k_293_);
    leanh::lean_dec(v_ctorIdx_290_);
    return v_res_295_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_le_elim___redArg(
    mut v_le_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_le_296_);
    return v_le_296_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_le_elim___redArg___boxed(
    mut v_le_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_298_ = l_Lean_Meta_Grind_Order_CnstrKind_le_elim___redArg(v_le_297_);
    leanh::lean_dec(v_le_297_);
    return v_res_298_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_le_elim(
    mut v_motive_299_: *mut leanh::LeanObject,
    mut v_t_300_: u8,
    mut v_h_301_: *mut leanh::LeanObject,
    mut v_le_302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_le_302_);
    return v_le_302_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_le_elim___boxed(
    mut v_motive_303_: *mut leanh::LeanObject,
    mut v_t_304_: *mut leanh::LeanObject,
    mut v_h_305_: *mut leanh::LeanObject,
    mut v_le_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_307_: u8 = 0;
    let mut v_res_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_307_ = (leanh::lean_unbox(v_t_304_) as u8);
    v_res_308_ = l_Lean_Meta_Grind_Order_CnstrKind_le_elim(
        v_motive_303_,
        v_t_boxed_307_,
        v_h_305_,
        v_le_306_,
    );
    leanh::lean_dec(v_le_306_);
    return v_res_308_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___redArg(
    mut v_lt_309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_lt_309_);
    return v_lt_309_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___redArg___boxed(
    mut v_lt_310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_311_ = l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___redArg(v_lt_310_);
    leanh::lean_dec(v_lt_310_);
    return v_res_311_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_lt_elim(
    mut v_motive_312_: *mut leanh::LeanObject,
    mut v_t_313_: u8,
    mut v_h_314_: *mut leanh::LeanObject,
    mut v_lt_315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_lt_315_);
    return v_lt_315_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___boxed(
    mut v_motive_316_: *mut leanh::LeanObject,
    mut v_t_317_: *mut leanh::LeanObject,
    mut v_h_318_: *mut leanh::LeanObject,
    mut v_lt_319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_320_: u8 = 0;
    let mut v_res_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_320_ = (leanh::lean_unbox(v_t_317_) as u8);
    v_res_321_ = l_Lean_Meta_Grind_Order_CnstrKind_lt_elim(
        v_motive_316_,
        v_t_boxed_320_,
        v_h_318_,
        v_lt_319_,
    );
    leanh::lean_dec(v_lt_319_);
    return v_res_321_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedCnstrKind_default() -> u8 {
    let mut v___x_322_: u8 = 0;
    v___x_322_ = 0;
    return v___x_322_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedCnstrKind() -> u8 {
    let mut v___x_323_: u8 = 0;
    v___x_323_ = 0;
    return v___x_323_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_324_ = leanh::lean_unsigned_to_nat(0);
    v___x_325_ = lean_nat_to_int(v___x_324_);
    return v___x_325_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_329_ = leanh::lean_box(0);
    v___x_330_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2;
    v___x_331_ = l_Lean_Expr_const___override(v___x_330_, v___x_329_);
    return v___x_331_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(
    mut v_inst_332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_333_: u8 = 0;
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_333_ = 0;
    v___x_334_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0,
    );
    v___x_335_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_336_ = leanh::lean_box(0);
    leanh::lean_inc(v_inst_332_);
    v___x_337_ = leanh::lean_alloc_ctor(0, 5, (1) as u32);
    leanh::lean_ctor_set(v___x_337_, 0, v_inst_332_);
    leanh::lean_ctor_set(v___x_337_, 1, v_inst_332_);
    leanh::lean_ctor_set(v___x_337_, 2, v___x_334_);
    leanh::lean_ctor_set(v___x_337_, 3, v___x_335_);
    leanh::lean_ctor_set(v___x_337_, 4, v___x_336_);
    leanh::lean_ctor_set_uint8(
        v___x_337_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
        v___x_333_,
    );
    return v___x_337_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instInhabitedCnstr_default(
    mut v_00_u03b1_338_: *mut leanh::LeanObject,
    mut v_inst_339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_340_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v_inst_339_);
    return v___x_340_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instInhabitedCnstr___redArg(
    mut v_inst_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v_inst_341_);
    return v___x_342_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instInhabitedCnstr(
    mut v_a_343_: *mut leanh::LeanObject,
    mut v_inst_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_345_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v_inst_344_);
    return v___x_345_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_346_: u8 = 0;
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_346_ = 0;
    v___x_347_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0,
    );
    v___x_348_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_348_, 0, v___x_347_);
    leanh::lean_ctor_set_uint8(
        v___x_348_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_346_,
    );
    return v___x_348_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default()
-> *mut leanh::LeanObject {
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_349_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0,
    );
    return v___x_349_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedWeight() -> *mut leanh::LeanObject {
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = l_Lean_Meta_Grind_Order_instInhabitedWeight_default;
    return v___x_350_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_351_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_352_ = l_Lean_Meta_Grind_Order_instInhabitedWeight_default;
    v___x_353_ = leanh::lean_unsigned_to_nat(0);
    v___x_354_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_354_, 0, v___x_353_);
    leanh::lean_ctor_set(v___x_354_, 1, v___x_352_);
    leanh::lean_ctor_set(v___x_354_, 2, v___x_351_);
    return v___x_354_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default()
-> *mut leanh::LeanObject {
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_355_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0,
    );
    return v___x_355_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo() -> *mut leanh::LeanObject
{
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default;
    return v___x_356_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_ctorIdx(
    mut v_x_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_357_) {
        0 => {
            let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_358_ = leanh::lean_unsigned_to_nat(0);
            return v___x_358_;
        }
        1 => {
            let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_359_ = leanh::lean_unsigned_to_nat(1);
            return v___x_359_;
        }
        _ => {
            let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_360_ = leanh::lean_unsigned_to_nat(2);
            return v___x_360_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_ctorIdx___boxed(
    mut v_x_361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_362_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorIdx(v_x_361_);
    leanh::lean_dec_ref(v_x_361_);
    return v_res_362_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(
    mut v_t_363_: *mut leanh::LeanObject,
    mut v_k_364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_363_) == 2 {
        let mut v_u_365_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_366_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_u_365_ = leanh::lean_ctor_get(v_t_363_, 0);
        leanh::lean_inc(v_u_365_);
        v_v_366_ = leanh::lean_ctor_get(v_t_363_, 1);
        leanh::lean_inc(v_v_366_);
        leanh::lean_dec_ref_known(v_t_363_, 2);
        v___x_367_ = leanh::lean_apply_2(v_k_364_, v_u_365_, v_v_366_);
        return v___x_367_;
    } else {
        let mut v_c_368_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_e_369_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_370_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_371_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_372_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_x27_373_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_c_368_ = leanh::lean_ctor_get(v_t_363_, 0);
        leanh::lean_inc_ref(v_c_368_);
        v_e_369_ = leanh::lean_ctor_get(v_t_363_, 1);
        leanh::lean_inc_ref(v_e_369_);
        v_u_370_ = leanh::lean_ctor_get(v_t_363_, 2);
        leanh::lean_inc(v_u_370_);
        v_v_371_ = leanh::lean_ctor_get(v_t_363_, 3);
        leanh::lean_inc(v_v_371_);
        v_k_372_ = leanh::lean_ctor_get(v_t_363_, 4);
        leanh::lean_inc_ref(v_k_372_);
        v_k_x27_373_ = leanh::lean_ctor_get(v_t_363_, 5);
        leanh::lean_inc_ref(v_k_x27_373_);
        leanh::lean_dec_ref(v_t_363_);
        v___x_374_ = leanh::lean_apply_6(
            v_k_364_,
            v_c_368_,
            v_e_369_,
            v_u_370_,
            v_v_371_,
            v_k_372_,
            v_k_x27_373_,
        );
        return v___x_374_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_ctorElim(
    mut v_motive_375_: *mut leanh::LeanObject,
    mut v_ctorIdx_376_: *mut leanh::LeanObject,
    mut v_t_377_: *mut leanh::LeanObject,
    mut v_h_378_: *mut leanh::LeanObject,
    mut v_k_379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_377_, v_k_379_);
    return v___x_380_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___boxed(
    mut v_motive_381_: *mut leanh::LeanObject,
    mut v_ctorIdx_382_: *mut leanh::LeanObject,
    mut v_t_383_: *mut leanh::LeanObject,
    mut v_h_384_: *mut leanh::LeanObject,
    mut v_k_385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_386_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim(
        v_motive_381_,
        v_ctorIdx_382_,
        v_t_383_,
        v_h_384_,
        v_k_385_,
    );
    leanh::lean_dec(v_ctorIdx_382_);
    return v_res_386_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eqTrue_elim___redArg(
    mut v_t_387_: *mut leanh::LeanObject,
    mut v_eqTrue_388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_389_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_387_, v_eqTrue_388_);
    return v___x_389_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eqTrue_elim(
    mut v_motive_390_: *mut leanh::LeanObject,
    mut v_t_391_: *mut leanh::LeanObject,
    mut v_h_392_: *mut leanh::LeanObject,
    mut v_eqTrue_393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_394_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_391_, v_eqTrue_393_);
    return v___x_394_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eqFalse_elim___redArg(
    mut v_t_395_: *mut leanh::LeanObject,
    mut v_eqFalse_396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_397_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_395_, v_eqFalse_396_);
    return v___x_397_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eqFalse_elim(
    mut v_motive_398_: *mut leanh::LeanObject,
    mut v_t_399_: *mut leanh::LeanObject,
    mut v_h_400_: *mut leanh::LeanObject,
    mut v_eqFalse_401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_399_, v_eqFalse_401_);
    return v___x_402_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eq_elim___redArg(
    mut v_t_403_: *mut leanh::LeanObject,
    mut v_eq_404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_405_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_403_, v_eq_404_);
    return v___x_405_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eq_elim(
    mut v_motive_406_: *mut leanh::LeanObject,
    mut v_t_407_: *mut leanh::LeanObject,
    mut v_h_408_: *mut leanh::LeanObject,
    mut v_eq_409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_410_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_407_, v_eq_409_);
    return v___x_410_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_411_ = leanh::lean_unsigned_to_nat(0);
    v___x_412_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v___x_411_);
    return v___x_412_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_413_ = l_Lean_Meta_Grind_Order_instInhabitedWeight_default;
    v___x_414_ = leanh::lean_unsigned_to_nat(0);
    v___x_415_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_416_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0,
    );
    v___x_417_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_417_, 0, v___x_416_);
    leanh::lean_ctor_set(v___x_417_, 1, v___x_415_);
    leanh::lean_ctor_set(v___x_417_, 2, v___x_414_);
    leanh::lean_ctor_set(v___x_417_, 3, v___x_414_);
    leanh::lean_ctor_set(v___x_417_, 4, v___x_413_);
    leanh::lean_ctor_set(v___x_417_, 5, v___x_413_);
    return v___x_417_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default()
-> *mut leanh::LeanObject {
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_418_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1,
    );
    return v___x_418_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate()
-> *mut leanh::LeanObject {
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_419_ = l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default;
    return v___x_419_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_420_ = leanh::lean_unsigned_to_nat(32);
    v___x_421_ = lean_mk_empty_array_with_capacity(v___x_420_);
    v___x_422_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_422_, 0, v___x_421_);
    return v___x_422_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_423_: usize = 0;
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_423_ = 5usize;
    v___x_424_ = leanh::lean_unsigned_to_nat(0);
    v___x_425_ = leanh::lean_unsigned_to_nat(32);
    v___x_426_ = lean_mk_empty_array_with_capacity(v___x_425_);
    v___x_427_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0,
    );
    v___x_428_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_428_, 0, v___x_427_);
    leanh::lean_ctor_set(v___x_428_, 1, v___x_426_);
    leanh::lean_ctor_set(v___x_428_, 2, v___x_424_);
    leanh::lean_ctor_set(v___x_428_, 3, v___x_424_);
    leanh::lean_ctor_set_usize(v___x_428_, 4, v___x_423_);
    return v___x_428_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_429_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_429_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2,
    );
    v___x_431_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_431_, 0, v___x_430_);
    return v___x_431_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: u8 = 0;
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_432_ = leanh::lean_box(0);
    v___x_433_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3,
    );
    v___x_434_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1,
    );
    v___x_435_ = 0;
    v___x_436_ = leanh::lean_box(0);
    v___x_437_ = leanh::lean_box(0);
    v___x_438_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_439_ = leanh::lean_unsigned_to_nat(0);
    v___x_440_ = leanh::lean_alloc_ctor(0, 22, (1) as u32);
    leanh::lean_ctor_set(v___x_440_, 0, v___x_439_);
    leanh::lean_ctor_set(v___x_440_, 1, v___x_438_);
    leanh::lean_ctor_set(v___x_440_, 2, v___x_437_);
    leanh::lean_ctor_set(v___x_440_, 3, v___x_438_);
    leanh::lean_ctor_set(v___x_440_, 4, v___x_438_);
    leanh::lean_ctor_set(v___x_440_, 5, v___x_436_);
    leanh::lean_ctor_set(v___x_440_, 6, v___x_436_);
    leanh::lean_ctor_set(v___x_440_, 7, v___x_436_);
    leanh::lean_ctor_set(v___x_440_, 8, v___x_436_);
    leanh::lean_ctor_set(v___x_440_, 9, v___x_436_);
    leanh::lean_ctor_set(v___x_440_, 10, v___x_436_);
    leanh::lean_ctor_set(v___x_440_, 11, v___x_436_);
    leanh::lean_ctor_set(v___x_440_, 12, v___x_438_);
    leanh::lean_ctor_set(v___x_440_, 13, v___x_436_);
    leanh::lean_ctor_set(v___x_440_, 14, v___x_434_);
    leanh::lean_ctor_set(v___x_440_, 15, v___x_433_);
    leanh::lean_ctor_set(v___x_440_, 16, v___x_433_);
    leanh::lean_ctor_set(v___x_440_, 17, v___x_433_);
    leanh::lean_ctor_set(v___x_440_, 18, v___x_434_);
    leanh::lean_ctor_set(v___x_440_, 19, v___x_434_);
    leanh::lean_ctor_set(v___x_440_, 20, v___x_434_);
    leanh::lean_ctor_set(v___x_440_, 21, v___x_432_);
    leanh::lean_ctor_set_uint8(
        v___x_440_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 22) as u32,
        v___x_435_,
    );
    return v___x_440_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default()
-> *mut leanh::LeanObject {
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_441_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4,
    );
    return v___x_441_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct() -> *mut leanh::LeanObject {
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_442_ = l_Lean_Meta_Grind_Order_instInhabitedStruct_default;
    return v___x_442_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_443_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_444_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_444_, 0, v___x_443_);
    leanh::lean_ctor_set(v___x_444_, 1, v___x_443_);
    leanh::lean_ctor_set(v___x_444_, 2, v___x_443_);
    return v___x_444_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default()
-> *mut leanh::LeanObject {
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_445_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default___closed__0,
    );
    return v___x_445_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry()
-> *mut leanh::LeanObject {
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_446_ = l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default;
    return v___x_446_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_449_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_449_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_450_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1,
    );
    v___x_451_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_451_, 0, v___x_450_);
    return v___x_451_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_452_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2,
    );
    v___x_453_ = l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0;
    v___x_454_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_454_, 0, v___x_453_);
    leanh::lean_ctor_set(v___x_454_, 1, v___x_452_);
    leanh::lean_ctor_set(v___x_454_, 2, v___x_452_);
    leanh::lean_ctor_set(v___x_454_, 3, v___x_452_);
    leanh::lean_ctor_set(v___x_454_, 4, v___x_452_);
    return v___x_454_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState_default()
-> *mut leanh::LeanObject {
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_455_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3,
    );
    return v___x_455_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState() -> *mut leanh::LeanObject {
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_456_ = l_Lean_Meta_Grind_Order_instInhabitedState_default;
    return v___x_456_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_(
    mut v___x_457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_459_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_459_, 0, v___x_457_);
    return v___x_459_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2____boxed(
    mut v___x_460_: *mut leanh::LeanObject,
    mut v___y_461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_462_ = l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_(v___x_460_);
    return v_res_462_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_463_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3,
    );
    v___f_464_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_464_, 0, v___x_463_);
    return v___f_464_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_466_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_);
    v___x_467_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_466_);
    return v___x_467_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2____boxed(
    mut v_a_468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_469_ = l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_();
    return v_res_469_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_get_x27___redArg(
    mut v_a_470_: *mut leanh::LeanObject,
    mut v_a_471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_473_ = l_Lean_Meta_Grind_Order_orderExt;
    v___x_474_ =
        l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_473_, v_a_470_, v_a_471_);
    return v___x_474_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_get_x27___redArg___boxed(
    mut v_a_475_: *mut leanh::LeanObject,
    mut v_a_476_: *mut leanh::LeanObject,
    mut v_a_477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_475_, v_a_476_);
    leanh::lean_dec_ref(v_a_476_);
    leanh::lean_dec(v_a_475_);
    return v_res_478_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_get_x27(
    mut v_a_479_: *mut leanh::LeanObject,
    mut v_a_480_: *mut leanh::LeanObject,
    mut v_a_481_: *mut leanh::LeanObject,
    mut v_a_482_: *mut leanh::LeanObject,
    mut v_a_483_: *mut leanh::LeanObject,
    mut v_a_484_: *mut leanh::LeanObject,
    mut v_a_485_: *mut leanh::LeanObject,
    mut v_a_486_: *mut leanh::LeanObject,
    mut v_a_487_: *mut leanh::LeanObject,
    mut v_a_488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_490_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_479_, v_a_487_);
    return v___x_490_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_get_x27___boxed(
    mut v_a_491_: *mut leanh::LeanObject,
    mut v_a_492_: *mut leanh::LeanObject,
    mut v_a_493_: *mut leanh::LeanObject,
    mut v_a_494_: *mut leanh::LeanObject,
    mut v_a_495_: *mut leanh::LeanObject,
    mut v_a_496_: *mut leanh::LeanObject,
    mut v_a_497_: *mut leanh::LeanObject,
    mut v_a_498_: *mut leanh::LeanObject,
    mut v_a_499_: *mut leanh::LeanObject,
    mut v_a_500_: *mut leanh::LeanObject,
    mut v_a_501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_502_ = l_Lean_Meta_Grind_Order_get_x27(
        v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_,
        v_a_500_,
    );
    leanh::lean_dec(v_a_500_);
    leanh::lean_dec_ref(v_a_499_);
    leanh::lean_dec(v_a_498_);
    leanh::lean_dec_ref(v_a_497_);
    leanh::lean_dec(v_a_496_);
    leanh::lean_dec_ref(v_a_495_);
    leanh::lean_dec(v_a_494_);
    leanh::lean_dec_ref(v_a_493_);
    leanh::lean_dec(v_a_492_);
    leanh::lean_dec(v_a_491_);
    return v_res_502_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modify_x27___redArg(
    mut v_f_503_: *mut leanh::LeanObject,
    mut v_a_504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_506_ = l_Lean_Meta_Grind_Order_orderExt;
    v___x_507_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_506_, v_f_503_, v_a_504_);
    return v___x_507_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modify_x27___redArg___boxed(
    mut v_f_508_: *mut leanh::LeanObject,
    mut v_a_509_: *mut leanh::LeanObject,
    mut v_a_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_511_ = l_Lean_Meta_Grind_Order_modify_x27___redArg(v_f_508_, v_a_509_);
    leanh::lean_dec(v_a_509_);
    return v_res_511_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modify_x27(
    mut v_f_512_: *mut leanh::LeanObject,
    mut v_a_513_: *mut leanh::LeanObject,
    mut v_a_514_: *mut leanh::LeanObject,
    mut v_a_515_: *mut leanh::LeanObject,
    mut v_a_516_: *mut leanh::LeanObject,
    mut v_a_517_: *mut leanh::LeanObject,
    mut v_a_518_: *mut leanh::LeanObject,
    mut v_a_519_: *mut leanh::LeanObject,
    mut v_a_520_: *mut leanh::LeanObject,
    mut v_a_521_: *mut leanh::LeanObject,
    mut v_a_522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_524_ = l_Lean_Meta_Grind_Order_orderExt;
    v___x_525_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_524_, v_f_512_, v_a_513_);
    return v___x_525_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modify_x27___boxed(
    mut v_f_526_: *mut leanh::LeanObject,
    mut v_a_527_: *mut leanh::LeanObject,
    mut v_a_528_: *mut leanh::LeanObject,
    mut v_a_529_: *mut leanh::LeanObject,
    mut v_a_530_: *mut leanh::LeanObject,
    mut v_a_531_: *mut leanh::LeanObject,
    mut v_a_532_: *mut leanh::LeanObject,
    mut v_a_533_: *mut leanh::LeanObject,
    mut v_a_534_: *mut leanh::LeanObject,
    mut v_a_535_: *mut leanh::LeanObject,
    mut v_a_536_: *mut leanh::LeanObject,
    mut v_a_537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_538_ = l_Lean_Meta_Grind_Order_modify_x27(
        v_f_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_,
        v_a_535_, v_a_536_,
    );
    leanh::lean_dec(v_a_536_);
    leanh::lean_dec_ref(v_a_535_);
    leanh::lean_dec(v_a_534_);
    leanh::lean_dec_ref(v_a_533_);
    leanh::lean_dec(v_a_532_);
    leanh::lean_dec_ref(v_a_531_);
    leanh::lean_dec(v_a_530_);
    leanh::lean_dec_ref(v_a_529_);
    leanh::lean_dec(v_a_528_);
    leanh::lean_dec(v_a_527_);
    return v_res_538_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_Order_instInhabitedCnstrKind_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstrKind_default();
    l_Lean_Meta_Grind_Order_instInhabitedCnstrKind =
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstrKind();
    l_Lean_Meta_Grind_Order_instInhabitedWeight_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedWeight_default);
    l_Lean_Meta_Grind_Order_instInhabitedWeight =
        _init_l_Lean_Meta_Grind_Order_instInhabitedWeight();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedWeight);
    l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default);
    l_Lean_Meta_Grind_Order_instInhabitedProofInfo =
        _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedProofInfo);
    l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default);
    l_Lean_Meta_Grind_Order_instInhabitedToPropagate =
        _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedToPropagate);
    l_Lean_Meta_Grind_Order_instInhabitedStruct_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedStruct_default);
    l_Lean_Meta_Grind_Order_instInhabitedStruct =
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedStruct);
    l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default);
    l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry =
        _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry);
    l_Lean_Meta_Grind_Order_instInhabitedState_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedState_default);
    l_Lean_Meta_Grind_Order_instInhabitedState = _init_l_Lean_Meta_Grind_Order_instInhabitedState();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedState);
    res = l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Grind_Order_orderExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_orderExt);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Order_Types(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Order_Types(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
}