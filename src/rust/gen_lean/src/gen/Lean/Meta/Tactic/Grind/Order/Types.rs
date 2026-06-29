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
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__1_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        17542774118954891045 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedWeight_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedWeight: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedProofInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedStruct: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedState_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_orderExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx(
    mut v_x_270_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_x_270_ == 0 {
        let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_271_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_271_;
    } else {
        let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_272_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_272_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx___boxed(
    mut v_x_273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_274_: u8 = 0;
    let mut v_res_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_274_ = (crate::leanh::lean_unbox(v_x_273_) as u8);
    v_res_275_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx(v_x_boxed_274_);
    return v_res_275_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_toCtorIdx(
    mut v_x_276_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_277_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx(v_x_276_);
    return v___x_277_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_toCtorIdx___boxed(
    mut v_x_278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_279_: u8 = 0;
    let mut v_res_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_279_ = (crate::leanh::lean_unbox(v_x_278_) as u8);
    v_res_280_ = l_Lean_Meta_Grind_Order_CnstrKind_toCtorIdx(v_x_4__boxed_279_);
    return v_res_280_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___redArg(
    mut v_k_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_281_);
    return v_k_281_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___redArg___boxed(
    mut v_k_282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_283_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___redArg(v_k_282_);
    crate::leanh::lean_dec(v_k_282_);
    return v_res_283_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorElim(
    mut v_motive_284_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_285_: *mut crate::leanh::LeanObject,
    mut v_t_286_: u8,
    mut v_h_287_: *mut crate::leanh::LeanObject,
    mut v_k_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_288_);
    return v_k_288_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___boxed(
    mut v_motive_289_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_290_: *mut crate::leanh::LeanObject,
    mut v_t_291_: *mut crate::leanh::LeanObject,
    mut v_h_292_: *mut crate::leanh::LeanObject,
    mut v_k_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_294_: u8 = 0;
    let mut v_res_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_294_ = (crate::leanh::lean_unbox(v_t_291_) as u8);
    v_res_295_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorElim(
        v_motive_289_,
        v_ctorIdx_290_,
        v_t_boxed_294_,
        v_h_292_,
        v_k_293_,
    );
    crate::leanh::lean_dec(v_k_293_);
    crate::leanh::lean_dec(v_ctorIdx_290_);
    return v_res_295_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_le_elim___redArg(
    mut v_le_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_le_296_);
    return v_le_296_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_le_elim___redArg___boxed(
    mut v_le_297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_298_ = l_Lean_Meta_Grind_Order_CnstrKind_le_elim___redArg(v_le_297_);
    crate::leanh::lean_dec(v_le_297_);
    return v_res_298_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_le_elim(
    mut v_motive_299_: *mut crate::leanh::LeanObject,
    mut v_t_300_: u8,
    mut v_h_301_: *mut crate::leanh::LeanObject,
    mut v_le_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_le_302_);
    return v_le_302_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_le_elim___boxed(
    mut v_motive_303_: *mut crate::leanh::LeanObject,
    mut v_t_304_: *mut crate::leanh::LeanObject,
    mut v_h_305_: *mut crate::leanh::LeanObject,
    mut v_le_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_307_: u8 = 0;
    let mut v_res_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_307_ = (crate::leanh::lean_unbox(v_t_304_) as u8);
    v_res_308_ = l_Lean_Meta_Grind_Order_CnstrKind_le_elim(
        v_motive_303_,
        v_t_boxed_307_,
        v_h_305_,
        v_le_306_,
    );
    crate::leanh::lean_dec(v_le_306_);
    return v_res_308_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___redArg(
    mut v_lt_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_lt_309_);
    return v_lt_309_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___redArg___boxed(
    mut v_lt_310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_311_ = l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___redArg(v_lt_310_);
    crate::leanh::lean_dec(v_lt_310_);
    return v_res_311_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_lt_elim(
    mut v_motive_312_: *mut crate::leanh::LeanObject,
    mut v_t_313_: u8,
    mut v_h_314_: *mut crate::leanh::LeanObject,
    mut v_lt_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_lt_315_);
    return v_lt_315_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___boxed(
    mut v_motive_316_: *mut crate::leanh::LeanObject,
    mut v_t_317_: *mut crate::leanh::LeanObject,
    mut v_h_318_: *mut crate::leanh::LeanObject,
    mut v_lt_319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_320_: u8 = 0;
    let mut v_res_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_320_ = (crate::leanh::lean_unbox(v_t_317_) as u8);
    v_res_321_ = l_Lean_Meta_Grind_Order_CnstrKind_lt_elim(
        v_motive_316_,
        v_t_boxed_320_,
        v_h_318_,
        v_lt_319_,
    );
    crate::leanh::lean_dec(v_lt_319_);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_324_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_325_ = lean_nat_to_int(v___x_324_);
    return v___x_325_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_329_ = crate::leanh::lean_box(0);
    v___x_330_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2;
    v___x_331_ = l_Lean_Expr_const___override(v___x_330_, v___x_329_);
    return v___x_331_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(
    mut v_inst_332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_333_: u8 = 0;
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_333_ = 0;
    v___x_334_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0,
    );
    v___x_335_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_336_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_inst_332_);
    v___x_337_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_337_, 0, v_inst_332_);
    crate::leanh::lean_ctor_set(v___x_337_, 1, v_inst_332_);
    crate::leanh::lean_ctor_set(v___x_337_, 2, v___x_334_);
    crate::leanh::lean_ctor_set(v___x_337_, 3, v___x_335_);
    crate::leanh::lean_ctor_set(v___x_337_, 4, v___x_336_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_337_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
        v___x_333_,
    );
    return v___x_337_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instInhabitedCnstr_default(
    mut v_00_u03b1_338_: *mut crate::leanh::LeanObject,
    mut v_inst_339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_340_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v_inst_339_);
    return v___x_340_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instInhabitedCnstr___redArg(
    mut v_inst_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v_inst_341_);
    return v___x_342_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instInhabitedCnstr(
    mut v_a_343_: *mut crate::leanh::LeanObject,
    mut v_inst_344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_345_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v_inst_344_);
    return v___x_345_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_346_: u8 = 0;
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_346_ = 0;
    v___x_347_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0,
    );
    v___x_348_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_348_, 0, v___x_347_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_348_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_346_,
    );
    return v___x_348_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_349_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0,
    );
    return v___x_349_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedWeight() -> *mut crate::leanh::LeanObject {
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = l_Lean_Meta_Grind_Order_instInhabitedWeight_default;
    return v___x_350_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_351_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_352_ = l_Lean_Meta_Grind_Order_instInhabitedWeight_default;
    v___x_353_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_354_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_354_, 0, v___x_353_);
    crate::leanh::lean_ctor_set(v___x_354_, 1, v___x_352_);
    crate::leanh::lean_ctor_set(v___x_354_, 2, v___x_351_);
    return v___x_354_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_355_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0,
    );
    return v___x_355_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo() -> *mut crate::leanh::LeanObject
{
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default;
    return v___x_356_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_ctorIdx(
    mut v_x_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_357_) {
        0 => {
            let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_358_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_358_;
        }
        1 => {
            let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_359_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_359_;
        }
        _ => {
            let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_360_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_360_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_ctorIdx___boxed(
    mut v_x_361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_362_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorIdx(v_x_361_);
    crate::leanh::lean_dec_ref(v_x_361_);
    return v_res_362_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(
    mut v_t_363_: *mut crate::leanh::LeanObject,
    mut v_k_364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_363_) == 2 {
        let mut v_u_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_u_365_ = crate::leanh::lean_ctor_get(v_t_363_, 0);
        crate::leanh::lean_inc(v_u_365_);
        v_v_366_ = crate::leanh::lean_ctor_get(v_t_363_, 1);
        crate::leanh::lean_inc(v_v_366_);
        crate::leanh::lean_dec_ref_known(v_t_363_, 2);
        v___x_367_ = crate::leanh::lean_apply_2(v_k_364_, v_u_365_, v_v_366_);
        return v___x_367_;
    } else {
        let mut v_c_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_e_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_x27_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_c_368_ = crate::leanh::lean_ctor_get(v_t_363_, 0);
        crate::leanh::lean_inc_ref(v_c_368_);
        v_e_369_ = crate::leanh::lean_ctor_get(v_t_363_, 1);
        crate::leanh::lean_inc_ref(v_e_369_);
        v_u_370_ = crate::leanh::lean_ctor_get(v_t_363_, 2);
        crate::leanh::lean_inc(v_u_370_);
        v_v_371_ = crate::leanh::lean_ctor_get(v_t_363_, 3);
        crate::leanh::lean_inc(v_v_371_);
        v_k_372_ = crate::leanh::lean_ctor_get(v_t_363_, 4);
        crate::leanh::lean_inc_ref(v_k_372_);
        v_k_x27_373_ = crate::leanh::lean_ctor_get(v_t_363_, 5);
        crate::leanh::lean_inc_ref(v_k_x27_373_);
        crate::leanh::lean_dec_ref(v_t_363_);
        v___x_374_ = crate::leanh::lean_apply_6(
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
    mut v_motive_375_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_376_: *mut crate::leanh::LeanObject,
    mut v_t_377_: *mut crate::leanh::LeanObject,
    mut v_h_378_: *mut crate::leanh::LeanObject,
    mut v_k_379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_377_, v_k_379_);
    return v___x_380_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___boxed(
    mut v_motive_381_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_382_: *mut crate::leanh::LeanObject,
    mut v_t_383_: *mut crate::leanh::LeanObject,
    mut v_h_384_: *mut crate::leanh::LeanObject,
    mut v_k_385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_386_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim(
        v_motive_381_,
        v_ctorIdx_382_,
        v_t_383_,
        v_h_384_,
        v_k_385_,
    );
    crate::leanh::lean_dec(v_ctorIdx_382_);
    return v_res_386_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eqTrue_elim___redArg(
    mut v_t_387_: *mut crate::leanh::LeanObject,
    mut v_eqTrue_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_389_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_387_, v_eqTrue_388_);
    return v___x_389_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eqTrue_elim(
    mut v_motive_390_: *mut crate::leanh::LeanObject,
    mut v_t_391_: *mut crate::leanh::LeanObject,
    mut v_h_392_: *mut crate::leanh::LeanObject,
    mut v_eqTrue_393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_394_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_391_, v_eqTrue_393_);
    return v___x_394_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eqFalse_elim___redArg(
    mut v_t_395_: *mut crate::leanh::LeanObject,
    mut v_eqFalse_396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_397_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_395_, v_eqFalse_396_);
    return v___x_397_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eqFalse_elim(
    mut v_motive_398_: *mut crate::leanh::LeanObject,
    mut v_t_399_: *mut crate::leanh::LeanObject,
    mut v_h_400_: *mut crate::leanh::LeanObject,
    mut v_eqFalse_401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_399_, v_eqFalse_401_);
    return v___x_402_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eq_elim___redArg(
    mut v_t_403_: *mut crate::leanh::LeanObject,
    mut v_eq_404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_405_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_403_, v_eq_404_);
    return v___x_405_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eq_elim(
    mut v_motive_406_: *mut crate::leanh::LeanObject,
    mut v_t_407_: *mut crate::leanh::LeanObject,
    mut v_h_408_: *mut crate::leanh::LeanObject,
    mut v_eq_409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_410_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_407_, v_eq_409_);
    return v___x_410_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_411_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_412_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v___x_411_);
    return v___x_412_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_413_ = l_Lean_Meta_Grind_Order_instInhabitedWeight_default;
    v___x_414_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_415_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_416_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0,
    );
    v___x_417_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_417_, 0, v___x_416_);
    crate::leanh::lean_ctor_set(v___x_417_, 1, v___x_415_);
    crate::leanh::lean_ctor_set(v___x_417_, 2, v___x_414_);
    crate::leanh::lean_ctor_set(v___x_417_, 3, v___x_414_);
    crate::leanh::lean_ctor_set(v___x_417_, 4, v___x_413_);
    crate::leanh::lean_ctor_set(v___x_417_, 5, v___x_413_);
    return v___x_417_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_418_ = crate::leanh::lean_obj_once(
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_419_ = l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default;
    return v___x_419_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_420_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_421_ = lean_mk_empty_array_with_capacity(v___x_420_);
    v___x_422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_422_, 0, v___x_421_);
    return v___x_422_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_423_: usize = 0;
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_423_ = 5usize;
    v___x_424_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_425_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_426_ = lean_mk_empty_array_with_capacity(v___x_425_);
    v___x_427_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0,
    );
    v___x_428_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_428_, 0, v___x_427_);
    crate::leanh::lean_ctor_set(v___x_428_, 1, v___x_426_);
    crate::leanh::lean_ctor_set(v___x_428_, 2, v___x_424_);
    crate::leanh::lean_ctor_set(v___x_428_, 3, v___x_424_);
    crate::leanh::lean_ctor_set_usize(v___x_428_, 4, v___x_423_);
    return v___x_428_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_429_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_429_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2,
    );
    v___x_431_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_431_, 0, v___x_430_);
    return v___x_431_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: u8 = 0;
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_432_ = crate::leanh::lean_box(0);
    v___x_433_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3,
    );
    v___x_434_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1,
    );
    v___x_435_ = 0;
    v___x_436_ = crate::leanh::lean_box(0);
    v___x_437_ = crate::leanh::lean_box(0);
    v___x_438_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_439_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_440_ = crate::leanh::lean_alloc_ctor(0, 22, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_440_, 0, v___x_439_);
    crate::leanh::lean_ctor_set(v___x_440_, 1, v___x_438_);
    crate::leanh::lean_ctor_set(v___x_440_, 2, v___x_437_);
    crate::leanh::lean_ctor_set(v___x_440_, 3, v___x_438_);
    crate::leanh::lean_ctor_set(v___x_440_, 4, v___x_438_);
    crate::leanh::lean_ctor_set(v___x_440_, 5, v___x_436_);
    crate::leanh::lean_ctor_set(v___x_440_, 6, v___x_436_);
    crate::leanh::lean_ctor_set(v___x_440_, 7, v___x_436_);
    crate::leanh::lean_ctor_set(v___x_440_, 8, v___x_436_);
    crate::leanh::lean_ctor_set(v___x_440_, 9, v___x_436_);
    crate::leanh::lean_ctor_set(v___x_440_, 10, v___x_436_);
    crate::leanh::lean_ctor_set(v___x_440_, 11, v___x_436_);
    crate::leanh::lean_ctor_set(v___x_440_, 12, v___x_438_);
    crate::leanh::lean_ctor_set(v___x_440_, 13, v___x_436_);
    crate::leanh::lean_ctor_set(v___x_440_, 14, v___x_434_);
    crate::leanh::lean_ctor_set(v___x_440_, 15, v___x_433_);
    crate::leanh::lean_ctor_set(v___x_440_, 16, v___x_433_);
    crate::leanh::lean_ctor_set(v___x_440_, 17, v___x_433_);
    crate::leanh::lean_ctor_set(v___x_440_, 18, v___x_434_);
    crate::leanh::lean_ctor_set(v___x_440_, 19, v___x_434_);
    crate::leanh::lean_ctor_set(v___x_440_, 20, v___x_434_);
    crate::leanh::lean_ctor_set(v___x_440_, 21, v___x_432_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_440_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 22) as u32,
        v___x_435_,
    );
    return v___x_440_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_441_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4,
    );
    return v___x_441_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct() -> *mut crate::leanh::LeanObject {
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_442_ = l_Lean_Meta_Grind_Order_instInhabitedStruct_default;
    return v___x_442_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_443_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_444_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_444_, 0, v___x_443_);
    crate::leanh::lean_ctor_set(v___x_444_, 1, v___x_443_);
    crate::leanh::lean_ctor_set(v___x_444_, 2, v___x_443_);
    return v___x_444_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_445_ = crate::leanh::lean_obj_once(
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_446_ = l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default;
    return v___x_446_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_449_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_449_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_450_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1,
    );
    v___x_451_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_451_, 0, v___x_450_);
    return v___x_451_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_452_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2,
    );
    v___x_453_ = l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0;
    v___x_454_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_454_, 0, v___x_453_);
    crate::leanh::lean_ctor_set(v___x_454_, 1, v___x_452_);
    crate::leanh::lean_ctor_set(v___x_454_, 2, v___x_452_);
    crate::leanh::lean_ctor_set(v___x_454_, 3, v___x_452_);
    crate::leanh::lean_ctor_set(v___x_454_, 4, v___x_452_);
    return v___x_454_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_455_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3,
    );
    return v___x_455_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState() -> *mut crate::leanh::LeanObject {
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_456_ = l_Lean_Meta_Grind_Order_instInhabitedState_default;
    return v___x_456_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_(
    mut v___x_457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_459_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_459_, 0, v___x_457_);
    return v___x_459_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2____boxed(
    mut v___x_460_: *mut crate::leanh::LeanObject,
    mut v___y_461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_462_ = l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_(v___x_460_);
    return v_res_462_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_463_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3,
    );
    v___f_464_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_464_, 0, v___x_463_);
    return v___f_464_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_466_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_);
    v___x_467_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_466_);
    return v___x_467_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2____boxed(
    mut v_a_468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_469_ = l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_();
    return v_res_469_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_get_x27___redArg(
    mut v_a_470_: *mut crate::leanh::LeanObject,
    mut v_a_471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_473_ = l_Lean_Meta_Grind_Order_orderExt;
    v___x_474_ =
        l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_473_, v_a_470_, v_a_471_);
    return v___x_474_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_get_x27___redArg___boxed(
    mut v_a_475_: *mut crate::leanh::LeanObject,
    mut v_a_476_: *mut crate::leanh::LeanObject,
    mut v_a_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_475_, v_a_476_);
    crate::leanh::lean_dec_ref(v_a_476_);
    crate::leanh::lean_dec(v_a_475_);
    return v_res_478_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_get_x27(
    mut v_a_479_: *mut crate::leanh::LeanObject,
    mut v_a_480_: *mut crate::leanh::LeanObject,
    mut v_a_481_: *mut crate::leanh::LeanObject,
    mut v_a_482_: *mut crate::leanh::LeanObject,
    mut v_a_483_: *mut crate::leanh::LeanObject,
    mut v_a_484_: *mut crate::leanh::LeanObject,
    mut v_a_485_: *mut crate::leanh::LeanObject,
    mut v_a_486_: *mut crate::leanh::LeanObject,
    mut v_a_487_: *mut crate::leanh::LeanObject,
    mut v_a_488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_490_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_479_, v_a_487_);
    return v___x_490_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_get_x27___boxed(
    mut v_a_491_: *mut crate::leanh::LeanObject,
    mut v_a_492_: *mut crate::leanh::LeanObject,
    mut v_a_493_: *mut crate::leanh::LeanObject,
    mut v_a_494_: *mut crate::leanh::LeanObject,
    mut v_a_495_: *mut crate::leanh::LeanObject,
    mut v_a_496_: *mut crate::leanh::LeanObject,
    mut v_a_497_: *mut crate::leanh::LeanObject,
    mut v_a_498_: *mut crate::leanh::LeanObject,
    mut v_a_499_: *mut crate::leanh::LeanObject,
    mut v_a_500_: *mut crate::leanh::LeanObject,
    mut v_a_501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_502_ = l_Lean_Meta_Grind_Order_get_x27(
        v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_,
        v_a_500_,
    );
    crate::leanh::lean_dec(v_a_500_);
    crate::leanh::lean_dec_ref(v_a_499_);
    crate::leanh::lean_dec(v_a_498_);
    crate::leanh::lean_dec_ref(v_a_497_);
    crate::leanh::lean_dec(v_a_496_);
    crate::leanh::lean_dec_ref(v_a_495_);
    crate::leanh::lean_dec(v_a_494_);
    crate::leanh::lean_dec_ref(v_a_493_);
    crate::leanh::lean_dec(v_a_492_);
    crate::leanh::lean_dec(v_a_491_);
    return v_res_502_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modify_x27___redArg(
    mut v_f_503_: *mut crate::leanh::LeanObject,
    mut v_a_504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_506_ = l_Lean_Meta_Grind_Order_orderExt;
    v___x_507_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_506_, v_f_503_, v_a_504_);
    return v___x_507_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modify_x27___redArg___boxed(
    mut v_f_508_: *mut crate::leanh::LeanObject,
    mut v_a_509_: *mut crate::leanh::LeanObject,
    mut v_a_510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_511_ = l_Lean_Meta_Grind_Order_modify_x27___redArg(v_f_508_, v_a_509_);
    crate::leanh::lean_dec(v_a_509_);
    return v_res_511_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modify_x27(
    mut v_f_512_: *mut crate::leanh::LeanObject,
    mut v_a_513_: *mut crate::leanh::LeanObject,
    mut v_a_514_: *mut crate::leanh::LeanObject,
    mut v_a_515_: *mut crate::leanh::LeanObject,
    mut v_a_516_: *mut crate::leanh::LeanObject,
    mut v_a_517_: *mut crate::leanh::LeanObject,
    mut v_a_518_: *mut crate::leanh::LeanObject,
    mut v_a_519_: *mut crate::leanh::LeanObject,
    mut v_a_520_: *mut crate::leanh::LeanObject,
    mut v_a_521_: *mut crate::leanh::LeanObject,
    mut v_a_522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_524_ = l_Lean_Meta_Grind_Order_orderExt;
    v___x_525_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_524_, v_f_512_, v_a_513_);
    return v___x_525_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modify_x27___boxed(
    mut v_f_526_: *mut crate::leanh::LeanObject,
    mut v_a_527_: *mut crate::leanh::LeanObject,
    mut v_a_528_: *mut crate::leanh::LeanObject,
    mut v_a_529_: *mut crate::leanh::LeanObject,
    mut v_a_530_: *mut crate::leanh::LeanObject,
    mut v_a_531_: *mut crate::leanh::LeanObject,
    mut v_a_532_: *mut crate::leanh::LeanObject,
    mut v_a_533_: *mut crate::leanh::LeanObject,
    mut v_a_534_: *mut crate::leanh::LeanObject,
    mut v_a_535_: *mut crate::leanh::LeanObject,
    mut v_a_536_: *mut crate::leanh::LeanObject,
    mut v_a_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_538_ = l_Lean_Meta_Grind_Order_modify_x27(
        v_f_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_,
        v_a_535_, v_a_536_,
    );
    crate::leanh::lean_dec(v_a_536_);
    crate::leanh::lean_dec_ref(v_a_535_);
    crate::leanh::lean_dec(v_a_534_);
    crate::leanh::lean_dec_ref(v_a_533_);
    crate::leanh::lean_dec(v_a_532_);
    crate::leanh::lean_dec_ref(v_a_531_);
    crate::leanh::lean_dec(v_a_530_);
    crate::leanh::lean_dec_ref(v_a_529_);
    crate::leanh::lean_dec(v_a_528_);
    crate::leanh::lean_dec(v_a_527_);
    return v_res_538_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_Order_instInhabitedCnstrKind_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstrKind_default();
    l_Lean_Meta_Grind_Order_instInhabitedCnstrKind =
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstrKind();
    l_Lean_Meta_Grind_Order_instInhabitedWeight_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedWeight_default);
    l_Lean_Meta_Grind_Order_instInhabitedWeight =
        _init_l_Lean_Meta_Grind_Order_instInhabitedWeight();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedWeight);
    l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default);
    l_Lean_Meta_Grind_Order_instInhabitedProofInfo =
        _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedProofInfo);
    l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default);
    l_Lean_Meta_Grind_Order_instInhabitedToPropagate =
        _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedToPropagate);
    l_Lean_Meta_Grind_Order_instInhabitedStruct_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedStruct_default);
    l_Lean_Meta_Grind_Order_instInhabitedStruct =
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedStruct);
    l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default);
    l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry =
        _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry);
    l_Lean_Meta_Grind_Order_instInhabitedState_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedState_default);
    l_Lean_Meta_Grind_Order_instInhabitedState = _init_l_Lean_Meta_Grind_Order_instInhabitedState();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedState);
    res = l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Grind_Order_orderExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_orderExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Order_Types(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Order_Types(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
}
