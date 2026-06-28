// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.Types
// Imports: Lean.Meta.Tactic.Grind.Types
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::l_Lean_Expr_const___override;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types,
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_SolverExtension_getState___redArg,
    l_Lean_Meta_Grind_registerSolverExtension___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_6, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static mut l_Lean_Meta_Grind_Order_instInhabitedCnstrKind_default: u8 = 0;
pub static mut l_Lean_Meta_Grind_Order_instInhabitedCnstrKind: u8 = 0;
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__1_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__1_value
        ) as *mut LeanObject,
        17542774118954891045 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedWeight_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedWeight: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedProofInfo: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedToPropagate: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedStruct_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedStruct: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedState_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instInhabitedState: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx(mut v_x_270_: u8) -> *mut LeanObject {
    if v_x_270_ == 0 {
        let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
        v___x_271_ = lean_unsigned_to_nat(0);
        return v___x_271_;
    } else {
        let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
        v___x_272_ = lean_unsigned_to_nat(1);
        return v___x_272_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx___boxed(
    mut v_x_273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_274_: u8 = 0;
    let mut v_res_275_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_274_ = (lean_unbox(v_x_273_) as u8);
    v_res_275_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx(v_x_boxed_274_);
    return v_res_275_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_toCtorIdx(mut v_x_276_: u8) -> *mut LeanObject {
    let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
    v___x_277_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorIdx(v_x_276_);
    return v___x_277_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_toCtorIdx___boxed(
    mut v_x_278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_279_: u8 = 0;
    let mut v_res_280_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_279_ = (lean_unbox(v_x_278_) as u8);
    v_res_280_ = l_Lean_Meta_Grind_Order_CnstrKind_toCtorIdx(v_x_4__boxed_279_);
    return v_res_280_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___redArg(
    mut v_k_281_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_281_);
    return v_k_281_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___redArg___boxed(
    mut v_k_282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_283_: *mut LeanObject = core::ptr::null_mut();
    v_res_283_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___redArg(v_k_282_);
    lean_dec(v_k_282_);
    return v_res_283_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorElim(
    mut v_motive_284_: *mut LeanObject,
    mut v_ctorIdx_285_: *mut LeanObject,
    mut v_t_286_: u8,
    mut v_h_287_: *mut LeanObject,
    mut v_k_288_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_288_);
    return v_k_288_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_ctorElim___boxed(
    mut v_motive_289_: *mut LeanObject,
    mut v_ctorIdx_290_: *mut LeanObject,
    mut v_t_291_: *mut LeanObject,
    mut v_h_292_: *mut LeanObject,
    mut v_k_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_294_: u8 = 0;
    let mut v_res_295_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_294_ = (lean_unbox(v_t_291_) as u8);
    v_res_295_ = l_Lean_Meta_Grind_Order_CnstrKind_ctorElim(
        v_motive_289_,
        v_ctorIdx_290_,
        v_t_boxed_294_,
        v_h_292_,
        v_k_293_,
    );
    lean_dec(v_k_293_);
    lean_dec(v_ctorIdx_290_);
    return v_res_295_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_le_elim___redArg(
    mut v_le_296_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_le_296_);
    return v_le_296_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_le_elim___redArg___boxed(
    mut v_le_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_298_: *mut LeanObject = core::ptr::null_mut();
    v_res_298_ = l_Lean_Meta_Grind_Order_CnstrKind_le_elim___redArg(v_le_297_);
    lean_dec(v_le_297_);
    return v_res_298_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_le_elim(
    mut v_motive_299_: *mut LeanObject,
    mut v_t_300_: u8,
    mut v_h_301_: *mut LeanObject,
    mut v_le_302_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_le_302_);
    return v_le_302_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_le_elim___boxed(
    mut v_motive_303_: *mut LeanObject,
    mut v_t_304_: *mut LeanObject,
    mut v_h_305_: *mut LeanObject,
    mut v_le_306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_307_: u8 = 0;
    let mut v_res_308_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_307_ = (lean_unbox(v_t_304_) as u8);
    v_res_308_ = l_Lean_Meta_Grind_Order_CnstrKind_le_elim(
        v_motive_303_,
        v_t_boxed_307_,
        v_h_305_,
        v_le_306_,
    );
    lean_dec(v_le_306_);
    return v_res_308_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___redArg(
    mut v_lt_309_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_lt_309_);
    return v_lt_309_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___redArg___boxed(
    mut v_lt_310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_311_: *mut LeanObject = core::ptr::null_mut();
    v_res_311_ = l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___redArg(v_lt_310_);
    lean_dec(v_lt_310_);
    return v_res_311_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_lt_elim(
    mut v_motive_312_: *mut LeanObject,
    mut v_t_313_: u8,
    mut v_h_314_: *mut LeanObject,
    mut v_lt_315_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_lt_315_);
    return v_lt_315_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_CnstrKind_lt_elim___boxed(
    mut v_motive_316_: *mut LeanObject,
    mut v_t_317_: *mut LeanObject,
    mut v_h_318_: *mut LeanObject,
    mut v_lt_319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_320_: u8 = 0;
    let mut v_res_321_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_320_ = (lean_unbox(v_t_317_) as u8);
    v_res_321_ = l_Lean_Meta_Grind_Order_CnstrKind_lt_elim(
        v_motive_316_,
        v_t_boxed_320_,
        v_h_318_,
        v_lt_319_,
    );
    lean_dec(v_lt_319_);
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
-> *mut LeanObject {
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
    v___x_324_ = lean_unsigned_to_nat(0);
    v___x_325_ = lean_nat_to_int(v___x_324_);
    return v___x_325_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    v___x_329_ = lean_box(0);
    v___x_330_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__2;
    v___x_331_ = l_Lean_Expr_const___override(v___x_330_, v___x_329_);
    return v___x_331_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(
    mut v_inst_332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_333_: u8 = 0;
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    v___x_333_ = 0;
    v___x_334_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0,
    );
    v___x_335_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_336_ = lean_box(0);
    lean_inc(v_inst_332_);
    v___x_337_ = lean_alloc_ctor(0, 5, (1) as u32);
    lean_ctor_set(v___x_337_, 0, v_inst_332_);
    lean_ctor_set(v___x_337_, 1, v_inst_332_);
    lean_ctor_set(v___x_337_, 2, v___x_334_);
    lean_ctor_set(v___x_337_, 3, v___x_335_);
    lean_ctor_set(v___x_337_, 4, v___x_336_);
    lean_ctor_set_uint8(
        v___x_337_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_333_,
    );
    return v___x_337_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instInhabitedCnstr_default(
    mut v_00_u03b1_338_: *mut LeanObject,
    mut v_inst_339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    v___x_340_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v_inst_339_);
    return v___x_340_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instInhabitedCnstr___redArg(
    mut v_inst_341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    v___x_342_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v_inst_341_);
    return v___x_342_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instInhabitedCnstr(
    mut v_a_343_: *mut LeanObject,
    mut v_inst_344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    v___x_345_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v_inst_344_);
    return v___x_345_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0()
-> *mut LeanObject {
    let mut v___x_346_: u8 = 0;
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    v___x_346_ = 0;
    v___x_347_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__0,
    );
    v___x_348_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_348_, 0, v___x_347_);
    lean_ctor_set_uint8(
        v___x_348_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_346_,
    );
    return v___x_348_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default() -> *mut LeanObject {
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    v___x_349_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default___closed__0,
    );
    return v___x_349_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedWeight() -> *mut LeanObject {
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    v___x_350_ = l_Lean_Meta_Grind_Order_instInhabitedWeight_default;
    return v___x_350_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0()
-> *mut LeanObject {
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    v___x_351_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_352_ = l_Lean_Meta_Grind_Order_instInhabitedWeight_default;
    v___x_353_ = lean_unsigned_to_nat(0);
    v___x_354_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_354_, 0, v___x_353_);
    lean_ctor_set(v___x_354_, 1, v___x_352_);
    lean_ctor_set(v___x_354_, 2, v___x_351_);
    return v___x_354_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default() -> *mut LeanObject {
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    v___x_355_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default___closed__0,
    );
    return v___x_355_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo() -> *mut LeanObject {
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    v___x_356_ = l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default;
    return v___x_356_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_ctorIdx(
    mut v_x_357_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_357_) {
        0 => {
            let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
            v___x_358_ = lean_unsigned_to_nat(0);
            return v___x_358_;
        }
        1 => {
            let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
            v___x_359_ = lean_unsigned_to_nat(1);
            return v___x_359_;
        }
        _ => {
            let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
            v___x_360_ = lean_unsigned_to_nat(2);
            return v___x_360_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_ctorIdx___boxed(
    mut v_x_361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_362_: *mut LeanObject = core::ptr::null_mut();
    v_res_362_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorIdx(v_x_361_);
    lean_dec_ref(v_x_361_);
    return v_res_362_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(
    mut v_t_363_: *mut LeanObject,
    mut v_k_364_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_363_) == 2 {
        let mut v_u_365_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
        v_u_365_ = lean_ctor_get(v_t_363_, 0);
        lean_inc(v_u_365_);
        v_v_366_ = lean_ctor_get(v_t_363_, 1);
        lean_inc(v_v_366_);
        lean_dec_ref_known(v_t_363_, 2);
        v___x_367_ = lean_apply_2(v_k_364_, v_u_365_, v_v_366_);
        return v___x_367_;
    } else {
        let mut v_c_368_: *mut LeanObject = core::ptr::null_mut();
        let mut v_e_369_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_370_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_371_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_372_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_x27_373_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
        v_c_368_ = lean_ctor_get(v_t_363_, 0);
        lean_inc_ref(v_c_368_);
        v_e_369_ = lean_ctor_get(v_t_363_, 1);
        lean_inc_ref(v_e_369_);
        v_u_370_ = lean_ctor_get(v_t_363_, 2);
        lean_inc(v_u_370_);
        v_v_371_ = lean_ctor_get(v_t_363_, 3);
        lean_inc(v_v_371_);
        v_k_372_ = lean_ctor_get(v_t_363_, 4);
        lean_inc_ref(v_k_372_);
        v_k_x27_373_ = lean_ctor_get(v_t_363_, 5);
        lean_inc_ref(v_k_x27_373_);
        lean_dec_ref(v_t_363_);
        v___x_374_ = lean_apply_6(
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
    mut v_motive_375_: *mut LeanObject,
    mut v_ctorIdx_376_: *mut LeanObject,
    mut v_t_377_: *mut LeanObject,
    mut v_h_378_: *mut LeanObject,
    mut v_k_379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    v___x_380_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_377_, v_k_379_);
    return v___x_380_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___boxed(
    mut v_motive_381_: *mut LeanObject,
    mut v_ctorIdx_382_: *mut LeanObject,
    mut v_t_383_: *mut LeanObject,
    mut v_h_384_: *mut LeanObject,
    mut v_k_385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_386_: *mut LeanObject = core::ptr::null_mut();
    v_res_386_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim(
        v_motive_381_,
        v_ctorIdx_382_,
        v_t_383_,
        v_h_384_,
        v_k_385_,
    );
    lean_dec(v_ctorIdx_382_);
    return v_res_386_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eqTrue_elim___redArg(
    mut v_t_387_: *mut LeanObject,
    mut v_eqTrue_388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    v___x_389_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_387_, v_eqTrue_388_);
    return v___x_389_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eqTrue_elim(
    mut v_motive_390_: *mut LeanObject,
    mut v_t_391_: *mut LeanObject,
    mut v_h_392_: *mut LeanObject,
    mut v_eqTrue_393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    v___x_394_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_391_, v_eqTrue_393_);
    return v___x_394_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eqFalse_elim___redArg(
    mut v_t_395_: *mut LeanObject,
    mut v_eqFalse_396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    v___x_397_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_395_, v_eqFalse_396_);
    return v___x_397_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eqFalse_elim(
    mut v_motive_398_: *mut LeanObject,
    mut v_t_399_: *mut LeanObject,
    mut v_h_400_: *mut LeanObject,
    mut v_eqFalse_401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    v___x_402_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_399_, v_eqFalse_401_);
    return v___x_402_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eq_elim___redArg(
    mut v_t_403_: *mut LeanObject,
    mut v_eq_404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    v___x_405_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_403_, v_eq_404_);
    return v___x_405_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_eq_elim(
    mut v_motive_406_: *mut LeanObject,
    mut v_t_407_: *mut LeanObject,
    mut v_h_408_: *mut LeanObject,
    mut v_eq_409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    v___x_410_ = l_Lean_Meta_Grind_Order_ToPropagate_ctorElim___redArg(v_t_407_, v_eq_409_);
    return v___x_410_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0()
-> *mut LeanObject {
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    v___x_411_ = lean_unsigned_to_nat(0);
    v___x_412_ = l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg(v___x_411_);
    return v___x_412_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__1()
-> *mut LeanObject {
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    v___x_413_ = l_Lean_Meta_Grind_Order_instInhabitedWeight_default;
    v___x_414_ = lean_unsigned_to_nat(0);
    v___x_415_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_416_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default___closed__0,
    );
    v___x_417_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_417_, 0, v___x_416_);
    lean_ctor_set(v___x_417_, 1, v___x_415_);
    lean_ctor_set(v___x_417_, 2, v___x_414_);
    lean_ctor_set(v___x_417_, 3, v___x_414_);
    lean_ctor_set(v___x_417_, 4, v___x_413_);
    lean_ctor_set(v___x_417_, 5, v___x_413_);
    return v___x_417_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default() -> *mut LeanObject {
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    v___x_418_ = lean_obj_once(
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
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate() -> *mut LeanObject {
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    v___x_419_ = l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default;
    return v___x_419_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0()
-> *mut LeanObject {
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    v___x_420_ = lean_unsigned_to_nat(32);
    v___x_421_ = lean_mk_empty_array_with_capacity(v___x_420_);
    v___x_422_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_422_, 0, v___x_421_);
    return v___x_422_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1()
-> *mut LeanObject {
    let mut v___x_423_: usize = 0;
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    v___x_423_ = 5usize;
    v___x_424_ = lean_unsigned_to_nat(0);
    v___x_425_ = lean_unsigned_to_nat(32);
    v___x_426_ = lean_mk_empty_array_with_capacity(v___x_425_);
    v___x_427_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__0,
    );
    v___x_428_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_428_, 0, v___x_427_);
    lean_ctor_set(v___x_428_, 1, v___x_426_);
    lean_ctor_set(v___x_428_, 2, v___x_424_);
    lean_ctor_set(v___x_428_, 3, v___x_424_);
    lean_ctor_set_usize(v___x_428_, 4, v___x_423_);
    return v___x_428_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2()
-> *mut LeanObject {
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    v___x_429_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_429_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3()
-> *mut LeanObject {
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    v___x_430_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__2,
    );
    v___x_431_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_431_, 0, v___x_430_);
    return v___x_431_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4()
-> *mut LeanObject {
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_435_: u8 = 0;
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    v___x_432_ = lean_box(0);
    v___x_433_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__3,
    );
    v___x_434_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__1,
    );
    v___x_435_ = 0;
    v___x_436_ = lean_box(0);
    v___x_437_ = lean_box(0);
    v___x_438_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_439_ = lean_unsigned_to_nat(0);
    v___x_440_ = lean_alloc_ctor(0, 22, (1) as u32);
    lean_ctor_set(v___x_440_, 0, v___x_439_);
    lean_ctor_set(v___x_440_, 1, v___x_438_);
    lean_ctor_set(v___x_440_, 2, v___x_437_);
    lean_ctor_set(v___x_440_, 3, v___x_438_);
    lean_ctor_set(v___x_440_, 4, v___x_438_);
    lean_ctor_set(v___x_440_, 5, v___x_436_);
    lean_ctor_set(v___x_440_, 6, v___x_436_);
    lean_ctor_set(v___x_440_, 7, v___x_436_);
    lean_ctor_set(v___x_440_, 8, v___x_436_);
    lean_ctor_set(v___x_440_, 9, v___x_436_);
    lean_ctor_set(v___x_440_, 10, v___x_436_);
    lean_ctor_set(v___x_440_, 11, v___x_436_);
    lean_ctor_set(v___x_440_, 12, v___x_438_);
    lean_ctor_set(v___x_440_, 13, v___x_436_);
    lean_ctor_set(v___x_440_, 14, v___x_434_);
    lean_ctor_set(v___x_440_, 15, v___x_433_);
    lean_ctor_set(v___x_440_, 16, v___x_433_);
    lean_ctor_set(v___x_440_, 17, v___x_433_);
    lean_ctor_set(v___x_440_, 18, v___x_434_);
    lean_ctor_set(v___x_440_, 19, v___x_434_);
    lean_ctor_set(v___x_440_, 20, v___x_434_);
    lean_ctor_set(v___x_440_, 21, v___x_432_);
    lean_ctor_set_uint8(
        v___x_440_,
        (core::mem::size_of::<*mut LeanObject>() * 22) as u32,
        v___x_435_,
    );
    return v___x_440_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default() -> *mut LeanObject {
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    v___x_441_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default___closed__4,
    );
    return v___x_441_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedStruct() -> *mut LeanObject {
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    v___x_442_ = l_Lean_Meta_Grind_Order_instInhabitedStruct_default;
    return v___x_442_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default___closed__0()
-> *mut LeanObject {
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    v___x_443_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstr_default___redArg___closed__3,
    );
    v___x_444_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_444_, 0, v___x_443_);
    lean_ctor_set(v___x_444_, 1, v___x_443_);
    lean_ctor_set(v___x_444_, 2, v___x_443_);
    return v___x_444_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default() -> *mut LeanObject {
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    v___x_445_ = lean_obj_once(
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
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry() -> *mut LeanObject {
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    v___x_446_ = l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default;
    return v___x_446_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1()
-> *mut LeanObject {
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    v___x_449_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_449_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2()
-> *mut LeanObject {
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    v___x_450_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__1,
    );
    v___x_451_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_451_, 0, v___x_450_);
    return v___x_451_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3()
-> *mut LeanObject {
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    v___x_452_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__2,
    );
    v___x_453_ = l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__0;
    v___x_454_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_454_, 0, v___x_453_);
    lean_ctor_set(v___x_454_, 1, v___x_452_);
    lean_ctor_set(v___x_454_, 2, v___x_452_);
    lean_ctor_set(v___x_454_, 3, v___x_452_);
    lean_ctor_set(v___x_454_, 4, v___x_452_);
    return v___x_454_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState_default() -> *mut LeanObject {
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    v___x_455_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3,
    );
    return v___x_455_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instInhabitedState() -> *mut LeanObject {
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    v___x_456_ = l_Lean_Meta_Grind_Order_instInhabitedState_default;
    return v___x_456_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_(
    mut v___x_457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    v___x_459_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_459_, 0, v___x_457_);
    return v___x_459_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2____boxed(
    mut v___x_460_: *mut LeanObject,
    mut v___y_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_462_: *mut LeanObject = core::ptr::null_mut();
    v_res_462_ = l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_(v___x_460_);
    return v_res_462_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_464_: *mut LeanObject = core::ptr::null_mut();
    v___x_463_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default___closed__3,
    );
    v___f_464_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_464_, 0, v___x_463_);
    return v___f_464_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    v___f_466_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_);
    v___x_467_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_466_);
    return v___x_467_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2____boxed(
    mut v_a_468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_469_: *mut LeanObject = core::ptr::null_mut();
    v_res_469_ = l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_();
    return v_res_469_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_get_x27___redArg(
    mut v_a_470_: *mut LeanObject,
    mut v_a_471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    v___x_473_ = l_Lean_Meta_Grind_Order_orderExt;
    v___x_474_ =
        l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_473_, v_a_470_, v_a_471_);
    return v___x_474_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_get_x27___redArg___boxed(
    mut v_a_475_: *mut LeanObject,
    mut v_a_476_: *mut LeanObject,
    mut v_a_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_478_: *mut LeanObject = core::ptr::null_mut();
    v_res_478_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_475_, v_a_476_);
    lean_dec_ref(v_a_476_);
    lean_dec(v_a_475_);
    return v_res_478_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_get_x27(
    mut v_a_479_: *mut LeanObject,
    mut v_a_480_: *mut LeanObject,
    mut v_a_481_: *mut LeanObject,
    mut v_a_482_: *mut LeanObject,
    mut v_a_483_: *mut LeanObject,
    mut v_a_484_: *mut LeanObject,
    mut v_a_485_: *mut LeanObject,
    mut v_a_486_: *mut LeanObject,
    mut v_a_487_: *mut LeanObject,
    mut v_a_488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    v___x_490_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_479_, v_a_487_);
    return v___x_490_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_get_x27___boxed(
    mut v_a_491_: *mut LeanObject,
    mut v_a_492_: *mut LeanObject,
    mut v_a_493_: *mut LeanObject,
    mut v_a_494_: *mut LeanObject,
    mut v_a_495_: *mut LeanObject,
    mut v_a_496_: *mut LeanObject,
    mut v_a_497_: *mut LeanObject,
    mut v_a_498_: *mut LeanObject,
    mut v_a_499_: *mut LeanObject,
    mut v_a_500_: *mut LeanObject,
    mut v_a_501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_502_: *mut LeanObject = core::ptr::null_mut();
    v_res_502_ = l_Lean_Meta_Grind_Order_get_x27(
        v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_,
        v_a_500_,
    );
    lean_dec(v_a_500_);
    lean_dec_ref(v_a_499_);
    lean_dec(v_a_498_);
    lean_dec_ref(v_a_497_);
    lean_dec(v_a_496_);
    lean_dec_ref(v_a_495_);
    lean_dec(v_a_494_);
    lean_dec_ref(v_a_493_);
    lean_dec(v_a_492_);
    lean_dec(v_a_491_);
    return v_res_502_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modify_x27___redArg(
    mut v_f_503_: *mut LeanObject,
    mut v_a_504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    v___x_506_ = l_Lean_Meta_Grind_Order_orderExt;
    v___x_507_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_506_, v_f_503_, v_a_504_);
    return v___x_507_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modify_x27___redArg___boxed(
    mut v_f_508_: *mut LeanObject,
    mut v_a_509_: *mut LeanObject,
    mut v_a_510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_511_: *mut LeanObject = core::ptr::null_mut();
    v_res_511_ = l_Lean_Meta_Grind_Order_modify_x27___redArg(v_f_508_, v_a_509_);
    lean_dec(v_a_509_);
    return v_res_511_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modify_x27(
    mut v_f_512_: *mut LeanObject,
    mut v_a_513_: *mut LeanObject,
    mut v_a_514_: *mut LeanObject,
    mut v_a_515_: *mut LeanObject,
    mut v_a_516_: *mut LeanObject,
    mut v_a_517_: *mut LeanObject,
    mut v_a_518_: *mut LeanObject,
    mut v_a_519_: *mut LeanObject,
    mut v_a_520_: *mut LeanObject,
    mut v_a_521_: *mut LeanObject,
    mut v_a_522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    v___x_524_ = l_Lean_Meta_Grind_Order_orderExt;
    v___x_525_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_524_, v_f_512_, v_a_513_);
    return v___x_525_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_modify_x27___boxed(
    mut v_f_526_: *mut LeanObject,
    mut v_a_527_: *mut LeanObject,
    mut v_a_528_: *mut LeanObject,
    mut v_a_529_: *mut LeanObject,
    mut v_a_530_: *mut LeanObject,
    mut v_a_531_: *mut LeanObject,
    mut v_a_532_: *mut LeanObject,
    mut v_a_533_: *mut LeanObject,
    mut v_a_534_: *mut LeanObject,
    mut v_a_535_: *mut LeanObject,
    mut v_a_536_: *mut LeanObject,
    mut v_a_537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_538_: *mut LeanObject = core::ptr::null_mut();
    v_res_538_ = l_Lean_Meta_Grind_Order_modify_x27(
        v_f_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_,
        v_a_535_, v_a_536_,
    );
    lean_dec(v_a_536_);
    lean_dec_ref(v_a_535_);
    lean_dec(v_a_534_);
    lean_dec_ref(v_a_533_);
    lean_dec(v_a_532_);
    lean_dec_ref(v_a_531_);
    lean_dec(v_a_530_);
    lean_dec_ref(v_a_529_);
    lean_dec(v_a_528_);
    lean_dec(v_a_527_);
    return v_res_538_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Grind_Order_instInhabitedCnstrKind_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstrKind_default();
    l_Lean_Meta_Grind_Order_instInhabitedCnstrKind =
        _init_l_Lean_Meta_Grind_Order_instInhabitedCnstrKind();
    l_Lean_Meta_Grind_Order_instInhabitedWeight_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedWeight_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedWeight_default);
    l_Lean_Meta_Grind_Order_instInhabitedWeight =
        _init_l_Lean_Meta_Grind_Order_instInhabitedWeight();
    lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedWeight);
    l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedProofInfo_default);
    l_Lean_Meta_Grind_Order_instInhabitedProofInfo =
        _init_l_Lean_Meta_Grind_Order_instInhabitedProofInfo();
    lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedProofInfo);
    l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedToPropagate_default);
    l_Lean_Meta_Grind_Order_instInhabitedToPropagate =
        _init_l_Lean_Meta_Grind_Order_instInhabitedToPropagate();
    lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedToPropagate);
    l_Lean_Meta_Grind_Order_instInhabitedStruct_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedStruct_default);
    l_Lean_Meta_Grind_Order_instInhabitedStruct =
        _init_l_Lean_Meta_Grind_Order_instInhabitedStruct();
    lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedStruct);
    l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry_default);
    l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry =
        _init_l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry();
    lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedTermMapEntry);
    l_Lean_Meta_Grind_Order_instInhabitedState_default =
        _init_l_Lean_Meta_Grind_Order_instInhabitedState_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedState_default);
    l_Lean_Meta_Grind_Order_instInhabitedState = _init_l_Lean_Meta_Grind_Order_instInhabitedState();
    lean_mark_persistent(l_Lean_Meta_Grind_Order_instInhabitedState);
    res = l___private_Lean_Meta_Tactic_Grind_Order_Types_0__Lean_Meta_Grind_Order_initFn_00___x40_Lean_Meta_Tactic_Grind_Order_Types_4206127938____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Grind_Order_orderExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_Grind_Order_orderExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
}
