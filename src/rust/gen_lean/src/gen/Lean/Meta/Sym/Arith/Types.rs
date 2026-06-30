// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Types
// Imports: Init.Grind.Ring.CommSemiringAdapter Lean.Meta.Sym.SymM
use crate::r#gen::Init::Grind::Ring::CommSemiringAdapter::{
    initialize_Init_Grind_Ring_CommSemiringAdapter,
    runtime_initialize_Init_Grind_Ring_CommSemiringAdapter,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::l_Lean_Expr_const___override;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM,
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Sym_SymExtension_getState___redArg, l_Lean_Meta_Sym_registerSymExtension___redArg,
    runtime_initialize_Lean_Meta_Sym_SymM,
};
pub static l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__0_value:
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
static mut l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__0_value)
            as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_instInhabitedSemiring: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_instInhabitedRing_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_instInhabitedRing: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_instInhabitedCommRing: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_instInhabitedClassifyResult_default___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Sym_Arith_instInhabitedClassifyResult_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_Arith_instInhabitedClassifyResult_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Arith_instInhabitedClassifyResult_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_Arith_instInhabitedClassifyResult_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Arith_instInhabitedClassifyResult: *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_Arith_instInhabitedClassifyResult_default___closed__0_value
)
    as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__0_value:
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
static mut l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_instInhabitedState_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_instInhabitedState: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_arithExt: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_364_ = leanh::lean_box(0);
    v___x_365_ = l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__1;
    v___x_366_ = l_Lean_Expr_const___override(v___x_365_, v___x_364_);
    return v___x_366_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_367_ = leanh::lean_box(0);
    v___x_368_ = leanh::lean_box(0);
    v___x_369_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once
        ),
        _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2,
    );
    v___x_370_ = leanh::lean_unsigned_to_nat(0);
    v___x_371_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
    leanh::lean_ctor_set(v___x_371_, 0, v___x_370_);
    leanh::lean_ctor_set(v___x_371_, 1, v___x_369_);
    leanh::lean_ctor_set(v___x_371_, 2, v___x_368_);
    leanh::lean_ctor_set(v___x_371_, 3, v___x_369_);
    leanh::lean_ctor_set(v___x_371_, 4, v___x_367_);
    leanh::lean_ctor_set(v___x_371_, 5, v___x_367_);
    leanh::lean_ctor_set(v___x_371_, 6, v___x_367_);
    leanh::lean_ctor_set(v___x_371_, 7, v___x_367_);
    return v___x_371_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default()
-> *mut leanh::LeanObject {
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_372_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3_once
        ),
        _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3,
    );
    return v___x_372_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring() -> *mut leanh::LeanObject {
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_373_ = l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default;
    return v___x_373_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_374_ = leanh::lean_box(0);
    v___x_375_ = leanh::lean_box(0);
    v___x_376_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once
        ),
        _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2,
    );
    v___x_377_ = leanh::lean_unsigned_to_nat(0);
    v___x_378_ = leanh::lean_alloc_ctor(0, 14, (0) as u32);
    leanh::lean_ctor_set(v___x_378_, 0, v___x_377_);
    leanh::lean_ctor_set(v___x_378_, 1, v___x_376_);
    leanh::lean_ctor_set(v___x_378_, 2, v___x_375_);
    leanh::lean_ctor_set(v___x_378_, 3, v___x_376_);
    leanh::lean_ctor_set(v___x_378_, 4, v___x_376_);
    leanh::lean_ctor_set(v___x_378_, 5, v___x_374_);
    leanh::lean_ctor_set(v___x_378_, 6, v___x_374_);
    leanh::lean_ctor_set(v___x_378_, 7, v___x_374_);
    leanh::lean_ctor_set(v___x_378_, 8, v___x_374_);
    leanh::lean_ctor_set(v___x_378_, 9, v___x_374_);
    leanh::lean_ctor_set(v___x_378_, 10, v___x_374_);
    leanh::lean_ctor_set(v___x_378_, 11, v___x_374_);
    leanh::lean_ctor_set(v___x_378_, 12, v___x_374_);
    leanh::lean_ctor_set(v___x_378_, 13, v___x_374_);
    return v___x_378_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedRing_default()
-> *mut leanh::LeanObject {
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_379_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0_once),
        _init_l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0,
    );
    return v___x_379_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedRing() -> *mut leanh::LeanObject {
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = l_Lean_Meta_Sym_Arith_instInhabitedRing_default;
    return v___x_380_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_381_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once
        ),
        _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2,
    );
    v___x_382_ = leanh::lean_box(0);
    v___x_383_ = l_Lean_Meta_Sym_Arith_instInhabitedRing_default;
    v___x_384_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
    leanh::lean_ctor_set(v___x_384_, 0, v___x_383_);
    leanh::lean_ctor_set(v___x_384_, 1, v___x_382_);
    leanh::lean_ctor_set(v___x_384_, 2, v___x_382_);
    leanh::lean_ctor_set(v___x_384_, 3, v___x_381_);
    leanh::lean_ctor_set(v___x_384_, 4, v___x_381_);
    leanh::lean_ctor_set(v___x_384_, 5, v___x_382_);
    leanh::lean_ctor_set(v___x_384_, 6, v___x_382_);
    return v___x_384_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default()
-> *mut leanh::LeanObject {
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_385_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0_once
        ),
        _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0,
    );
    return v___x_385_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing() -> *mut leanh::LeanObject {
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_386_ = l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default;
    return v___x_386_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_387_ = leanh::lean_box(0);
    v___x_388_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once
        ),
        _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2,
    );
    v___x_389_ = leanh::lean_unsigned_to_nat(0);
    v___x_390_ = l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default;
    v___x_391_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_391_, 0, v___x_390_);
    leanh::lean_ctor_set(v___x_391_, 1, v___x_389_);
    leanh::lean_ctor_set(v___x_391_, 2, v___x_388_);
    leanh::lean_ctor_set(v___x_391_, 3, v___x_387_);
    leanh::lean_ctor_set(v___x_391_, 4, v___x_387_);
    return v___x_391_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default()
-> *mut leanh::LeanObject {
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_392_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0_once
        ),
        _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0,
    );
    return v___x_392_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring()
-> *mut leanh::LeanObject {
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_393_ = l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default;
    return v___x_393_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_ctorIdx(
    mut v_x_394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_394_) {
        0 => {
            let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_395_ = leanh::lean_unsigned_to_nat(0);
            return v___x_395_;
        }
        1 => {
            let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_396_ = leanh::lean_unsigned_to_nat(1);
            return v___x_396_;
        }
        2 => {
            let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_397_ = leanh::lean_unsigned_to_nat(2);
            return v___x_397_;
        }
        3 => {
            let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_398_ = leanh::lean_unsigned_to_nat(3);
            return v___x_398_;
        }
        _ => {
            let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_399_ = leanh::lean_unsigned_to_nat(4);
            return v___x_399_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_ctorIdx___boxed(
    mut v_x_400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_401_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorIdx(v_x_400_);
    leanh::lean_dec(v_x_400_);
    return v_res_401_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(
    mut v_t_402_: *mut leanh::LeanObject,
    mut v_k_403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_402_) == 4 {
        return v_k_403_;
    } else {
        let mut v_id_404_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_id_404_ = leanh::lean_ctor_get(v_t_402_, 0);
        leanh::lean_inc(v_id_404_);
        leanh::lean_dec(v_t_402_);
        v___x_405_ = leanh::lean_apply_1(v_k_403_, v_id_404_);
        return v___x_405_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim(
    mut v_motive_406_: *mut leanh::LeanObject,
    mut v_ctorIdx_407_: *mut leanh::LeanObject,
    mut v_t_408_: *mut leanh::LeanObject,
    mut v_h_409_: *mut leanh::LeanObject,
    mut v_k_410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_411_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_408_, v_k_410_);
    return v___x_411_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___boxed(
    mut v_motive_412_: *mut leanh::LeanObject,
    mut v_ctorIdx_413_: *mut leanh::LeanObject,
    mut v_t_414_: *mut leanh::LeanObject,
    mut v_h_415_: *mut leanh::LeanObject,
    mut v_k_416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_417_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim(
        v_motive_412_,
        v_ctorIdx_413_,
        v_t_414_,
        v_h_415_,
        v_k_416_,
    );
    leanh::lean_dec(v_ctorIdx_413_);
    return v_res_417_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_commRing_elim___redArg(
    mut v_t_418_: *mut leanh::LeanObject,
    mut v_commRing_419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_420_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_418_, v_commRing_419_);
    return v___x_420_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_commRing_elim(
    mut v_motive_421_: *mut leanh::LeanObject,
    mut v_t_422_: *mut leanh::LeanObject,
    mut v_h_423_: *mut leanh::LeanObject,
    mut v_commRing_424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_425_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_422_, v_commRing_424_);
    return v___x_425_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommRing_elim___redArg(
    mut v_t_426_: *mut leanh::LeanObject,
    mut v_nonCommRing_427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ =
        l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_426_, v_nonCommRing_427_);
    return v___x_428_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommRing_elim(
    mut v_motive_429_: *mut leanh::LeanObject,
    mut v_t_430_: *mut leanh::LeanObject,
    mut v_h_431_: *mut leanh::LeanObject,
    mut v_nonCommRing_432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_433_ =
        l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_430_, v_nonCommRing_432_);
    return v___x_433_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_commSemiring_elim___redArg(
    mut v_t_434_: *mut leanh::LeanObject,
    mut v_commSemiring_435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_436_ =
        l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_434_, v_commSemiring_435_);
    return v___x_436_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_commSemiring_elim(
    mut v_motive_437_: *mut leanh::LeanObject,
    mut v_t_438_: *mut leanh::LeanObject,
    mut v_h_439_: *mut leanh::LeanObject,
    mut v_commSemiring_440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_441_ =
        l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_438_, v_commSemiring_440_);
    return v___x_441_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommSemiring_elim___redArg(
    mut v_t_442_: *mut leanh::LeanObject,
    mut v_nonCommSemiring_443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_444_ =
        l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_442_, v_nonCommSemiring_443_);
    return v___x_444_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommSemiring_elim(
    mut v_motive_445_: *mut leanh::LeanObject,
    mut v_t_446_: *mut leanh::LeanObject,
    mut v_h_447_: *mut leanh::LeanObject,
    mut v_nonCommSemiring_448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_449_ =
        l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_446_, v_nonCommSemiring_448_);
    return v___x_449_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_none_elim___redArg(
    mut v_t_450_: *mut leanh::LeanObject,
    mut v_none_451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_452_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_450_, v_none_451_);
    return v___x_452_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ClassifyResult_none_elim(
    mut v_motive_453_: *mut leanh::LeanObject,
    mut v_t_454_: *mut leanh::LeanObject,
    mut v_h_455_: *mut leanh::LeanObject,
    mut v_none_456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_457_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_454_, v_none_456_);
    return v___x_457_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_464_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_464_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_465_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1_once),
        _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1,
    );
    v___x_466_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_466_, 0, v___x_465_);
    return v___x_466_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_467_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2_once),
        _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2,
    );
    v___x_468_ = l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__0;
    v___x_469_ = leanh::lean_unsigned_to_nat(8);
    v___x_470_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_470_, 0, v___x_469_);
    leanh::lean_ctor_set(v___x_470_, 1, v___x_468_);
    leanh::lean_ctor_set(v___x_470_, 2, v___x_468_);
    leanh::lean_ctor_set(v___x_470_, 3, v___x_468_);
    leanh::lean_ctor_set(v___x_470_, 4, v___x_468_);
    leanh::lean_ctor_set(v___x_470_, 5, v___x_467_);
    return v___x_470_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default()
-> *mut leanh::LeanObject {
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_471_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3_once),
        _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3,
    );
    return v___x_471_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instInhabitedState() -> *mut leanh::LeanObject {
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_472_ = l_Lean_Meta_Sym_Arith_instInhabitedState_default;
    return v___x_472_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(
    mut v___x_473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_475_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_475_, 0, v___x_473_);
    return v___x_475_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed(
    mut v___x_476_: *mut leanh::LeanObject,
    mut v___y_477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ = l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(v___x_476_);
    return v_res_478_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_479_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3_once),
        _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3,
    );
    v___f_480_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_480_, 0, v___x_479_);
    return v___f_480_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_482_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_);
    v___x_483_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v___f_482_);
    return v___x_483_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed(
    mut v_a_484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_485_ = l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_();
    return v_res_485_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getArithState___redArg(
    mut v_a_486_: *mut leanh::LeanObject,
    mut v_a_487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_489_ = l_Lean_Meta_Sym_Arith_arithExt;
    v___x_490_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v___x_489_, v_a_486_, v_a_487_);
    return v___x_490_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getArithState___redArg___boxed(
    mut v_a_491_: *mut leanh::LeanObject,
    mut v_a_492_: *mut leanh::LeanObject,
    mut v_a_493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_494_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_491_, v_a_492_);
    leanh::lean_dec_ref(v_a_492_);
    leanh::lean_dec(v_a_491_);
    return v_res_494_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getArithState(
    mut v_a_495_: *mut leanh::LeanObject,
    mut v_a_496_: *mut leanh::LeanObject,
    mut v_a_497_: *mut leanh::LeanObject,
    mut v_a_498_: *mut leanh::LeanObject,
    mut v_a_499_: *mut leanh::LeanObject,
    mut v_a_500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_502_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_496_, v_a_499_);
    return v___x_502_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getArithState___boxed(
    mut v_a_503_: *mut leanh::LeanObject,
    mut v_a_504_: *mut leanh::LeanObject,
    mut v_a_505_: *mut leanh::LeanObject,
    mut v_a_506_: *mut leanh::LeanObject,
    mut v_a_507_: *mut leanh::LeanObject,
    mut v_a_508_: *mut leanh::LeanObject,
    mut v_a_509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_510_ = l_Lean_Meta_Sym_Arith_getArithState(
        v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_,
    );
    leanh::lean_dec(v_a_508_);
    leanh::lean_dec_ref(v_a_507_);
    leanh::lean_dec(v_a_506_);
    leanh::lean_dec_ref(v_a_505_);
    leanh::lean_dec(v_a_504_);
    leanh::lean_dec_ref(v_a_503_);
    return v_res_510_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_modifyArithState___redArg(
    mut v_f_511_: *mut leanh::LeanObject,
    mut v_a_512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_514_ = l_Lean_Meta_Sym_Arith_arithExt;
    v___x_515_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(
            v___x_514_, v_f_511_, v_a_512_,
        );
    return v___x_515_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_modifyArithState___redArg___boxed(
    mut v_f_516_: *mut leanh::LeanObject,
    mut v_a_517_: *mut leanh::LeanObject,
    mut v_a_518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_519_ = l_Lean_Meta_Sym_Arith_modifyArithState___redArg(v_f_516_, v_a_517_);
    leanh::lean_dec(v_a_517_);
    return v_res_519_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_modifyArithState(
    mut v_f_520_: *mut leanh::LeanObject,
    mut v_a_521_: *mut leanh::LeanObject,
    mut v_a_522_: *mut leanh::LeanObject,
    mut v_a_523_: *mut leanh::LeanObject,
    mut v_a_524_: *mut leanh::LeanObject,
    mut v_a_525_: *mut leanh::LeanObject,
    mut v_a_526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_528_ = l_Lean_Meta_Sym_Arith_arithExt;
    v___x_529_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(
            v___x_528_, v_f_520_, v_a_522_,
        );
    return v___x_529_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_modifyArithState___boxed(
    mut v_f_530_: *mut leanh::LeanObject,
    mut v_a_531_: *mut leanh::LeanObject,
    mut v_a_532_: *mut leanh::LeanObject,
    mut v_a_533_: *mut leanh::LeanObject,
    mut v_a_534_: *mut leanh::LeanObject,
    mut v_a_535_: *mut leanh::LeanObject,
    mut v_a_536_: *mut leanh::LeanObject,
    mut v_a_537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_538_ = l_Lean_Meta_Sym_Arith_modifyArithState(
        v_f_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_,
    );
    leanh::lean_dec(v_a_536_);
    leanh::lean_dec_ref(v_a_535_);
    leanh::lean_dec(v_a_534_);
    leanh::lean_dec_ref(v_a_533_);
    leanh::lean_dec(v_a_532_);
    leanh::lean_dec_ref(v_a_531_);
    return v_res_538_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(
    mut v_a_539_: *mut leanh::LeanObject,
    mut v_a_540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_546_: u8 = 0;
    let mut v_exp_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_551_: u8 = 0;
    let mut v_a_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_555_: u8 = 0;
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_542_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_539_, v_a_540_);
                if leanh::lean_obj_tag(v___x_542_) == 0 {
                    v_a_543_ = leanh::lean_ctor_get(v___x_542_, 0);
                    v_isSharedCheck_551_ = (!leanh::lean_is_exclusive(v___x_542_)) as u8;
                    if v_isSharedCheck_551_ == 0 {
                        v___x_545_ = v___x_542_;
                        v_isShared_546_ = v_isSharedCheck_551_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_543_);
                        leanh::lean_dec(v___x_542_);
                        v___x_545_ = leanh::lean_box(0);
                        v_isShared_546_ = v_isSharedCheck_551_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_552_ = leanh::lean_ctor_get(v___x_542_, 0);
                    v_isSharedCheck_559_ = (!leanh::lean_is_exclusive(v___x_542_)) as u8;
                    if v_isSharedCheck_559_ == 0 {
                        v___x_554_ = v___x_542_;
                        v_isShared_555_ = v_isSharedCheck_559_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_552_);
                        leanh::lean_dec(v___x_542_);
                        v___x_554_ = leanh::lean_box(0);
                        v_isShared_555_ = v_isSharedCheck_559_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_exp_547_ = leanh::lean_ctor_get(v_a_543_, 0);
                leanh::lean_inc(v_exp_547_);
                leanh::lean_dec(v_a_543_);
                if v_isShared_546_ == 0 {
                    leanh::lean_ctor_set(v___x_545_, 0, v_exp_547_);
                    v___x_549_ = v___x_545_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_550_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_550_, 0, v_exp_547_);
                    v___x_549_ = v_reuseFailAlloc_550_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_549_;
            }
            3 => {
                if v_isShared_555_ == 0 {
                    v___x_557_ = v___x_554_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_558_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
                    v___x_557_ = v_reuseFailAlloc_558_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getExpThreshold___redArg___boxed(
    mut v_a_560_: *mut leanh::LeanObject,
    mut v_a_561_: *mut leanh::LeanObject,
    mut v_a_562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_563_ = l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(v_a_560_, v_a_561_);
    leanh::lean_dec_ref(v_a_561_);
    leanh::lean_dec(v_a_560_);
    return v_res_563_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getExpThreshold(
    mut v_a_564_: *mut leanh::LeanObject,
    mut v_a_565_: *mut leanh::LeanObject,
    mut v_a_566_: *mut leanh::LeanObject,
    mut v_a_567_: *mut leanh::LeanObject,
    mut v_a_568_: *mut leanh::LeanObject,
    mut v_a_569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_571_ = l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(v_a_565_, v_a_568_);
    return v___x_571_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_getExpThreshold___boxed(
    mut v_a_572_: *mut leanh::LeanObject,
    mut v_a_573_: *mut leanh::LeanObject,
    mut v_a_574_: *mut leanh::LeanObject,
    mut v_a_575_: *mut leanh::LeanObject,
    mut v_a_576_: *mut leanh::LeanObject,
    mut v_a_577_: *mut leanh::LeanObject,
    mut v_a_578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_579_ = l_Lean_Meta_Sym_Arith_getExpThreshold(
        v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_,
    );
    leanh::lean_dec(v_a_577_);
    leanh::lean_dec_ref(v_a_576_);
    leanh::lean_dec(v_a_575_);
    leanh::lean_dec_ref(v_a_574_);
    leanh::lean_dec(v_a_573_);
    leanh::lean_dec_ref(v_a_572_);
    return v_res_579_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_setExpThreshold___redArg___lam__0(
    mut v_exp_580_: *mut leanh::LeanObject,
    mut v_s_581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rings_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_593_: u8 = 0;
    let mut v_unused_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_582_ = leanh::lean_ctor_get(v_s_581_, 1);
                v_semirings_583_ = leanh::lean_ctor_get(v_s_581_, 2);
                v_ncRings_584_ = leanh::lean_ctor_get(v_s_581_, 3);
                v_ncSemirings_585_ = leanh::lean_ctor_get(v_s_581_, 4);
                v_typeClassify_586_ = leanh::lean_ctor_get(v_s_581_, 5);
                v_isSharedCheck_593_ = (!leanh::lean_is_exclusive(v_s_581_)) as u8;
                if v_isSharedCheck_593_ == 0 {
                    v_unused_594_ = leanh::lean_ctor_get(v_s_581_, 0);
                    leanh::lean_dec(v_unused_594_);
                    v___x_588_ = v_s_581_;
                    v_isShared_589_ = v_isSharedCheck_593_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeClassify_586_);
                    leanh::lean_inc(v_ncSemirings_585_);
                    leanh::lean_inc(v_ncRings_584_);
                    leanh::lean_inc(v_semirings_583_);
                    leanh::lean_inc(v_rings_582_);
                    leanh::lean_dec(v_s_581_);
                    v___x_588_ = leanh::lean_box(0);
                    v_isShared_589_ = v_isSharedCheck_593_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_589_ == 0 {
                    leanh::lean_ctor_set(v___x_588_, 0, v_exp_580_);
                    v___x_591_ = v___x_588_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_592_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_592_, 0, v_exp_580_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_592_, 1, v_rings_582_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_592_, 2, v_semirings_583_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_592_, 3, v_ncRings_584_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_592_, 4, v_ncSemirings_585_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_592_, 5, v_typeClassify_586_);
                    v___x_591_ = v_reuseFailAlloc_592_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(
    mut v_exp_595_: *mut leanh::LeanObject,
    mut v_a_596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_598_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_setExpThreshold___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_598_, 0, v_exp_595_);
    v___x_599_ = l_Lean_Meta_Sym_Arith_arithExt;
    v___x_600_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(
            v___x_599_, v___f_598_, v_a_596_,
        );
    return v___x_600_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_setExpThreshold___redArg___boxed(
    mut v_exp_601_: *mut leanh::LeanObject,
    mut v_a_602_: *mut leanh::LeanObject,
    mut v_a_603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_604_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_601_, v_a_602_);
    leanh::lean_dec(v_a_602_);
    return v_res_604_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_setExpThreshold(
    mut v_exp_605_: *mut leanh::LeanObject,
    mut v_a_606_: *mut leanh::LeanObject,
    mut v_a_607_: *mut leanh::LeanObject,
    mut v_a_608_: *mut leanh::LeanObject,
    mut v_a_609_: *mut leanh::LeanObject,
    mut v_a_610_: *mut leanh::LeanObject,
    mut v_a_611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_613_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_605_, v_a_607_);
    return v___x_613_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_setExpThreshold___boxed(
    mut v_exp_614_: *mut leanh::LeanObject,
    mut v_a_615_: *mut leanh::LeanObject,
    mut v_a_616_: *mut leanh::LeanObject,
    mut v_a_617_: *mut leanh::LeanObject,
    mut v_a_618_: *mut leanh::LeanObject,
    mut v_a_619_: *mut leanh::LeanObject,
    mut v_a_620_: *mut leanh::LeanObject,
    mut v_a_621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_622_ = l_Lean_Meta_Sym_Arith_setExpThreshold(
        v_exp_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_,
    );
    leanh::lean_dec(v_a_620_);
    leanh::lean_dec_ref(v_a_619_);
    leanh::lean_dec(v_a_618_);
    leanh::lean_dec_ref(v_a_617_);
    leanh::lean_dec(v_a_616_);
    leanh::lean_dec_ref(v_a_615_);
    return v_res_622_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_withExpThreshold___redArg(
    mut v_exp_623_: *mut leanh::LeanObject,
    mut v_k_624_: *mut leanh::LeanObject,
    mut v_a_625_: *mut leanh::LeanObject,
    mut v_a_626_: *mut leanh::LeanObject,
    mut v_a_627_: *mut leanh::LeanObject,
    mut v_a_628_: *mut leanh::LeanObject,
    mut v_a_629_: *mut leanh::LeanObject,
    mut v_a_630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exp_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_641_: u8 = 0;
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_645_: u8 = 0;
    let mut v_unused_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_650_: u8 = 0;
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_654_: u8 = 0;
    let mut v_a_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_659_: u8 = 0;
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_663_: u8 = 0;
    let mut v_unused_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_668_: u8 = 0;
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_672_: u8 = 0;
    let mut v_a_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_676_: u8 = 0;
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_680_: u8 = 0;
    let mut v_a_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_684_: u8 = 0;
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_632_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_626_, v_a_629_);
                if leanh::lean_obj_tag(v___x_632_) == 0 {
                    v_a_633_ = leanh::lean_ctor_get(v___x_632_, 0);
                    leanh::lean_inc(v_a_633_);
                    leanh::lean_dec_ref_known(v___x_632_, 1);
                    v___x_634_ =
                        l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_623_, v_a_626_);
                    if leanh::lean_obj_tag(v___x_634_) == 0 {
                        leanh::lean_dec_ref_known(v___x_634_, 1);
                        v_exp_635_ = leanh::lean_ctor_get(v_a_633_, 0);
                        leanh::lean_inc(v_exp_635_);
                        leanh::lean_dec(v_a_633_);
                        leanh::lean_inc(v_a_630_);
                        leanh::lean_inc_ref(v_a_629_);
                        leanh::lean_inc(v_a_628_);
                        leanh::lean_inc_ref(v_a_627_);
                        leanh::lean_inc(v_a_626_);
                        leanh::lean_inc_ref(v_a_625_);
                        v_r_636_ = leanh::lean_apply_7(
                            v_k_624_,
                            v_a_625_,
                            v_a_626_,
                            v_a_627_,
                            v_a_628_,
                            v_a_629_,
                            v_a_630_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v_r_636_) == 0 {
                            v_a_637_ = leanh::lean_ctor_get(v_r_636_, 0);
                            leanh::lean_inc(v_a_637_);
                            leanh::lean_dec_ref_known(v_r_636_, 1);
                            v___x_638_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(
                                v_exp_635_, v_a_626_,
                            );
                            if leanh::lean_obj_tag(v___x_638_) == 0 {
                                v_isSharedCheck_645_ =
                                    (!leanh::lean_is_exclusive(v___x_638_)) as u8;
                                if v_isSharedCheck_645_ == 0 {
                                    v_unused_646_ = leanh::lean_ctor_get(v___x_638_, 0);
                                    leanh::lean_dec(v_unused_646_);
                                    v___x_640_ = v___x_638_;
                                    v_isShared_641_ = v_isSharedCheck_645_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_638_);
                                    v___x_640_ = leanh::lean_box(0);
                                    v_isShared_641_ = v_isSharedCheck_645_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_637_);
                                v_a_647_ = leanh::lean_ctor_get(v___x_638_, 0);
                                v_isSharedCheck_654_ =
                                    (!leanh::lean_is_exclusive(v___x_638_)) as u8;
                                if v_isSharedCheck_654_ == 0 {
                                    v___x_649_ = v___x_638_;
                                    v_isShared_650_ = v_isSharedCheck_654_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_647_);
                                    leanh::lean_dec(v___x_638_);
                                    v___x_649_ = leanh::lean_box(0);
                                    v_isShared_650_ = v_isSharedCheck_654_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_a_655_ = leanh::lean_ctor_get(v_r_636_, 0);
                            leanh::lean_inc(v_a_655_);
                            leanh::lean_dec_ref_known(v_r_636_, 1);
                            v___x_656_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(
                                v_exp_635_, v_a_626_,
                            );
                            if leanh::lean_obj_tag(v___x_656_) == 0 {
                                v_isSharedCheck_663_ =
                                    (!leanh::lean_is_exclusive(v___x_656_)) as u8;
                                if v_isSharedCheck_663_ == 0 {
                                    v_unused_664_ = leanh::lean_ctor_get(v___x_656_, 0);
                                    leanh::lean_dec(v_unused_664_);
                                    v___x_658_ = v___x_656_;
                                    v_isShared_659_ = v_isSharedCheck_663_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_656_);
                                    v___x_658_ = leanh::lean_box(0);
                                    v_isShared_659_ = v_isSharedCheck_663_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_655_);
                                v_a_665_ = leanh::lean_ctor_get(v___x_656_, 0);
                                v_isSharedCheck_672_ =
                                    (!leanh::lean_is_exclusive(v___x_656_)) as u8;
                                if v_isSharedCheck_672_ == 0 {
                                    v___x_667_ = v___x_656_;
                                    v_isShared_668_ = v_isSharedCheck_672_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_665_);
                                    leanh::lean_dec(v___x_656_);
                                    v___x_667_ = leanh::lean_box(0);
                                    v_isShared_668_ = v_isSharedCheck_672_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_633_);
                        leanh::lean_dec_ref(v_k_624_);
                        v_a_673_ = leanh::lean_ctor_get(v___x_634_, 0);
                        v_isSharedCheck_680_ = (!leanh::lean_is_exclusive(v___x_634_)) as u8;
                        if v_isSharedCheck_680_ == 0 {
                            v___x_675_ = v___x_634_;
                            v_isShared_676_ = v_isSharedCheck_680_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_673_);
                            leanh::lean_dec(v___x_634_);
                            v___x_675_ = leanh::lean_box(0);
                            v_isShared_676_ = v_isSharedCheck_680_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_k_624_);
                    leanh::lean_dec(v_exp_623_);
                    v_a_681_ = leanh::lean_ctor_get(v___x_632_, 0);
                    v_isSharedCheck_688_ = (!leanh::lean_is_exclusive(v___x_632_)) as u8;
                    if v_isSharedCheck_688_ == 0 {
                        v___x_683_ = v___x_632_;
                        v_isShared_684_ = v_isSharedCheck_688_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_681_);
                        leanh::lean_dec(v___x_632_);
                        v___x_683_ = leanh::lean_box(0);
                        v_isShared_684_ = v_isSharedCheck_688_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_641_ == 0 {
                    leanh::lean_ctor_set(v___x_640_, 0, v_a_637_);
                    v___x_643_ = v___x_640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_644_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_637_);
                    v___x_643_ = v_reuseFailAlloc_644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_643_;
            }
            3 => {
                if v_isShared_650_ == 0 {
                    v___x_652_ = v___x_649_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_653_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
                    v___x_652_ = v_reuseFailAlloc_653_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_652_;
            }
            5 => {
                if v_isShared_659_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_658_, 1);
                    leanh::lean_ctor_set(v___x_658_, 0, v_a_655_);
                    v___x_661_ = v___x_658_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_662_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_655_);
                    v___x_661_ = v_reuseFailAlloc_662_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_661_;
            }
            7 => {
                if v_isShared_668_ == 0 {
                    v___x_670_ = v___x_667_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_671_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
                    v___x_670_ = v_reuseFailAlloc_671_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_670_;
            }
            9 => {
                if v_isShared_676_ == 0 {
                    v___x_678_ = v___x_675_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_679_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
                    v___x_678_ = v_reuseFailAlloc_679_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_678_;
            }
            11 => {
                if v_isShared_684_ == 0 {
                    v___x_686_ = v___x_683_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_687_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
                    v___x_686_ = v_reuseFailAlloc_687_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_withExpThreshold___redArg___boxed(
    mut v_exp_689_: *mut leanh::LeanObject,
    mut v_k_690_: *mut leanh::LeanObject,
    mut v_a_691_: *mut leanh::LeanObject,
    mut v_a_692_: *mut leanh::LeanObject,
    mut v_a_693_: *mut leanh::LeanObject,
    mut v_a_694_: *mut leanh::LeanObject,
    mut v_a_695_: *mut leanh::LeanObject,
    mut v_a_696_: *mut leanh::LeanObject,
    mut v_a_697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_698_ = l_Lean_Meta_Sym_Arith_withExpThreshold___redArg(
        v_exp_689_, v_k_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_,
    );
    leanh::lean_dec(v_a_696_);
    leanh::lean_dec_ref(v_a_695_);
    leanh::lean_dec(v_a_694_);
    leanh::lean_dec_ref(v_a_693_);
    leanh::lean_dec(v_a_692_);
    leanh::lean_dec_ref(v_a_691_);
    return v_res_698_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_withExpThreshold(
    mut v_00_u03b1_699_: *mut leanh::LeanObject,
    mut v_exp_700_: *mut leanh::LeanObject,
    mut v_k_701_: *mut leanh::LeanObject,
    mut v_a_702_: *mut leanh::LeanObject,
    mut v_a_703_: *mut leanh::LeanObject,
    mut v_a_704_: *mut leanh::LeanObject,
    mut v_a_705_: *mut leanh::LeanObject,
    mut v_a_706_: *mut leanh::LeanObject,
    mut v_a_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ = l_Lean_Meta_Sym_Arith_withExpThreshold___redArg(
        v_exp_700_, v_k_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_,
    );
    return v___x_709_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_withExpThreshold___boxed(
    mut v_00_u03b1_710_: *mut leanh::LeanObject,
    mut v_exp_711_: *mut leanh::LeanObject,
    mut v_k_712_: *mut leanh::LeanObject,
    mut v_a_713_: *mut leanh::LeanObject,
    mut v_a_714_: *mut leanh::LeanObject,
    mut v_a_715_: *mut leanh::LeanObject,
    mut v_a_716_: *mut leanh::LeanObject,
    mut v_a_717_: *mut leanh::LeanObject,
    mut v_a_718_: *mut leanh::LeanObject,
    mut v_a_719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_720_ = l_Lean_Meta_Sym_Arith_withExpThreshold(
        v_00_u03b1_710_,
        v_exp_711_,
        v_k_712_,
        v_a_713_,
        v_a_714_,
        v_a_715_,
        v_a_716_,
        v_a_717_,
        v_a_718_,
    );
    leanh::lean_dec(v_a_718_);
    leanh::lean_dec_ref(v_a_717_);
    leanh::lean_dec(v_a_716_);
    leanh::lean_dec_ref(v_a_715_);
    leanh::lean_dec(v_a_714_);
    leanh::lean_dec_ref(v_a_713_);
    return v_res_720_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_Types(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default =
        _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default);
    l_Lean_Meta_Sym_Arith_instInhabitedSemiring =
        _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedSemiring);
    l_Lean_Meta_Sym_Arith_instInhabitedRing_default =
        _init_l_Lean_Meta_Sym_Arith_instInhabitedRing_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedRing_default);
    l_Lean_Meta_Sym_Arith_instInhabitedRing = _init_l_Lean_Meta_Sym_Arith_instInhabitedRing();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedRing);
    l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default =
        _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default);
    l_Lean_Meta_Sym_Arith_instInhabitedCommRing =
        _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedCommRing);
    l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default =
        _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default);
    l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring =
        _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring);
    l_Lean_Meta_Sym_Arith_instInhabitedState_default =
        _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedState_default);
    l_Lean_Meta_Sym_Arith_instInhabitedState = _init_l_Lean_Meta_Sym_Arith_instInhabitedState();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedState);
    res = l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Sym_Arith_arithExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_arithExt);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_Types(
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
pub unsafe fn initialize_Lean_Meta_Sym_Arith_Types(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_Types(builtin);
}