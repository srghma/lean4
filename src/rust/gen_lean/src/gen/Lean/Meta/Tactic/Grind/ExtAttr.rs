// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ExtAttr
// Imports: Lean.Meta.Tactic.Ext Lean.Meta.Tactic.Grind.Extension
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_set, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_lt,
    lean_st_ref_get, lean_uint64_of_nat, lean_uint64_to_usize, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_eraseIdx___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_isUnaryNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofConstName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Tactic::Ext::{
    initialize_Lean_Meta_Tactic_Ext, l_Lean_Meta_Ext_isExtTheorem___redArg,
    runtime_initialize_Lean_Meta_Tactic_Ext,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Extension::{
    initialize_Lean_Meta_Tactic_Grind_Extension,
    runtime_initialize_Lean_Meta_Tactic_Grind_Extension,
};
use crate::r#gen::Lean::Structure::l_Lean_isStructure;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_validateExtAttr___closed__0_value: leanh::LeanStringObject<25> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 96, 91, 103, 114, 105, 110, 100, 32, 101, 120,
            116, 93, 96, 44, 32, 96, 0,
        ],
    };
static mut l_Lean_Meta_Grind_validateExtAttr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_validateExtAttr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_validateExtAttr___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_validateExtAttr___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_validateExtAttr___closed__2_value: leanh::LeanStringObject<52> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 52,
        m_capacity: 52,
        m_length: 51,
        m_data: [
            96, 32, 105, 115, 32, 110, 101, 105, 116, 104, 101, 114, 32, 116, 97, 103, 103, 101,
            100, 32, 119, 105, 116, 104, 32, 96, 91, 101, 120, 116, 93, 96, 32, 110, 111, 114, 32,
            105, 115, 32, 97, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 0,
        ],
    };
static mut l_Lean_Meta_Grind_validateExtAttr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_validateExtAttr___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_validateExtAttr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_validateExtAttr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0: u64 = 0;
pub static l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__2_value:
    leanh::LeanStringObject<49> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 109, 97, 114, 107, 101, 100, 32, 119, 105, 116,
        104, 32, 116, 104, 101, 32, 96, 91, 103, 114, 105, 110, 100, 32, 101, 120, 116, 93, 96, 32,
        97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_368_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_368_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__0);
    v___x_370_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_370_, 0, v___x_369_);
    return v___x_370_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_371_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1);
    v___x_372_ = leanh::lean_unsigned_to_nat(0);
    v___x_373_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_373_, 0, v___x_372_);
    leanh::lean_ctor_set(v___x_373_, 1, v___x_372_);
    leanh::lean_ctor_set(v___x_373_, 2, v___x_372_);
    leanh::lean_ctor_set(v___x_373_, 3, v___x_372_);
    leanh::lean_ctor_set(v___x_373_, 4, v___x_371_);
    leanh::lean_ctor_set(v___x_373_, 5, v___x_371_);
    leanh::lean_ctor_set(v___x_373_, 6, v___x_371_);
    leanh::lean_ctor_set(v___x_373_, 7, v___x_371_);
    leanh::lean_ctor_set(v___x_373_, 8, v___x_371_);
    leanh::lean_ctor_set(v___x_373_, 9, v___x_371_);
    return v___x_373_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_374_ = leanh::lean_unsigned_to_nat(32);
    v___x_375_ = lean_mk_empty_array_with_capacity(v___x_374_);
    v___x_376_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_376_, 0, v___x_375_);
    return v___x_376_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_377_: usize = 0;
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = 5usize;
    v___x_378_ = leanh::lean_unsigned_to_nat(0);
    v___x_379_ = leanh::lean_unsigned_to_nat(32);
    v___x_380_ = lean_mk_empty_array_with_capacity(v___x_379_);
    v___x_381_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__3);
    v___x_382_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_382_, 0, v___x_381_);
    leanh::lean_ctor_set(v___x_382_, 1, v___x_380_);
    leanh::lean_ctor_set(v___x_382_, 2, v___x_378_);
    leanh::lean_ctor_set(v___x_382_, 3, v___x_378_);
    leanh::lean_ctor_set_usize(v___x_382_, 4, v___x_377_);
    return v___x_382_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_383_ = leanh::lean_box(1);
    v___x_384_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__4);
    v___x_385_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__1);
    v___x_386_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_386_, 0, v___x_385_);
    leanh::lean_ctor_set(v___x_386_, 1, v___x_384_);
    leanh::lean_ctor_set(v___x_386_, 2, v___x_383_);
    return v___x_386_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0(
    mut v_msgData_387_: *mut leanh::LeanObject,
    mut v___y_388_: *mut leanh::LeanObject,
    mut v___y_389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_391_ = lean_st_ref_get(v___y_389_);
    v_env_392_ = leanh::lean_ctor_get(v___x_391_, 0);
    leanh::lean_inc_ref(v_env_392_);
    leanh::lean_dec(v___x_391_);
    v_options_393_ = leanh::lean_ctor_get(v___y_388_, 2);
    v___x_394_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__2);
    v___x_395_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_393_);
    v___x_396_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_396_, 0, v_env_392_);
    leanh::lean_ctor_set(v___x_396_, 1, v___x_394_);
    leanh::lean_ctor_set(v___x_396_, 2, v___x_395_);
    leanh::lean_ctor_set(v___x_396_, 3, v_options_393_);
    v___x_397_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_397_, 0, v___x_396_);
    leanh::lean_ctor_set(v___x_397_, 1, v_msgData_387_);
    v___x_398_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_398_, 0, v___x_397_);
    return v___x_398_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0___boxed(
    mut v_msgData_399_: *mut leanh::LeanObject,
    mut v___y_400_: *mut leanh::LeanObject,
    mut v___y_401_: *mut leanh::LeanObject,
    mut v___y_402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_403_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0(v_msgData_399_, v___y_400_, v___y_401_);
    leanh::lean_dec(v___y_401_);
    leanh::lean_dec_ref(v___y_400_);
    return v_res_403_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg(
    mut v_msg_404_: *mut leanh::LeanObject,
    mut v___y_405_: *mut leanh::LeanObject,
    mut v___y_406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_413_: u8 = 0;
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_418_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_408_ = leanh::lean_ctor_get(v___y_405_, 5);
                v___x_409_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0_spec__0(v_msg_404_, v___y_405_, v___y_406_);
                v_a_410_ = leanh::lean_ctor_get(v___x_409_, 0);
                v_isSharedCheck_418_ = (!leanh::lean_is_exclusive(v___x_409_)) as u8;
                if v_isSharedCheck_418_ == 0 {
                    v___x_412_ = v___x_409_;
                    v_isShared_413_ = v_isSharedCheck_418_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_410_);
                    leanh::lean_dec(v___x_409_);
                    v___x_412_ = leanh::lean_box(0);
                    v_isShared_413_ = v_isSharedCheck_418_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_408_);
                v___x_414_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_414_, 0, v_ref_408_);
                leanh::lean_ctor_set(v___x_414_, 1, v_a_410_);
                if v_isShared_413_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_412_, 1);
                    leanh::lean_ctor_set(v___x_412_, 0, v___x_414_);
                    v___x_416_ = v___x_412_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_417_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
                    v___x_416_ = v_reuseFailAlloc_417_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_416_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg___boxed(
    mut v_msg_419_: *mut leanh::LeanObject,
    mut v___y_420_: *mut leanh::LeanObject,
    mut v___y_421_: *mut leanh::LeanObject,
    mut v___y_422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_423_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg(
        v_msg_419_, v___y_420_, v___y_421_,
    );
    leanh::lean_dec(v___y_421_);
    leanh::lean_dec_ref(v___y_420_);
    return v_res_423_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_validateExtAttr___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_425_ = l_Lean_Meta_Grind_validateExtAttr___closed__0;
    v___x_426_ = l_Lean_stringToMessageData(v___x_425_);
    return v___x_426_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_validateExtAttr___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ = l_Lean_Meta_Grind_validateExtAttr___closed__2;
    v___x_429_ = l_Lean_stringToMessageData(v___x_428_);
    return v___x_429_;
}
pub unsafe fn l_Lean_Meta_Grind_validateExtAttr(
    mut v_declName_430_: *mut leanh::LeanObject,
    mut v_a_431_: *mut leanh::LeanObject,
    mut v_a_432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_438_: u8 = 0;
    let mut v___x_439_: u8 = 0;
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: u8 = 0;
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_457_: u8 = 0;
    let mut v_a_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_461_: u8 = 0;
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_465_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_430_);
                v___x_434_ = l_Lean_Meta_Ext_isExtTheorem___redArg(v_declName_430_, v_a_432_);
                if leanh::lean_obj_tag(v___x_434_) == 0 {
                    v_a_435_ = leanh::lean_ctor_get(v___x_434_, 0);
                    v_isSharedCheck_457_ = (!leanh::lean_is_exclusive(v___x_434_)) as u8;
                    if v_isSharedCheck_457_ == 0 {
                        v___x_437_ = v___x_434_;
                        v_isShared_438_ = v_isSharedCheck_457_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_435_);
                        leanh::lean_dec(v___x_434_);
                        v___x_437_ = leanh::lean_box(0);
                        v_isShared_438_ = v_isSharedCheck_457_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_430_);
                    v_a_458_ = leanh::lean_ctor_get(v___x_434_, 0);
                    v_isSharedCheck_465_ = (!leanh::lean_is_exclusive(v___x_434_)) as u8;
                    if v_isSharedCheck_465_ == 0 {
                        v___x_460_ = v___x_434_;
                        v_isShared_461_ = v_isSharedCheck_465_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_458_);
                        leanh::lean_dec(v___x_434_);
                        v___x_460_ = leanh::lean_box(0);
                        v_isShared_461_ = v_isSharedCheck_465_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_439_ = (leanh::lean_unbox(v_a_435_) as u8);
                leanh::lean_dec(v_a_435_);
                if v___x_439_ == 0 {
                    v___x_440_ = lean_st_ref_get(v_a_432_);
                    v_env_441_ = leanh::lean_ctor_get(v___x_440_, 0);
                    leanh::lean_inc_ref(v_env_441_);
                    leanh::lean_dec(v___x_440_);
                    leanh::lean_inc(v_declName_430_);
                    v___x_442_ = l_Lean_isStructure(v_env_441_, v_declName_430_);
                    if v___x_442_ == 0 {
                        leanh::lean_del_object(v___x_437_);
                        v___x_443_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_validateExtAttr___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_validateExtAttr___closed__1_once
                            ),
                            _init_l_Lean_Meta_Grind_validateExtAttr___closed__1,
                        );
                        v___x_444_ = l_Lean_MessageData_ofConstName(v_declName_430_, v___x_442_);
                        v___x_445_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_445_, 0, v___x_443_);
                        leanh::lean_ctor_set(v___x_445_, 1, v___x_444_);
                        v___x_446_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_validateExtAttr___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_validateExtAttr___closed__3_once
                            ),
                            _init_l_Lean_Meta_Grind_validateExtAttr___closed__3,
                        );
                        v___x_447_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_447_, 0, v___x_445_);
                        leanh::lean_ctor_set(v___x_447_, 1, v___x_446_);
                        v___x_448_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg(v___x_447_, v_a_431_, v_a_432_);
                        return v___x_448_;
                    } else {
                        leanh::lean_dec(v_declName_430_);
                        v___x_449_ = leanh::lean_box(0);
                        if v_isShared_438_ == 0 {
                            leanh::lean_ctor_set(v___x_437_, 0, v___x_449_);
                            v___x_451_ = v___x_437_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_452_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
                            v___x_451_ = v_reuseFailAlloc_452_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_declName_430_);
                    v___x_453_ = leanh::lean_box(0);
                    if v_isShared_438_ == 0 {
                        leanh::lean_ctor_set(v___x_437_, 0, v___x_453_);
                        v___x_455_ = v___x_437_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_456_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
                        v___x_455_ = v_reuseFailAlloc_456_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_451_;
            }
            3 => {
                return v___x_455_;
            }
            4 => {
                if v_isShared_461_ == 0 {
                    v___x_463_ = v___x_460_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_464_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
                    v___x_463_ = v_reuseFailAlloc_464_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_463_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_validateExtAttr___boxed(
    mut v_declName_466_: *mut leanh::LeanObject,
    mut v_a_467_: *mut leanh::LeanObject,
    mut v_a_468_: *mut leanh::LeanObject,
    mut v_a_469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_470_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_466_, v_a_467_, v_a_468_);
    leanh::lean_dec(v_a_468_);
    leanh::lean_dec_ref(v_a_467_);
    return v_res_470_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0(
    mut v_00_u03b1_471_: *mut leanh::LeanObject,
    mut v_msg_472_: *mut leanh::LeanObject,
    mut v___y_473_: *mut leanh::LeanObject,
    mut v___y_474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_476_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg(
        v_msg_472_, v___y_473_, v___y_474_,
    );
    return v___x_476_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___boxed(
    mut v_00_u03b1_477_: *mut leanh::LeanObject,
    mut v_msg_478_: *mut leanh::LeanObject,
    mut v___y_479_: *mut leanh::LeanObject,
    mut v___y_480_: *mut leanh::LeanObject,
    mut v___y_481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_482_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0(
        v_00_u03b1_477_,
        v_msg_478_,
        v___y_479_,
        v___y_480_,
    );
    leanh::lean_dec(v___y_480_);
    leanh::lean_dec_ref(v___y_479_);
    return v_res_482_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg(
    mut v_keys_483_: *mut leanh::LeanObject,
    mut v_i_484_: *mut leanh::LeanObject,
    mut v_k_485_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: u8 = 0;
    let mut v_k_x27_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: u8 = 0;
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_486_ = lean_array_get_size(v_keys_483_);
                v___x_487_ = lean_nat_dec_lt(v_i_484_, v___x_486_);
                if v___x_487_ == 0 {
                    leanh::lean_dec(v_i_484_);
                    return v___x_487_;
                } else {
                    v_k_x27_488_ = lean_array_fget_borrowed(v_keys_483_, v_i_484_);
                    v___x_489_ = lean_name_eq(v_k_485_, v_k_x27_488_);
                    if v___x_489_ == 0 {
                        v___x_490_ = leanh::lean_unsigned_to_nat(1);
                        v___x_491_ = lean_nat_add(v_i_484_, v___x_490_);
                        leanh::lean_dec(v_i_484_);
                        v_i_484_ = v___x_491_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_484_);
                        return v___x_489_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_493_: *mut leanh::LeanObject,
    mut v_i_494_: *mut leanh::LeanObject,
    mut v_k_495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_496_: u8 = 0;
    let mut v_r_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_496_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg(v_keys_493_, v_i_494_, v_k_495_);
    leanh::lean_dec(v_k_495_);
    leanh::lean_dec_ref(v_keys_493_);
    v_r_497_ = leanh::lean_box((v_res_496_) as usize);
    return v_r_497_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_498_: usize = 0;
    let mut v___x_499_: usize = 0;
    let mut v___x_500_: usize = 0;
    v___x_498_ = 5usize;
    v___x_499_ = 1usize;
    v___x_500_ = lean_usize_shift_left(v___x_499_, v___x_498_);
    return v___x_500_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_501_: usize = 0;
    let mut v___x_502_: usize = 0;
    let mut v___x_503_: usize = 0;
    v___x_501_ = 1usize;
    v___x_502_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__0);
    v___x_503_ = lean_usize_sub(v___x_502_, v___x_501_);
    return v___x_503_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg(
    mut v_x_504_: *mut leanh::LeanObject,
    mut v_x_505_: usize,
    mut v_x_506_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: usize = 0;
    let mut v___x_510_: usize = 0;
    let mut v___x_511_: usize = 0;
    let mut v_j_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: u8 = 0;
    let mut v_node_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: usize = 0;
    let mut v___x_519_: u8 = 0;
    let mut v_ks_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_504_) == 0 {
                    v_es_507_ = leanh::lean_ctor_get(v_x_504_, 0);
                    v___x_508_ = leanh::lean_box(2);
                    v___x_509_ = 5usize;
                    v___x_510_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__1);
                    v___x_511_ = lean_usize_land(v_x_505_, v___x_510_);
                    v_j_512_ = lean_usize_to_nat(v___x_511_);
                    v___x_513_ = lean_array_get_borrowed(v___x_508_, v_es_507_, v_j_512_);
                    leanh::lean_dec(v_j_512_);
                    match leanh::lean_obj_tag(v___x_513_) {
                        0 => {
                            v_key_514_ = leanh::lean_ctor_get(v___x_513_, 0);
                            v___x_515_ = lean_name_eq(v_x_506_, v_key_514_);
                            return v___x_515_;
                        }
                        1 => {
                            v_node_516_ = leanh::lean_ctor_get(v___x_513_, 0);
                            v___x_517_ = lean_usize_shift_right(v_x_505_, v___x_509_);
                            v_x_504_ = v_node_516_;
                            v_x_505_ = v___x_517_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_519_ = 0;
                            return v___x_519_;
                        }
                    }
                } else {
                    v_ks_520_ = leanh::lean_ctor_get(v_x_504_, 0);
                    v___x_521_ = leanh::lean_unsigned_to_nat(0);
                    v___x_522_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg(v_ks_520_, v___x_521_, v_x_506_);
                    return v___x_522_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___boxed(
    mut v_x_523_: *mut leanh::LeanObject,
    mut v_x_524_: *mut leanh::LeanObject,
    mut v_x_525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_526__boxed_526_: usize = 0;
    let mut v_res_527_: u8 = 0;
    let mut v_r_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_526__boxed_526_ = leanh::lean_unbox_usize(v_x_524_);
    leanh::lean_dec(v_x_524_);
    v_res_527_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg(v_x_523_, v_x_526__boxed_526_, v_x_525_);
    leanh::lean_dec(v_x_525_);
    leanh::lean_dec_ref(v_x_523_);
    v_r_528_ = leanh::lean_box((v_res_527_) as usize);
    return v_r_528_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: u64 = 0;
    v___x_529_ = leanh::lean_unsigned_to_nat(1723);
    v___x_530_ = lean_uint64_of_nat(v___x_529_);
    return v___x_530_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg(
    mut v_x_531_: *mut leanh::LeanObject,
    mut v_x_532_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_534_: u64 = 0;
    let mut v___x_535_: usize = 0;
    let mut v___x_536_: u8 = 0;
    let mut v___x_537_: u64 = 0;
    let mut v_hash_538_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_532_) == 0 {
                    v___x_537_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0);
                    v___y_534_ = v___x_537_;
                    state = 1;
                    continue;
                } else {
                    v_hash_538_ = leanh::lean_ctor_get_uint64(
                        v_x_532_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_534_ = v_hash_538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_535_ = lean_uint64_to_usize(v___y_534_);
                v___x_536_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg(v_x_531_, v___x_535_, v_x_532_);
                return v___x_536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___boxed(
    mut v_x_539_: *mut leanh::LeanObject,
    mut v_x_540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_541_: u8 = 0;
    let mut v_r_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_541_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg(v_x_539_, v_x_540_);
    leanh::lean_dec(v_x_540_);
    leanh::lean_dec_ref(v_x_539_);
    v_r_542_ = leanh::lean_box((v_res_541_) as usize);
    return v_r_542_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4_spec__5(
    mut v_xs_543_: *mut leanh::LeanObject,
    mut v_v_544_: *mut leanh::LeanObject,
    mut v_i_545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: u8 = 0;
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_546_ = lean_array_get_size(v_xs_543_);
                v___x_547_ = lean_nat_dec_lt(v_i_545_, v___x_546_);
                if v___x_547_ == 0 {
                    leanh::lean_dec(v_i_545_);
                    v___x_548_ = leanh::lean_box(0);
                    return v___x_548_;
                } else {
                    v___x_549_ = lean_array_fget_borrowed(v_xs_543_, v_i_545_);
                    v___x_550_ = lean_name_eq(v___x_549_, v_v_544_);
                    if v___x_550_ == 0 {
                        v___x_551_ = leanh::lean_unsigned_to_nat(1);
                        v___x_552_ = lean_nat_add(v_i_545_, v___x_551_);
                        leanh::lean_dec(v_i_545_);
                        v_i_545_ = v___x_552_;
                        state = 0;
                        continue;
                    } else {
                        v___x_554_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_554_, 0, v_i_545_);
                        return v___x_554_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4_spec__5___boxed(
    mut v_xs_555_: *mut leanh::LeanObject,
    mut v_v_556_: *mut leanh::LeanObject,
    mut v_i_557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_558_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4_spec__5(v_xs_555_, v_v_556_, v_i_557_);
    leanh::lean_dec(v_v_556_);
    leanh::lean_dec_ref(v_xs_555_);
    return v_res_558_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4(
    mut v_xs_559_: *mut leanh::LeanObject,
    mut v_v_560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_561_ = leanh::lean_unsigned_to_nat(0);
    v___x_562_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4_spec__5(v_xs_559_, v_v_560_, v___x_561_);
    return v___x_562_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4___boxed(
    mut v_xs_563_: *mut leanh::LeanObject,
    mut v_v_564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_565_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4(v_xs_563_, v_v_564_);
    leanh::lean_dec(v_v_564_);
    leanh::lean_dec_ref(v_xs_563_);
    return v_res_565_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(
    mut v_x_566_: *mut leanh::LeanObject,
    mut v_x_567_: usize,
    mut v_x_568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: usize = 0;
    let mut v___x_572_: usize = 0;
    let mut v___x_573_: usize = 0;
    let mut v_j_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: u8 = 0;
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_580_: u8 = 0;
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_585_: u8 = 0;
    let mut v_unused_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v_node_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_593_: u8 = 0;
    let mut v_entries_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: usize = 0;
    let mut v_newNode_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_610_: u8 = 0;
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_618_: u8 = 0;
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut v_isSharedCheck_620_: u8 = 0;
    let mut v_unused_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_626_: u8 = 0;
    let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_x27_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vals_x27_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_566_) == 0 {
                    v_es_569_ = leanh::lean_ctor_get(v_x_566_, 0);
                    v___x_570_ = leanh::lean_box(2);
                    v___x_571_ = 5usize;
                    v___x_572_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg___closed__1);
                    v___x_573_ = lean_usize_land(v_x_567_, v___x_572_);
                    v_j_574_ = lean_usize_to_nat(v___x_573_);
                    v_entry_575_ = lean_array_get(v___x_570_, v_es_569_, v_j_574_);
                    match leanh::lean_obj_tag(v_entry_575_) {
                        0 => {
                            v_key_576_ = leanh::lean_ctor_get(v_entry_575_, 0);
                            leanh::lean_inc(v_key_576_);
                            leanh::lean_dec_ref_known(v_entry_575_, 2);
                            v___x_577_ = lean_name_eq(v_x_568_, v_key_576_);
                            leanh::lean_dec(v_key_576_);
                            if v___x_577_ == 0 {
                                leanh::lean_dec(v_j_574_);
                                return v_x_566_;
                            } else {
                                leanh::lean_inc_ref(v_es_569_);
                                v_isSharedCheck_585_ =
                                    (!leanh::lean_is_exclusive(v_x_566_)) as u8;
                                if v_isSharedCheck_585_ == 0 {
                                    v_unused_586_ = leanh::lean_ctor_get(v_x_566_, 0);
                                    leanh::lean_dec(v_unused_586_);
                                    v___x_579_ = v_x_566_;
                                    v_isShared_580_ = v_isSharedCheck_585_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_x_566_);
                                    v___x_579_ = leanh::lean_box(0);
                                    v_isShared_580_ = v_isSharedCheck_585_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            leanh::lean_inc_ref(v_es_569_);
                            v_isSharedCheck_620_ =
                                (!leanh::lean_is_exclusive(v_x_566_)) as u8;
                            if v_isSharedCheck_620_ == 0 {
                                v_unused_621_ = leanh::lean_ctor_get(v_x_566_, 0);
                                leanh::lean_dec(v_unused_621_);
                                v___x_588_ = v_x_566_;
                                v_isShared_589_ = v_isSharedCheck_620_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v_x_566_);
                                v___x_588_ = leanh::lean_box(0);
                                v_isShared_589_ = v_isSharedCheck_620_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            leanh::lean_dec(v_j_574_);
                            return v_x_566_;
                        }
                    }
                } else {
                    v_ks_622_ = leanh::lean_ctor_get(v_x_566_, 0);
                    v_vs_623_ = leanh::lean_ctor_get(v_x_566_, 1);
                    v_isSharedCheck_637_ = (!leanh::lean_is_exclusive(v_x_566_)) as u8;
                    if v_isSharedCheck_637_ == 0 {
                        v___x_625_ = v_x_566_;
                        v_isShared_626_ = v_isSharedCheck_637_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_623_);
                        leanh::lean_inc(v_ks_622_);
                        leanh::lean_dec(v_x_566_);
                        v___x_625_ = leanh::lean_box(0);
                        v_isShared_626_ = v_isSharedCheck_637_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_581_ = lean_array_set(v_es_569_, v_j_574_, v___x_570_);
                leanh::lean_dec(v_j_574_);
                if v_isShared_580_ == 0 {
                    leanh::lean_ctor_set(v___x_579_, 0, v___x_581_);
                    v___x_583_ = v___x_579_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_584_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
                    v___x_583_ = v_reuseFailAlloc_584_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_583_;
            }
            3 => {
                v_node_590_ = leanh::lean_ctor_get(v_entry_575_, 0);
                v_isSharedCheck_619_ = (!leanh::lean_is_exclusive(v_entry_575_)) as u8;
                if v_isSharedCheck_619_ == 0 {
                    v___x_592_ = v_entry_575_;
                    v_isShared_593_ = v_isSharedCheck_619_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_node_590_);
                    leanh::lean_dec(v_entry_575_);
                    v___x_592_ = leanh::lean_box(0);
                    v_isShared_593_ = v_isSharedCheck_619_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_entries_594_ = lean_array_set(v_es_569_, v_j_574_, v___x_570_);
                v___x_595_ = lean_usize_shift_right(v_x_567_, v___x_571_);
                v_newNode_596_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(v_node_590_, v___x_595_, v_x_568_);
                leanh::lean_inc_ref(v_newNode_596_);
                v___x_597_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_596_);
                if leanh::lean_obj_tag(v___x_597_) == 0 {
                    if v_isShared_593_ == 0 {
                        leanh::lean_ctor_set(v___x_592_, 0, v_newNode_596_);
                        v___x_599_ = v___x_592_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_604_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_604_, 0, v_newNode_596_);
                        v___x_599_ = v_reuseFailAlloc_604_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_newNode_596_);
                    leanh::lean_del_object(v___x_592_);
                    v_val_605_ = leanh::lean_ctor_get(v___x_597_, 0);
                    leanh::lean_inc(v_val_605_);
                    leanh::lean_dec_ref_known(v___x_597_, 1);
                    v_fst_606_ = leanh::lean_ctor_get(v_val_605_, 0);
                    v_snd_607_ = leanh::lean_ctor_get(v_val_605_, 1);
                    v_isSharedCheck_618_ = (!leanh::lean_is_exclusive(v_val_605_)) as u8;
                    if v_isSharedCheck_618_ == 0 {
                        v___x_609_ = v_val_605_;
                        v_isShared_610_ = v_isSharedCheck_618_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_607_);
                        leanh::lean_inc(v_fst_606_);
                        leanh::lean_dec(v_val_605_);
                        v___x_609_ = leanh::lean_box(0);
                        v_isShared_610_ = v_isSharedCheck_618_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_600_ = lean_array_set(v_entries_594_, v_j_574_, v___x_599_);
                leanh::lean_dec(v_j_574_);
                if v_isShared_589_ == 0 {
                    leanh::lean_ctor_set(v___x_588_, 0, v___x_600_);
                    v___x_602_ = v___x_588_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_603_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
                    v___x_602_ = v_reuseFailAlloc_603_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_602_;
            }
            7 => {
                if v_isShared_610_ == 0 {
                    v___x_612_ = v___x_609_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_617_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_617_, 0, v_fst_606_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_617_, 1, v_snd_607_);
                    v___x_612_ = v_reuseFailAlloc_617_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_613_ = lean_array_set(v_entries_594_, v_j_574_, v___x_612_);
                leanh::lean_dec(v_j_574_);
                if v_isShared_589_ == 0 {
                    leanh::lean_ctor_set(v___x_588_, 0, v___x_613_);
                    v___x_615_ = v___x_588_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_616_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
                    v___x_615_ = v_reuseFailAlloc_616_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_615_;
            }
            10 => {
                v___x_627_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2_spec__4(v_ks_622_, v_x_568_);
                if leanh::lean_obj_tag(v___x_627_) == 0 {
                    if v_isShared_626_ == 0 {
                        v___x_629_ = v___x_625_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_630_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_630_, 0, v_ks_622_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_630_, 1, v_vs_623_);
                        v___x_629_ = v_reuseFailAlloc_630_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_val_631_ = leanh::lean_ctor_get(v___x_627_, 0);
                    leanh::lean_inc_n(v_val_631_, 2);
                    leanh::lean_dec_ref_known(v___x_627_, 1);
                    v_keys_x27_632_ = l_Array_eraseIdx___redArg(v_ks_622_, v_val_631_);
                    v_vals_x27_633_ = l_Array_eraseIdx___redArg(v_vs_623_, v_val_631_);
                    if v_isShared_626_ == 0 {
                        leanh::lean_ctor_set(v___x_625_, 1, v_vals_x27_633_);
                        leanh::lean_ctor_set(v___x_625_, 0, v_keys_x27_632_);
                        v___x_635_ = v___x_625_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_636_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_636_, 0, v_keys_x27_632_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_636_, 1, v_vals_x27_633_);
                        v___x_635_ = v_reuseFailAlloc_636_;
                        state = 12;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_629_;
            }
            12 => {
                return v___x_635_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg___boxed(
    mut v_x_638_: *mut leanh::LeanObject,
    mut v_x_639_: *mut leanh::LeanObject,
    mut v_x_640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_623__boxed_641_: usize = 0;
    let mut v_res_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_623__boxed_641_ = leanh::lean_unbox_usize(v_x_639_);
    leanh::lean_dec(v_x_639_);
    v_res_642_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(v_x_638_, v_x_623__boxed_641_, v_x_640_);
    leanh::lean_dec(v_x_640_);
    return v_res_642_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg(
    mut v_x_643_: *mut leanh::LeanObject,
    mut v_x_644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_646_: u64 = 0;
    let mut v_h_647_: usize = 0;
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: u64 = 0;
    let mut v_hash_650_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_644_) == 0 {
                    v___x_649_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg___closed__0);
                    v___y_646_ = v___x_649_;
                    state = 1;
                    continue;
                } else {
                    v_hash_650_ = leanh::lean_ctor_get_uint64(
                        v_x_644_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_646_ = v_hash_650_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_h_647_ = lean_uint64_to_usize(v___y_646_);
                v___x_648_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(v_x_643_, v_h_647_, v_x_644_);
                return v___x_648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg___boxed(
    mut v_x_651_: *mut leanh::LeanObject,
    mut v_x_652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_653_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg(v_x_651_, v_x_652_);
    leanh::lean_dec(v_x_652_);
    return v_res_653_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_655_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__0;
    v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
    return v___x_656_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_658_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__2;
    v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
    return v___x_659_;
}
pub unsafe fn l_Lean_Meta_Grind_ExtTheorems_eraseDecl(
    mut v_s_660_: *mut leanh::LeanObject,
    mut v_declName_661_: *mut leanh::LeanObject,
    mut v_a_662_: *mut leanh::LeanObject,
    mut v_a_663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_665_: u8 = 0;
    v___x_665_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg(v_s_660_, v_declName_661_);
    if v___x_665_ == 0 {
        let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_660_);
        v___x_666_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1_once),
            _init_l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__1,
        );
        v___x_667_ = l_Lean_MessageData_ofConstName(v_declName_661_, v___x_665_);
        v___x_668_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_668_, 0, v___x_666_);
        leanh::lean_ctor_set(v___x_668_, 1, v___x_667_);
        v___x_669_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3_once),
            _init_l_Lean_Meta_Grind_ExtTheorems_eraseDecl___closed__3,
        );
        v___x_670_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_670_, 0, v___x_668_);
        leanh::lean_ctor_set(v___x_670_, 1, v___x_669_);
        v___x_671_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateExtAttr_spec__0___redArg(
            v___x_670_, v_a_662_, v_a_663_,
        );
        return v___x_671_;
    } else {
        let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_672_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg(v_s_660_, v_declName_661_);
        leanh::lean_dec(v_declName_661_);
        v___x_673_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_673_, 0, v___x_672_);
        return v___x_673_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_ExtTheorems_eraseDecl___boxed(
    mut v_s_674_: *mut leanh::LeanObject,
    mut v_declName_675_: *mut leanh::LeanObject,
    mut v_a_676_: *mut leanh::LeanObject,
    mut v_a_677_: *mut leanh::LeanObject,
    mut v_a_678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_679_ =
        l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_s_674_, v_declName_675_, v_a_676_, v_a_677_);
    leanh::lean_dec(v_a_677_);
    leanh::lean_dec_ref(v_a_676_);
    return v_res_679_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0(
    mut v_00_u03b2_680_: *mut leanh::LeanObject,
    mut v_x_681_: *mut leanh::LeanObject,
    mut v_x_682_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_683_: u8 = 0;
    v___x_683_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___redArg(v_x_681_, v_x_682_);
    return v___x_683_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0___boxed(
    mut v_00_u03b2_684_: *mut leanh::LeanObject,
    mut v_x_685_: *mut leanh::LeanObject,
    mut v_x_686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_687_: u8 = 0;
    let mut v_r_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_687_ =
        l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0(
            v_00_u03b2_684_,
            v_x_685_,
            v_x_686_,
        );
    leanh::lean_dec(v_x_686_);
    leanh::lean_dec_ref(v_x_685_);
    v_r_688_ = leanh::lean_box((v_res_687_) as usize);
    return v_r_688_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1(
    mut v_00_u03b2_689_: *mut leanh::LeanObject,
    mut v_x_690_: *mut leanh::LeanObject,
    mut v_x_691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_692_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___redArg(v_x_690_, v_x_691_);
    return v___x_692_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1___boxed(
    mut v_00_u03b2_693_: *mut leanh::LeanObject,
    mut v_x_694_: *mut leanh::LeanObject,
    mut v_x_695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_696_ =
        l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1(
            v_00_u03b2_693_,
            v_x_694_,
            v_x_695_,
        );
    leanh::lean_dec(v_x_695_);
    return v_res_696_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0(
    mut v_00_u03b2_697_: *mut leanh::LeanObject,
    mut v_x_698_: *mut leanh::LeanObject,
    mut v_x_699_: usize,
    mut v_x_700_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_701_: u8 = 0;
    v___x_701_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___redArg(v_x_698_, v_x_699_, v_x_700_);
    return v___x_701_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0___boxed(
    mut v_00_u03b2_702_: *mut leanh::LeanObject,
    mut v_x_703_: *mut leanh::LeanObject,
    mut v_x_704_: *mut leanh::LeanObject,
    mut v_x_705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_833__boxed_706_: usize = 0;
    let mut v_res_707_: u8 = 0;
    let mut v_r_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_833__boxed_706_ = leanh::lean_unbox_usize(v_x_704_);
    leanh::lean_dec(v_x_704_);
    v_res_707_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0(v_00_u03b2_702_, v_x_703_, v_x_833__boxed_706_, v_x_705_);
    leanh::lean_dec(v_x_705_);
    leanh::lean_dec_ref(v_x_703_);
    v_r_708_ = leanh::lean_box((v_res_707_) as usize);
    return v_r_708_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2(
    mut v_00_u03b2_709_: *mut leanh::LeanObject,
    mut v_x_710_: *mut leanh::LeanObject,
    mut v_x_711_: usize,
    mut v_x_712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_713_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___redArg(v_x_710_, v_x_711_, v_x_712_);
    return v___x_713_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2___boxed(
    mut v_00_u03b2_714_: *mut leanh::LeanObject,
    mut v_x_715_: *mut leanh::LeanObject,
    mut v_x_716_: *mut leanh::LeanObject,
    mut v_x_717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_844__boxed_718_: usize = 0;
    let mut v_res_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_844__boxed_718_ = leanh::lean_unbox_usize(v_x_716_);
    leanh::lean_dec(v_x_716_);
    v_res_719_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__1_spec__2(v_00_u03b2_714_, v_x_715_, v_x_844__boxed_718_, v_x_717_);
    leanh::lean_dec(v_x_717_);
    return v_res_719_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1(
    mut v_00_u03b2_720_: *mut leanh::LeanObject,
    mut v_keys_721_: *mut leanh::LeanObject,
    mut v_vals_722_: *mut leanh::LeanObject,
    mut v_heq_723_: *mut leanh::LeanObject,
    mut v_i_724_: *mut leanh::LeanObject,
    mut v_k_725_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_726_: u8 = 0;
    v___x_726_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___redArg(v_keys_721_, v_i_724_, v_k_725_);
    return v___x_726_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_727_: *mut leanh::LeanObject,
    mut v_keys_728_: *mut leanh::LeanObject,
    mut v_vals_729_: *mut leanh::LeanObject,
    mut v_heq_730_: *mut leanh::LeanObject,
    mut v_i_731_: *mut leanh::LeanObject,
    mut v_k_732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_733_: u8 = 0;
    let mut v_r_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_733_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_ExtTheorems_eraseDecl_spec__0_spec__0_spec__1(v_00_u03b2_727_, v_keys_728_, v_vals_729_, v_heq_730_, v_i_731_, v_k_732_);
    leanh::lean_dec(v_k_732_);
    leanh::lean_dec_ref(v_vals_729_);
    leanh::lean_dec_ref(v_keys_728_);
    v_r_734_ = leanh::lean_box((v_res_733_) as usize);
    return v_r_734_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_ExtAttr(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_ExtAttr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
}