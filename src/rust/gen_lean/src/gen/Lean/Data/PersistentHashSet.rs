// Lean compiler output
// Module: Lean.Data.PersistentHashSet
// Imports: Lean.Data.PersistentHashMap
use crate::ffi::lean_uint64_to_usize;
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::List::Basic::l_List_mapTR_loop___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    initialize_Lean_Data_PersistentHashMap, l_Lean_PersistentHashMap_Node_isEmpty___redArg,
    l_Lean_PersistentHashMap_contains___redArg, l_Lean_PersistentHashMap_empty,
    l_Lean_PersistentHashMap_erase___redArg, l_Lean_PersistentHashMap_findEntry_x3f___redArg,
    l_Lean_PersistentHashMap_findKeyDAux___redArg, l_Lean_PersistentHashMap_foldlMAux___redArg,
    l_Lean_PersistentHashMap_forIn___redArg, l_Lean_PersistentHashMap_insert___redArg,
    l_Lean_PersistentHashMap_toList___redArg, runtime_initialize_Lean_Data_PersistentHashMap,
};
pub static l_Lean_PersistentHashSet_fold___redArg___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentHashSet_fold___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashSet_fold___redArg___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentHashSet_fold___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashSet_fold___redArg___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentHashSet_fold___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashSet_fold___redArg___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentHashSet_fold___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashSet_fold___redArg___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentHashSet_fold___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashSet_fold___redArg___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentHashSet_fold___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashSet_fold___redArg___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentHashSet_fold___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashSet_fold___redArg___closed__7_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_PersistentHashSet_fold___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashSet_fold___redArg___closed__8_value: crate::leanh::LeanCtorObject<
    5,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_PersistentHashSet_fold___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashSet_fold___redArg___closed__9_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_PersistentHashSet_fold___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashSet_fold___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashSet_toList___redArg___closed__0_value:
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
    m_fun: l_Lean_PersistentHashSet_toList___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentHashSet_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashSet_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_PersistentHashSet_empty___redArg(
    mut v_inst_338_: *mut crate::leanh::LeanObject,
    mut v_inst_339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_340_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_338_,
        v_inst_339_,
    );
    return v___x_340_;
}
pub unsafe fn l_Lean_PersistentHashSet_empty___redArg___boxed(
    mut v_inst_341_: *mut crate::leanh::LeanObject,
    mut v_inst_342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_343_ = l_Lean_PersistentHashSet_empty___redArg(v_inst_341_, v_inst_342_);
    crate::leanh::lean_dec_ref(v_inst_342_);
    crate::leanh::lean_dec_ref(v_inst_341_);
    return v_res_343_;
}
pub unsafe fn l_Lean_PersistentHashSet_empty(
    mut v_00_u03b1_344_: *mut crate::leanh::LeanObject,
    mut v_inst_345_: *mut crate::leanh::LeanObject,
    mut v_inst_346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_347_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_345_,
        v_inst_346_,
    );
    return v___x_347_;
}
pub unsafe fn l_Lean_PersistentHashSet_empty___boxed(
    mut v_00_u03b1_348_: *mut crate::leanh::LeanObject,
    mut v_inst_349_: *mut crate::leanh::LeanObject,
    mut v_inst_350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_351_ = l_Lean_PersistentHashSet_empty(v_00_u03b1_348_, v_inst_349_, v_inst_350_);
    crate::leanh::lean_dec_ref(v_inst_350_);
    crate::leanh::lean_dec_ref(v_inst_349_);
    return v_res_351_;
}
pub unsafe fn l_Lean_PersistentHashSet_instInhabited___redArg(
    mut v_inst_352_: *mut crate::leanh::LeanObject,
    mut v_inst_353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_354_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_352_,
        v_inst_353_,
    );
    return v___x_354_;
}
pub unsafe fn l_Lean_PersistentHashSet_instInhabited___redArg___boxed(
    mut v_inst_355_: *mut crate::leanh::LeanObject,
    mut v_inst_356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_357_ = l_Lean_PersistentHashSet_instInhabited___redArg(v_inst_355_, v_inst_356_);
    crate::leanh::lean_dec_ref(v_inst_356_);
    crate::leanh::lean_dec_ref(v_inst_355_);
    return v_res_357_;
}
pub unsafe fn l_Lean_PersistentHashSet_instInhabited(
    mut v_00_u03b1_358_: *mut crate::leanh::LeanObject,
    mut v_inst_359_: *mut crate::leanh::LeanObject,
    mut v_inst_360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_361_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_359_,
        v_inst_360_,
    );
    return v___x_361_;
}
pub unsafe fn l_Lean_PersistentHashSet_instInhabited___boxed(
    mut v_00_u03b1_362_: *mut crate::leanh::LeanObject,
    mut v_inst_363_: *mut crate::leanh::LeanObject,
    mut v_inst_364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_365_ = l_Lean_PersistentHashSet_instInhabited(v_00_u03b1_362_, v_inst_363_, v_inst_364_);
    crate::leanh::lean_dec_ref(v_inst_364_);
    crate::leanh::lean_dec_ref(v_inst_363_);
    return v_res_365_;
}
pub unsafe fn l_Lean_PersistentHashSet_instEmptyCollection___redArg(
    mut v_inst_366_: *mut crate::leanh::LeanObject,
    mut v_inst_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_368_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_366_,
        v_inst_367_,
    );
    return v___x_368_;
}
pub unsafe fn l_Lean_PersistentHashSet_instEmptyCollection___redArg___boxed(
    mut v_inst_369_: *mut crate::leanh::LeanObject,
    mut v_inst_370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_371_ = l_Lean_PersistentHashSet_instEmptyCollection___redArg(v_inst_369_, v_inst_370_);
    crate::leanh::lean_dec_ref(v_inst_370_);
    crate::leanh::lean_dec_ref(v_inst_369_);
    return v_res_371_;
}
pub unsafe fn l_Lean_PersistentHashSet_instEmptyCollection(
    mut v_00_u03b1_372_: *mut crate::leanh::LeanObject,
    mut v_inst_373_: *mut crate::leanh::LeanObject,
    mut v_inst_374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_375_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_373_,
        v_inst_374_,
    );
    return v___x_375_;
}
pub unsafe fn l_Lean_PersistentHashSet_instEmptyCollection___boxed(
    mut v_00_u03b1_376_: *mut crate::leanh::LeanObject,
    mut v_inst_377_: *mut crate::leanh::LeanObject,
    mut v_inst_378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_379_ =
        l_Lean_PersistentHashSet_instEmptyCollection(v_00_u03b1_376_, v_inst_377_, v_inst_378_);
    crate::leanh::lean_dec_ref(v_inst_378_);
    crate::leanh::lean_dec_ref(v_inst_377_);
    return v_res_379_;
}
pub unsafe fn l_Lean_PersistentHashSet_isEmpty___redArg(
    mut v_s_380_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_381_: u8 = 0;
    v___x_381_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_s_380_);
    return v___x_381_;
}
pub unsafe fn l_Lean_PersistentHashSet_isEmpty___redArg___boxed(
    mut v_s_382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_383_: u8 = 0;
    let mut v_r_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_383_ = l_Lean_PersistentHashSet_isEmpty___redArg(v_s_382_);
    crate::leanh::lean_dec_ref(v_s_382_);
    v_r_384_ = crate::leanh::lean_box((v_res_383_) as usize);
    return v_r_384_;
}
pub unsafe fn l_Lean_PersistentHashSet_isEmpty(
    mut v_00_u03b1_385_: *mut crate::leanh::LeanObject,
    mut v_x_386_: *mut crate::leanh::LeanObject,
    mut v_x_387_: *mut crate::leanh::LeanObject,
    mut v_s_388_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_389_: u8 = 0;
    v___x_389_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_s_388_);
    return v___x_389_;
}
pub unsafe fn l_Lean_PersistentHashSet_isEmpty___boxed(
    mut v_00_u03b1_390_: *mut crate::leanh::LeanObject,
    mut v_x_391_: *mut crate::leanh::LeanObject,
    mut v_x_392_: *mut crate::leanh::LeanObject,
    mut v_s_393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_394_: u8 = 0;
    let mut v_r_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_394_ = l_Lean_PersistentHashSet_isEmpty(v_00_u03b1_390_, v_x_391_, v_x_392_, v_s_393_);
    crate::leanh::lean_dec_ref(v_s_393_);
    crate::leanh::lean_dec_ref(v_x_392_);
    crate::leanh::lean_dec_ref(v_x_391_);
    v_r_395_ = crate::leanh::lean_box((v_res_394_) as usize);
    return v_r_395_;
}
pub unsafe fn l_Lean_PersistentHashSet_insert___redArg(
    mut v_x_396_: *mut crate::leanh::LeanObject,
    mut v_x_397_: *mut crate::leanh::LeanObject,
    mut v_s_398_: *mut crate::leanh::LeanObject,
    mut v_a_399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_400_ = crate::leanh::lean_box(0);
    v___x_401_ = l_Lean_PersistentHashMap_insert___redArg(
        v_x_396_, v_x_397_, v_s_398_, v_a_399_, v___x_400_,
    );
    return v___x_401_;
}
pub unsafe fn l_Lean_PersistentHashSet_insert(
    mut v_00_u03b1_402_: *mut crate::leanh::LeanObject,
    mut v_x_403_: *mut crate::leanh::LeanObject,
    mut v_x_404_: *mut crate::leanh::LeanObject,
    mut v_s_405_: *mut crate::leanh::LeanObject,
    mut v_a_406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = crate::leanh::lean_box(0);
    v___x_408_ = l_Lean_PersistentHashMap_insert___redArg(
        v_x_403_, v_x_404_, v_s_405_, v_a_406_, v___x_407_,
    );
    return v___x_408_;
}
pub unsafe fn l_Lean_PersistentHashSet_erase___redArg(
    mut v_x_409_: *mut crate::leanh::LeanObject,
    mut v_x_410_: *mut crate::leanh::LeanObject,
    mut v_s_411_: *mut crate::leanh::LeanObject,
    mut v_a_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_413_ = l_Lean_PersistentHashMap_erase___redArg(v_x_409_, v_x_410_, v_s_411_, v_a_412_);
    return v___x_413_;
}
pub unsafe fn l_Lean_PersistentHashSet_erase(
    mut v_00_u03b1_414_: *mut crate::leanh::LeanObject,
    mut v_x_415_: *mut crate::leanh::LeanObject,
    mut v_x_416_: *mut crate::leanh::LeanObject,
    mut v_s_417_: *mut crate::leanh::LeanObject,
    mut v_a_418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_419_ = l_Lean_PersistentHashMap_erase___redArg(v_x_415_, v_x_416_, v_s_417_, v_a_418_);
    return v___x_419_;
}
pub unsafe fn l_Lean_PersistentHashSet_find_x3f___redArg(
    mut v_x_420_: *mut crate::leanh::LeanObject,
    mut v_x_421_: *mut crate::leanh::LeanObject,
    mut v_s_422_: *mut crate::leanh::LeanObject,
    mut v_a_423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_429_: u8 = 0;
    let mut v_fst_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_424_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(
                    v_x_420_, v_x_421_, v_s_422_, v_a_423_,
                );
                if crate::leanh::lean_obj_tag(v___x_424_) == 0 {
                    v___x_425_ = crate::leanh::lean_box(0);
                    return v___x_425_;
                } else {
                    v_val_426_ = crate::leanh::lean_ctor_get(v___x_424_, 0);
                    v_isSharedCheck_434_ = (!crate::leanh::lean_is_exclusive(v___x_424_)) as u8;
                    if v_isSharedCheck_434_ == 0 {
                        v___x_428_ = v___x_424_;
                        v_isShared_429_ = v_isSharedCheck_434_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_426_);
                        crate::leanh::lean_dec(v___x_424_);
                        v___x_428_ = crate::leanh::lean_box(0);
                        v_isShared_429_ = v_isSharedCheck_434_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_430_ = crate::leanh::lean_ctor_get(v_val_426_, 0);
                crate::leanh::lean_inc(v_fst_430_);
                crate::leanh::lean_dec(v_val_426_);
                if v_isShared_429_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_428_, 0, v_fst_430_);
                    v___x_432_ = v___x_428_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_433_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_433_, 0, v_fst_430_);
                    v___x_432_ = v_reuseFailAlloc_433_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashSet_find_x3f___redArg___boxed(
    mut v_x_435_: *mut crate::leanh::LeanObject,
    mut v_x_436_: *mut crate::leanh::LeanObject,
    mut v_s_437_: *mut crate::leanh::LeanObject,
    mut v_a_438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_439_ = l_Lean_PersistentHashSet_find_x3f___redArg(v_x_435_, v_x_436_, v_s_437_, v_a_438_);
    crate::leanh::lean_dec_ref(v_s_437_);
    return v_res_439_;
}
pub unsafe fn l_Lean_PersistentHashSet_find_x3f(
    mut v_00_u03b1_440_: *mut crate::leanh::LeanObject,
    mut v_x_441_: *mut crate::leanh::LeanObject,
    mut v_x_442_: *mut crate::leanh::LeanObject,
    mut v_s_443_: *mut crate::leanh::LeanObject,
    mut v_a_444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_450_: u8 = 0;
    let mut v_fst_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_445_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(
                    v_x_441_, v_x_442_, v_s_443_, v_a_444_,
                );
                if crate::leanh::lean_obj_tag(v___x_445_) == 0 {
                    v___x_446_ = crate::leanh::lean_box(0);
                    return v___x_446_;
                } else {
                    v_val_447_ = crate::leanh::lean_ctor_get(v___x_445_, 0);
                    v_isSharedCheck_455_ = (!crate::leanh::lean_is_exclusive(v___x_445_)) as u8;
                    if v_isSharedCheck_455_ == 0 {
                        v___x_449_ = v___x_445_;
                        v_isShared_450_ = v_isSharedCheck_455_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_447_);
                        crate::leanh::lean_dec(v___x_445_);
                        v___x_449_ = crate::leanh::lean_box(0);
                        v_isShared_450_ = v_isSharedCheck_455_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_451_ = crate::leanh::lean_ctor_get(v_val_447_, 0);
                crate::leanh::lean_inc(v_fst_451_);
                crate::leanh::lean_dec(v_val_447_);
                if v_isShared_450_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_449_, 0, v_fst_451_);
                    v___x_453_ = v___x_449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_454_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_454_, 0, v_fst_451_);
                    v___x_453_ = v_reuseFailAlloc_454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashSet_find_x3f___boxed(
    mut v_00_u03b1_456_: *mut crate::leanh::LeanObject,
    mut v_x_457_: *mut crate::leanh::LeanObject,
    mut v_x_458_: *mut crate::leanh::LeanObject,
    mut v_s_459_: *mut crate::leanh::LeanObject,
    mut v_a_460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_461_ =
        l_Lean_PersistentHashSet_find_x3f(v_00_u03b1_456_, v_x_457_, v_x_458_, v_s_459_, v_a_460_);
    crate::leanh::lean_dec_ref(v_s_459_);
    return v_res_461_;
}
pub unsafe fn l_Lean_PersistentHashSet_findD___redArg(
    mut v_x_462_: *mut crate::leanh::LeanObject,
    mut v_x_463_: *mut crate::leanh::LeanObject,
    mut v_s_464_: *mut crate::leanh::LeanObject,
    mut v_a_465_: *mut crate::leanh::LeanObject,
    mut v_a_u2080_466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: u64 = 0;
    let mut v___x_469_: usize = 0;
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_465_);
    v___x_467_ = crate::leanh::lean_apply_1(v_x_463_, v_a_465_);
    v___x_468_ = crate::leanh::lean_unbox_uint64(v___x_467_);
    crate::leanh::lean_dec_ref(v___x_467_);
    v___x_469_ = lean_uint64_to_usize(v___x_468_);
    v___x_470_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(
        v_x_462_,
        v_s_464_,
        v___x_469_,
        v_a_465_,
        v_a_u2080_466_,
    );
    return v___x_470_;
}
pub unsafe fn l_Lean_PersistentHashSet_findD___redArg___boxed(
    mut v_x_471_: *mut crate::leanh::LeanObject,
    mut v_x_472_: *mut crate::leanh::LeanObject,
    mut v_s_473_: *mut crate::leanh::LeanObject,
    mut v_a_474_: *mut crate::leanh::LeanObject,
    mut v_a_u2080_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_476_ = l_Lean_PersistentHashSet_findD___redArg(
        v_x_471_,
        v_x_472_,
        v_s_473_,
        v_a_474_,
        v_a_u2080_475_,
    );
    crate::leanh::lean_dec(v_a_u2080_475_);
    return v_res_476_;
}
pub unsafe fn l_Lean_PersistentHashSet_findD(
    mut v_00_u03b1_477_: *mut crate::leanh::LeanObject,
    mut v_x_478_: *mut crate::leanh::LeanObject,
    mut v_x_479_: *mut crate::leanh::LeanObject,
    mut v_s_480_: *mut crate::leanh::LeanObject,
    mut v_a_481_: *mut crate::leanh::LeanObject,
    mut v_a_u2080_482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: u64 = 0;
    let mut v___x_485_: usize = 0;
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_481_);
    v___x_483_ = crate::leanh::lean_apply_1(v_x_479_, v_a_481_);
    v___x_484_ = crate::leanh::lean_unbox_uint64(v___x_483_);
    crate::leanh::lean_dec_ref(v___x_483_);
    v___x_485_ = lean_uint64_to_usize(v___x_484_);
    v___x_486_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(
        v_x_478_,
        v_s_480_,
        v___x_485_,
        v_a_481_,
        v_a_u2080_482_,
    );
    return v___x_486_;
}
pub unsafe fn l_Lean_PersistentHashSet_findD___boxed(
    mut v_00_u03b1_487_: *mut crate::leanh::LeanObject,
    mut v_x_488_: *mut crate::leanh::LeanObject,
    mut v_x_489_: *mut crate::leanh::LeanObject,
    mut v_s_490_: *mut crate::leanh::LeanObject,
    mut v_a_491_: *mut crate::leanh::LeanObject,
    mut v_a_u2080_492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_493_ = l_Lean_PersistentHashSet_findD(
        v_00_u03b1_487_,
        v_x_488_,
        v_x_489_,
        v_s_490_,
        v_a_491_,
        v_a_u2080_492_,
    );
    crate::leanh::lean_dec(v_a_u2080_492_);
    return v_res_493_;
}
pub unsafe fn l_Lean_PersistentHashSet_contains___redArg(
    mut v_x_494_: *mut crate::leanh::LeanObject,
    mut v_x_495_: *mut crate::leanh::LeanObject,
    mut v_s_496_: *mut crate::leanh::LeanObject,
    mut v_a_497_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_498_: u8 = 0;
    v___x_498_ = l_Lean_PersistentHashMap_contains___redArg(v_x_494_, v_x_495_, v_s_496_, v_a_497_);
    return v___x_498_;
}
pub unsafe fn l_Lean_PersistentHashSet_contains___redArg___boxed(
    mut v_x_499_: *mut crate::leanh::LeanObject,
    mut v_x_500_: *mut crate::leanh::LeanObject,
    mut v_s_501_: *mut crate::leanh::LeanObject,
    mut v_a_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_503_: u8 = 0;
    let mut v_r_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_503_ = l_Lean_PersistentHashSet_contains___redArg(v_x_499_, v_x_500_, v_s_501_, v_a_502_);
    v_r_504_ = crate::leanh::lean_box((v_res_503_) as usize);
    return v_r_504_;
}
pub unsafe fn l_Lean_PersistentHashSet_contains(
    mut v_00_u03b1_505_: *mut crate::leanh::LeanObject,
    mut v_x_506_: *mut crate::leanh::LeanObject,
    mut v_x_507_: *mut crate::leanh::LeanObject,
    mut v_s_508_: *mut crate::leanh::LeanObject,
    mut v_a_509_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_510_: u8 = 0;
    v___x_510_ = l_Lean_PersistentHashMap_contains___redArg(v_x_506_, v_x_507_, v_s_508_, v_a_509_);
    return v___x_510_;
}
pub unsafe fn l_Lean_PersistentHashSet_contains___boxed(
    mut v_00_u03b1_511_: *mut crate::leanh::LeanObject,
    mut v_x_512_: *mut crate::leanh::LeanObject,
    mut v_x_513_: *mut crate::leanh::LeanObject,
    mut v_s_514_: *mut crate::leanh::LeanObject,
    mut v_a_515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_516_: u8 = 0;
    let mut v_r_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_516_ =
        l_Lean_PersistentHashSet_contains(v_00_u03b1_511_, v_x_512_, v_x_513_, v_s_514_, v_a_515_);
    v_r_517_ = crate::leanh::lean_box((v_res_516_) as usize);
    return v_r_517_;
}
pub unsafe fn l_Lean_PersistentHashSet_foldM___redArg___lam__0(
    mut v_f_518_: *mut crate::leanh::LeanObject,
    mut v_d_519_: *mut crate::leanh::LeanObject,
    mut v_a_520_: *mut crate::leanh::LeanObject,
    mut v_x_521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_522_ = crate::leanh::lean_apply_2(v_f_518_, v_d_519_, v_a_520_);
    return v___x_522_;
}
pub unsafe fn l_Lean_PersistentHashSet_foldM___redArg(
    mut v_inst_523_: *mut crate::leanh::LeanObject,
    mut v_f_524_: *mut crate::leanh::LeanObject,
    mut v_init_525_: *mut crate::leanh::LeanObject,
    mut v_s_526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_527_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashSet_foldM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_527_, 0, v_f_524_);
    v___x_528_ =
        l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_523_, v___f_527_, v_s_526_, v_init_525_);
    return v___x_528_;
}
pub unsafe fn l_Lean_PersistentHashSet_foldM(
    mut v_00_u03b1_529_: *mut crate::leanh::LeanObject,
    mut v_x_530_: *mut crate::leanh::LeanObject,
    mut v_x_531_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_532_: *mut crate::leanh::LeanObject,
    mut v_m_533_: *mut crate::leanh::LeanObject,
    mut v_inst_534_: *mut crate::leanh::LeanObject,
    mut v_f_535_: *mut crate::leanh::LeanObject,
    mut v_init_536_: *mut crate::leanh::LeanObject,
    mut v_s_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_538_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashSet_foldM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_538_, 0, v_f_535_);
    v___x_539_ =
        l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_534_, v___f_538_, v_s_537_, v_init_536_);
    return v___x_539_;
}
pub unsafe fn l_Lean_PersistentHashSet_foldM___boxed(
    mut v_00_u03b1_540_: *mut crate::leanh::LeanObject,
    mut v_x_541_: *mut crate::leanh::LeanObject,
    mut v_x_542_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_543_: *mut crate::leanh::LeanObject,
    mut v_m_544_: *mut crate::leanh::LeanObject,
    mut v_inst_545_: *mut crate::leanh::LeanObject,
    mut v_f_546_: *mut crate::leanh::LeanObject,
    mut v_init_547_: *mut crate::leanh::LeanObject,
    mut v_s_548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_549_ = l_Lean_PersistentHashSet_foldM(
        v_00_u03b1_540_,
        v_x_541_,
        v_x_542_,
        v_00_u03b2_543_,
        v_m_544_,
        v_inst_545_,
        v_f_546_,
        v_init_547_,
        v_s_548_,
    );
    crate::leanh::lean_dec_ref(v_x_542_);
    crate::leanh::lean_dec_ref(v_x_541_);
    return v_res_549_;
}
pub unsafe fn l_Lean_PersistentHashSet_fold___redArg(
    mut v_f_569_: *mut crate::leanh::LeanObject,
    mut v_init_570_: *mut crate::leanh::LeanObject,
    mut v_s_571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_572_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashSet_foldM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_572_, 0, v_f_569_);
    v___x_573_ = l_Lean_PersistentHashSet_fold___redArg___closed__9;
    v___x_574_ =
        l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_573_, v___f_572_, v_s_571_, v_init_570_);
    return v___x_574_;
}
pub unsafe fn l_Lean_PersistentHashSet_fold(
    mut v_00_u03b1_575_: *mut crate::leanh::LeanObject,
    mut v_x_576_: *mut crate::leanh::LeanObject,
    mut v_x_577_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_578_: *mut crate::leanh::LeanObject,
    mut v_f_579_: *mut crate::leanh::LeanObject,
    mut v_init_580_: *mut crate::leanh::LeanObject,
    mut v_s_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_582_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashSet_foldM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_582_, 0, v_f_579_);
    v___x_583_ = l_Lean_PersistentHashSet_fold___redArg___closed__9;
    v___x_584_ =
        l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_583_, v___f_582_, v_s_581_, v_init_580_);
    return v___x_584_;
}
pub unsafe fn l_Lean_PersistentHashSet_fold___boxed(
    mut v_00_u03b1_585_: *mut crate::leanh::LeanObject,
    mut v_x_586_: *mut crate::leanh::LeanObject,
    mut v_x_587_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_588_: *mut crate::leanh::LeanObject,
    mut v_f_589_: *mut crate::leanh::LeanObject,
    mut v_init_590_: *mut crate::leanh::LeanObject,
    mut v_s_591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_592_ = l_Lean_PersistentHashSet_fold(
        v_00_u03b1_585_,
        v_x_586_,
        v_x_587_,
        v_00_u03b2_588_,
        v_f_589_,
        v_init_590_,
        v_s_591_,
    );
    crate::leanh::lean_dec_ref(v_x_587_);
    crate::leanh::lean_dec_ref(v_x_586_);
    return v_res_592_;
}
pub unsafe fn l_Lean_PersistentHashSet_toList___redArg___lam__0(
    mut v_x_593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_594_ = crate::leanh::lean_ctor_get(v_x_593_, 0);
    crate::leanh::lean_inc(v_fst_594_);
    return v_fst_594_;
}
pub unsafe fn l_Lean_PersistentHashSet_toList___redArg___lam__0___boxed(
    mut v_x_595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_596_ = l_Lean_PersistentHashSet_toList___redArg___lam__0(v_x_595_);
    crate::leanh::lean_dec_ref(v_x_595_);
    return v_res_596_;
}
pub unsafe fn l_Lean_PersistentHashSet_toList___redArg(
    mut v_s_598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_599_ = l_Lean_PersistentHashSet_toList___redArg___closed__0;
    v___x_600_ = l_Lean_PersistentHashMap_toList___redArg(v_s_598_);
    v___x_601_ = crate::leanh::lean_box(0);
    v___x_602_ = l_List_mapTR_loop___redArg(v___f_599_, v___x_600_, v___x_601_);
    return v___x_602_;
}
pub unsafe fn l_Lean_PersistentHashSet_toList(
    mut v_00_u03b1_603_: *mut crate::leanh::LeanObject,
    mut v_x_604_: *mut crate::leanh::LeanObject,
    mut v_x_605_: *mut crate::leanh::LeanObject,
    mut v_s_606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_607_ = l_Lean_PersistentHashSet_toList___redArg(v_s_606_);
    return v___x_607_;
}
pub unsafe fn l_Lean_PersistentHashSet_toList___boxed(
    mut v_00_u03b1_608_: *mut crate::leanh::LeanObject,
    mut v_x_609_: *mut crate::leanh::LeanObject,
    mut v_x_610_: *mut crate::leanh::LeanObject,
    mut v_s_611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_612_ = l_Lean_PersistentHashSet_toList(v_00_u03b1_608_, v_x_609_, v_x_610_, v_s_611_);
    crate::leanh::lean_dec_ref(v_x_610_);
    crate::leanh::lean_dec_ref(v_x_609_);
    return v_res_612_;
}
pub unsafe fn l_Lean_PersistentHashSet_forIn___redArg___lam__0(
    mut v_f_613_: *mut crate::leanh::LeanObject,
    mut v_p_614_: *mut crate::leanh::LeanObject,
    mut v_s_615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_616_ = crate::leanh::lean_ctor_get(v_p_614_, 0);
    crate::leanh::lean_inc(v_fst_616_);
    crate::leanh::lean_dec_ref(v_p_614_);
    v___x_617_ = crate::leanh::lean_apply_2(v_f_613_, v_fst_616_, v_s_615_);
    return v___x_617_;
}
pub unsafe fn l_Lean_PersistentHashSet_forIn___redArg(
    mut v_inst_618_: *mut crate::leanh::LeanObject,
    mut v_s_619_: *mut crate::leanh::LeanObject,
    mut v_init_620_: *mut crate::leanh::LeanObject,
    mut v_f_621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_622_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_622_, 0, v_f_621_);
    v___x_623_ =
        l_Lean_PersistentHashMap_forIn___redArg(v_inst_618_, v_s_619_, v_init_620_, v___f_622_);
    return v___x_623_;
}
pub unsafe fn l_Lean_PersistentHashSet_forIn___redArg___boxed(
    mut v_inst_624_: *mut crate::leanh::LeanObject,
    mut v_s_625_: *mut crate::leanh::LeanObject,
    mut v_init_626_: *mut crate::leanh::LeanObject,
    mut v_f_627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_628_ =
        l_Lean_PersistentHashSet_forIn___redArg(v_inst_624_, v_s_625_, v_init_626_, v_f_627_);
    crate::leanh::lean_dec_ref(v_s_625_);
    return v_res_628_;
}
pub unsafe fn l_Lean_PersistentHashSet_forIn(
    mut v_00_u03b1_629_: *mut crate::leanh::LeanObject,
    mut v_m_630_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_631_: *mut crate::leanh::LeanObject,
    mut v_x_632_: *mut crate::leanh::LeanObject,
    mut v_x_633_: *mut crate::leanh::LeanObject,
    mut v_inst_634_: *mut crate::leanh::LeanObject,
    mut v_s_635_: *mut crate::leanh::LeanObject,
    mut v_init_636_: *mut crate::leanh::LeanObject,
    mut v_f_637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_638_ =
        l_Lean_PersistentHashSet_forIn___redArg(v_inst_634_, v_s_635_, v_init_636_, v_f_637_);
    return v___x_638_;
}
pub unsafe fn l_Lean_PersistentHashSet_forIn___boxed(
    mut v_00_u03b1_639_: *mut crate::leanh::LeanObject,
    mut v_m_640_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_641_: *mut crate::leanh::LeanObject,
    mut v_x_642_: *mut crate::leanh::LeanObject,
    mut v_x_643_: *mut crate::leanh::LeanObject,
    mut v_inst_644_: *mut crate::leanh::LeanObject,
    mut v_s_645_: *mut crate::leanh::LeanObject,
    mut v_init_646_: *mut crate::leanh::LeanObject,
    mut v_f_647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_648_ = l_Lean_PersistentHashSet_forIn(
        v_00_u03b1_639_,
        v_m_640_,
        v_00_u03c3_641_,
        v_x_642_,
        v_x_643_,
        v_inst_644_,
        v_s_645_,
        v_init_646_,
        v_f_647_,
    );
    crate::leanh::lean_dec_ref(v_s_645_);
    crate::leanh::lean_dec_ref(v_x_643_);
    crate::leanh::lean_dec_ref(v_x_642_);
    return v_res_648_;
}
pub unsafe fn l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0(
    mut v_inst_649_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_650_: *mut crate::leanh::LeanObject,
    mut v___y_651_: *mut crate::leanh::LeanObject,
    mut v___y_652_: *mut crate::leanh::LeanObject,
    mut v___y_653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_654_ =
        l_Lean_PersistentHashSet_forIn___redArg(v_inst_649_, v___y_651_, v___y_652_, v___y_653_);
    return v___x_654_;
}
pub unsafe fn l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0___boxed(
    mut v_inst_655_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_656_: *mut crate::leanh::LeanObject,
    mut v___y_657_: *mut crate::leanh::LeanObject,
    mut v___y_658_: *mut crate::leanh::LeanObject,
    mut v___y_659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_660_ = l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0(
        v_inst_655_,
        v_00_u03b2_656_,
        v___y_657_,
        v___y_658_,
        v___y_659_,
    );
    crate::leanh::lean_dec_ref(v___y_657_);
    return v_res_660_;
}
pub unsafe fn l_Lean_PersistentHashSet_instForInOfMonad___redArg(
    mut v_inst_661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_662_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_662_, 0, v_inst_661_);
    return v___f_662_;
}
pub unsafe fn l_Lean_PersistentHashSet_instForInOfMonad(
    mut v_00_u03b1_663_: *mut crate::leanh::LeanObject,
    mut v_m_664_: *mut crate::leanh::LeanObject,
    mut v_x_665_: *mut crate::leanh::LeanObject,
    mut v_x_666_: *mut crate::leanh::LeanObject,
    mut v_inst_667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_668_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_668_, 0, v_inst_667_);
    return v___f_668_;
}
pub unsafe fn l_Lean_PersistentHashSet_instForInOfMonad___boxed(
    mut v_00_u03b1_669_: *mut crate::leanh::LeanObject,
    mut v_m_670_: *mut crate::leanh::LeanObject,
    mut v_x_671_: *mut crate::leanh::LeanObject,
    mut v_x_672_: *mut crate::leanh::LeanObject,
    mut v_inst_673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_674_ = l_Lean_PersistentHashSet_instForInOfMonad(
        v_00_u03b1_669_,
        v_m_670_,
        v_x_671_,
        v_x_672_,
        v_inst_673_,
    );
    crate::leanh::lean_dec_ref(v_x_672_);
    crate::leanh::lean_dec_ref(v_x_671_);
    return v_res_674_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_PersistentHashSet(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_PersistentHashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_PersistentHashSet(
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
pub unsafe fn initialize_Lean_Data_PersistentHashSet(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_PersistentHashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentHashSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_PersistentHashSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_PersistentHashSet(builtin);
}
