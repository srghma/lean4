// Lean compiler output
// Module: Init.Data.Vector.Algebra
// Imports: Init.Grind Init.Data.Vector.Basic Init.Data.Vector.Lemmas
use crate::ffi::{lean_array_size, lean_mk_array};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_zipWithMAux___redArg,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Data::Vector::Lemmas::{
    initialize_Init_Data_Vector_Lemmas, runtime_initialize_Init_Data_Vector_Lemmas,
};
use crate::r#gen::Init::Grind::Module::Basic::l_Lean_Grind_IntModule_toNatModule___redArg;
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
pub static l_Vector_add___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_add___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_add___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Vector_add___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_add___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_add___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Vector_add___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_add___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_add___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Vector_add___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_add___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_add___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_Vector_add___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_add___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_add___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_Vector_add___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_add___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_add___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Vector_add___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_add___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_add___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_Vector_add___redArg___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_add___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_add___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_add___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_add___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l_Vector_add___redArg___closed__8_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_add___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_add___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_add___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_add___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_add___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_add___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_add___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l_Vector_add___redArg___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_add___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_add___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_add___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_add___redArg___closed__9_value) as *mut leanh::LeanObject;
pub static l_Vector_add___redArg___closed__10_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Vector_add___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_add___redArg___closed__10_value) as *mut leanh::LeanObject;
pub unsafe fn l_Vector_zero___redArg(
    mut v_n_291_: *mut leanh::LeanObject,
    mut v_inst_292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_293_ = lean_mk_array(v_n_291_, v_inst_292_);
    return v___x_293_;
}
pub unsafe fn l_Vector_zero(
    mut v_00_u03b1_294_: *mut leanh::LeanObject,
    mut v_n_295_: *mut leanh::LeanObject,
    mut v_inst_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_297_ = lean_mk_array(v_n_295_, v_inst_296_);
    return v___x_297_;
}
pub unsafe fn l_Vector_instZero___redArg(
    mut v_n_298_: *mut leanh::LeanObject,
    mut v_inst_299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_300_ = lean_mk_array(v_n_298_, v_inst_299_);
    return v___x_300_;
}
pub unsafe fn l_Vector_instZero(
    mut v_00_u03b1_301_: *mut leanh::LeanObject,
    mut v_n_302_: *mut leanh::LeanObject,
    mut v_inst_303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_304_ = lean_mk_array(v_n_302_, v_inst_303_);
    return v___x_304_;
}
pub unsafe fn l_Vector_add___redArg___lam__0(
    mut v_inst_305_: *mut leanh::LeanObject,
    mut v_x1_306_: *mut leanh::LeanObject,
    mut v_x2_307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_308_ = leanh::lean_apply_2(v_inst_305_, v_x1_306_, v_x2_307_);
    return v___x_308_;
}
pub unsafe fn l_Vector_add___redArg(
    mut v_inst_330_: *mut leanh::LeanObject,
    mut v_xs_331_: *mut leanh::LeanObject,
    mut v_ys_332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_333_ = leanh::lean_alloc_closure(
        l_Vector_add___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_333_, 0, v_inst_330_);
    v___x_334_ = l_Vector_add___redArg___closed__9;
    v___x_335_ = leanh::lean_unsigned_to_nat(0);
    v___x_336_ = l_Vector_add___redArg___closed__10;
    v___x_337_ = l_Array_zipWithMAux___redArg(
        v___x_334_, v_xs_331_, v_ys_332_, v___f_333_, v___x_335_, v___x_336_,
    );
    return v___x_337_;
}
pub unsafe fn l_Vector_add(
    mut v_00_u03b1_338_: *mut leanh::LeanObject,
    mut v_n_339_: *mut leanh::LeanObject,
    mut v_inst_340_: *mut leanh::LeanObject,
    mut v_xs_341_: *mut leanh::LeanObject,
    mut v_ys_342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_343_ = l_Vector_add___redArg(v_inst_340_, v_xs_341_, v_ys_342_);
    return v___x_343_;
}
pub unsafe fn l_Vector_add___boxed(
    mut v_00_u03b1_344_: *mut leanh::LeanObject,
    mut v_n_345_: *mut leanh::LeanObject,
    mut v_inst_346_: *mut leanh::LeanObject,
    mut v_xs_347_: *mut leanh::LeanObject,
    mut v_ys_348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_349_ = l_Vector_add(v_00_u03b1_344_, v_n_345_, v_inst_346_, v_xs_347_, v_ys_348_);
    leanh::lean_dec(v_n_345_);
    return v_res_349_;
}
pub unsafe fn l_Vector_instAdd___redArg(
    mut v_n_350_: *mut leanh::LeanObject,
    mut v_inst_351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_352_ =
        leanh::lean_alloc_closure(l_Vector_add___boxed as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_352_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_352_, 1, v_n_350_);
    leanh::lean_closure_set(v___x_352_, 2, v_inst_351_);
    return v___x_352_;
}
pub unsafe fn l_Vector_instAdd(
    mut v_00_u03b1_353_: *mut leanh::LeanObject,
    mut v_n_354_: *mut leanh::LeanObject,
    mut v_inst_355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ =
        leanh::lean_alloc_closure(l_Vector_add___boxed as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_356_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_356_, 1, v_n_354_);
    leanh::lean_closure_set(v___x_356_, 2, v_inst_355_);
    return v___x_356_;
}
pub unsafe fn l_Vector_neg___redArg___lam__0(
    mut v_inst_357_: *mut leanh::LeanObject,
    mut v_x_358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_359_ = leanh::lean_apply_1(v_inst_357_, v_x_358_);
    return v___x_359_;
}
pub unsafe fn l_Vector_neg___redArg(
    mut v_inst_360_: *mut leanh::LeanObject,
    mut v_xs_361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_364_: usize = 0;
    let mut v___x_365_: usize = 0;
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_362_ = leanh::lean_alloc_closure(
        l_Vector_neg___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_362_, 0, v_inst_360_);
    v___x_363_ = l_Vector_add___redArg___closed__9;
    v_sz_364_ = lean_array_size(v_xs_361_);
    v___x_365_ = 0usize;
    v___x_366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_363_,
        v___f_362_,
        v_sz_364_,
        v___x_365_,
        v_xs_361_,
    );
    return v___x_366_;
}
pub unsafe fn l_Vector_neg(
    mut v_00_u03b1_367_: *mut leanh::LeanObject,
    mut v_n_368_: *mut leanh::LeanObject,
    mut v_inst_369_: *mut leanh::LeanObject,
    mut v_xs_370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_371_ = l_Vector_neg___redArg(v_inst_369_, v_xs_370_);
    return v___x_371_;
}
pub unsafe fn l_Vector_neg___boxed(
    mut v_00_u03b1_372_: *mut leanh::LeanObject,
    mut v_n_373_: *mut leanh::LeanObject,
    mut v_inst_374_: *mut leanh::LeanObject,
    mut v_xs_375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_376_ = l_Vector_neg(v_00_u03b1_372_, v_n_373_, v_inst_374_, v_xs_375_);
    leanh::lean_dec(v_n_373_);
    return v_res_376_;
}
pub unsafe fn l_Vector_instNeg___redArg(
    mut v_n_377_: *mut leanh::LeanObject,
    mut v_inst_378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_379_ =
        leanh::lean_alloc_closure(l_Vector_neg___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_379_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_379_, 1, v_n_377_);
    leanh::lean_closure_set(v___x_379_, 2, v_inst_378_);
    return v___x_379_;
}
pub unsafe fn l_Vector_instNeg(
    mut v_00_u03b1_380_: *mut leanh::LeanObject,
    mut v_n_381_: *mut leanh::LeanObject,
    mut v_inst_382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_383_ =
        leanh::lean_alloc_closure(l_Vector_neg___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_383_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_383_, 1, v_n_381_);
    leanh::lean_closure_set(v___x_383_, 2, v_inst_382_);
    return v___x_383_;
}
pub unsafe fn l_Vector_sub___redArg(
    mut v_inst_384_: *mut leanh::LeanObject,
    mut v_xs_385_: *mut leanh::LeanObject,
    mut v_ys_386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_387_ = leanh::lean_alloc_closure(
        l_Vector_add___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_387_, 0, v_inst_384_);
    v___x_388_ = l_Vector_add___redArg___closed__9;
    v___x_389_ = leanh::lean_unsigned_to_nat(0);
    v___x_390_ = l_Vector_add___redArg___closed__10;
    v___x_391_ = l_Array_zipWithMAux___redArg(
        v___x_388_, v_xs_385_, v_ys_386_, v___f_387_, v___x_389_, v___x_390_,
    );
    return v___x_391_;
}
pub unsafe fn l_Vector_sub(
    mut v_00_u03b1_392_: *mut leanh::LeanObject,
    mut v_n_393_: *mut leanh::LeanObject,
    mut v_inst_394_: *mut leanh::LeanObject,
    mut v_xs_395_: *mut leanh::LeanObject,
    mut v_ys_396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_397_ = l_Vector_sub___redArg(v_inst_394_, v_xs_395_, v_ys_396_);
    return v___x_397_;
}
pub unsafe fn l_Vector_sub___boxed(
    mut v_00_u03b1_398_: *mut leanh::LeanObject,
    mut v_n_399_: *mut leanh::LeanObject,
    mut v_inst_400_: *mut leanh::LeanObject,
    mut v_xs_401_: *mut leanh::LeanObject,
    mut v_ys_402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_403_ = l_Vector_sub(v_00_u03b1_398_, v_n_399_, v_inst_400_, v_xs_401_, v_ys_402_);
    leanh::lean_dec(v_n_399_);
    return v_res_403_;
}
pub unsafe fn l_Vector_instSub___redArg(
    mut v_n_404_: *mut leanh::LeanObject,
    mut v_inst_405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_406_ =
        leanh::lean_alloc_closure(l_Vector_sub___boxed as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_406_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_406_, 1, v_n_404_);
    leanh::lean_closure_set(v___x_406_, 2, v_inst_405_);
    return v___x_406_;
}
pub unsafe fn l_Vector_instSub(
    mut v_00_u03b1_407_: *mut leanh::LeanObject,
    mut v_n_408_: *mut leanh::LeanObject,
    mut v_inst_409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_410_ =
        leanh::lean_alloc_closure(l_Vector_sub___boxed as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_410_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_410_, 1, v_n_408_);
    leanh::lean_closure_set(v___x_410_, 2, v_inst_409_);
    return v___x_410_;
}
pub unsafe fn l_Vector_mul___redArg(
    mut v_inst_411_: *mut leanh::LeanObject,
    mut v_xs_412_: *mut leanh::LeanObject,
    mut v_ys_413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_414_ = leanh::lean_alloc_closure(
        l_Vector_add___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_414_, 0, v_inst_411_);
    v___x_415_ = l_Vector_add___redArg___closed__9;
    v___x_416_ = leanh::lean_unsigned_to_nat(0);
    v___x_417_ = l_Vector_add___redArg___closed__10;
    v___x_418_ = l_Array_zipWithMAux___redArg(
        v___x_415_, v_xs_412_, v_ys_413_, v___f_414_, v___x_416_, v___x_417_,
    );
    return v___x_418_;
}
pub unsafe fn l_Vector_mul(
    mut v_00_u03b1_419_: *mut leanh::LeanObject,
    mut v_n_420_: *mut leanh::LeanObject,
    mut v_inst_421_: *mut leanh::LeanObject,
    mut v_xs_422_: *mut leanh::LeanObject,
    mut v_ys_423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_424_ = l_Vector_mul___redArg(v_inst_421_, v_xs_422_, v_ys_423_);
    return v___x_424_;
}
pub unsafe fn l_Vector_mul___boxed(
    mut v_00_u03b1_425_: *mut leanh::LeanObject,
    mut v_n_426_: *mut leanh::LeanObject,
    mut v_inst_427_: *mut leanh::LeanObject,
    mut v_xs_428_: *mut leanh::LeanObject,
    mut v_ys_429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_430_ = l_Vector_mul(v_00_u03b1_425_, v_n_426_, v_inst_427_, v_xs_428_, v_ys_429_);
    leanh::lean_dec(v_n_426_);
    return v_res_430_;
}
pub unsafe fn l_Vector_instMul___redArg(
    mut v_n_431_: *mut leanh::LeanObject,
    mut v_inst_432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_433_ =
        leanh::lean_alloc_closure(l_Vector_mul___boxed as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_433_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_433_, 1, v_n_431_);
    leanh::lean_closure_set(v___x_433_, 2, v_inst_432_);
    return v___x_433_;
}
pub unsafe fn l_Vector_instMul(
    mut v_00_u03b1_434_: *mut leanh::LeanObject,
    mut v_n_435_: *mut leanh::LeanObject,
    mut v_inst_436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_437_ =
        leanh::lean_alloc_closure(l_Vector_mul___boxed as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_437_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_437_, 1, v_n_435_);
    leanh::lean_closure_set(v___x_437_, 2, v_inst_436_);
    return v___x_437_;
}
pub unsafe fn l_Vector_hmul___redArg___lam__0(
    mut v_inst_438_: *mut leanh::LeanObject,
    mut v_c_439_: *mut leanh::LeanObject,
    mut v_x_440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_441_ = leanh::lean_apply_2(v_inst_438_, v_c_439_, v_x_440_);
    return v___x_441_;
}
pub unsafe fn l_Vector_hmul___redArg(
    mut v_inst_442_: *mut leanh::LeanObject,
    mut v_c_443_: *mut leanh::LeanObject,
    mut v_xs_444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_447_: usize = 0;
    let mut v___x_448_: usize = 0;
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_445_ = leanh::lean_alloc_closure(
        l_Vector_hmul___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_445_, 0, v_inst_442_);
    leanh::lean_closure_set(v___f_445_, 1, v_c_443_);
    v___x_446_ = l_Vector_add___redArg___closed__9;
    v_sz_447_ = lean_array_size(v_xs_444_);
    v___x_448_ = 0usize;
    v___x_449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_446_,
        v___f_445_,
        v_sz_447_,
        v___x_448_,
        v_xs_444_,
    );
    return v___x_449_;
}
pub unsafe fn l_Vector_hmul(
    mut v_00_u03b1_450_: *mut leanh::LeanObject,
    mut v_00_u03b2_451_: *mut leanh::LeanObject,
    mut v_00_u03b3_452_: *mut leanh::LeanObject,
    mut v_n_453_: *mut leanh::LeanObject,
    mut v_inst_454_: *mut leanh::LeanObject,
    mut v_c_455_: *mut leanh::LeanObject,
    mut v_xs_456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_457_ = l_Vector_hmul___redArg(v_inst_454_, v_c_455_, v_xs_456_);
    return v___x_457_;
}
pub unsafe fn l_Vector_hmul___boxed(
    mut v_00_u03b1_458_: *mut leanh::LeanObject,
    mut v_00_u03b2_459_: *mut leanh::LeanObject,
    mut v_00_u03b3_460_: *mut leanh::LeanObject,
    mut v_n_461_: *mut leanh::LeanObject,
    mut v_inst_462_: *mut leanh::LeanObject,
    mut v_c_463_: *mut leanh::LeanObject,
    mut v_xs_464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_465_ = l_Vector_hmul(
        v_00_u03b1_458_,
        v_00_u03b2_459_,
        v_00_u03b3_460_,
        v_n_461_,
        v_inst_462_,
        v_c_463_,
        v_xs_464_,
    );
    leanh::lean_dec(v_n_461_);
    return v_res_465_;
}
pub unsafe fn l_Vector_instHMul___redArg(
    mut v_n_466_: *mut leanh::LeanObject,
    mut v_inst_467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_468_ =
        leanh::lean_alloc_closure(l_Vector_hmul___boxed as *mut core::ffi::c_void, 7, 5);
    leanh::lean_closure_set(v___x_468_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_468_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_468_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_468_, 3, v_n_466_);
    leanh::lean_closure_set(v___x_468_, 4, v_inst_467_);
    return v___x_468_;
}
pub unsafe fn l_Vector_instHMul(
    mut v_00_u03b1_469_: *mut leanh::LeanObject,
    mut v_00_u03b2_470_: *mut leanh::LeanObject,
    mut v_00_u03b3_471_: *mut leanh::LeanObject,
    mut v_n_472_: *mut leanh::LeanObject,
    mut v_inst_473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_474_ =
        leanh::lean_alloc_closure(l_Vector_hmul___boxed as *mut core::ffi::c_void, 7, 5);
    leanh::lean_closure_set(v___x_474_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_474_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_474_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_474_, 3, v_n_472_);
    leanh::lean_closure_set(v___x_474_, 4, v_inst_473_);
    return v___x_474_;
}
pub unsafe fn l_Vector_smul___redArg(
    mut v_inst_475_: *mut leanh::LeanObject,
    mut v_c_476_: *mut leanh::LeanObject,
    mut v_xs_477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_480_: usize = 0;
    let mut v___x_481_: usize = 0;
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_478_ = leanh::lean_alloc_closure(
        l_Vector_hmul___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_478_, 0, v_inst_475_);
    leanh::lean_closure_set(v___f_478_, 1, v_c_476_);
    v___x_479_ = l_Vector_add___redArg___closed__9;
    v_sz_480_ = lean_array_size(v_xs_477_);
    v___x_481_ = 0usize;
    v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_479_,
        v___f_478_,
        v_sz_480_,
        v___x_481_,
        v_xs_477_,
    );
    return v___x_482_;
}
pub unsafe fn l_Vector_smul(
    mut v_00_u03b1_483_: *mut leanh::LeanObject,
    mut v_00_u03b2_484_: *mut leanh::LeanObject,
    mut v_n_485_: *mut leanh::LeanObject,
    mut v_inst_486_: *mut leanh::LeanObject,
    mut v_c_487_: *mut leanh::LeanObject,
    mut v_xs_488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_489_ = l_Vector_smul___redArg(v_inst_486_, v_c_487_, v_xs_488_);
    return v___x_489_;
}
pub unsafe fn l_Vector_smul___boxed(
    mut v_00_u03b1_490_: *mut leanh::LeanObject,
    mut v_00_u03b2_491_: *mut leanh::LeanObject,
    mut v_n_492_: *mut leanh::LeanObject,
    mut v_inst_493_: *mut leanh::LeanObject,
    mut v_c_494_: *mut leanh::LeanObject,
    mut v_xs_495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_496_ = l_Vector_smul(
        v_00_u03b1_490_,
        v_00_u03b2_491_,
        v_n_492_,
        v_inst_493_,
        v_c_494_,
        v_xs_495_,
    );
    leanh::lean_dec(v_n_492_);
    return v_res_496_;
}
pub unsafe fn l_Vector_instSMul___redArg(
    mut v_n_497_: *mut leanh::LeanObject,
    mut v_inst_498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_499_ =
        leanh::lean_alloc_closure(l_Vector_smul___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_499_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_499_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_499_, 2, v_n_497_);
    leanh::lean_closure_set(v___x_499_, 3, v_inst_498_);
    return v___x_499_;
}
pub unsafe fn l_Vector_instSMul(
    mut v_00_u03b1_500_: *mut leanh::LeanObject,
    mut v_00_u03b2_501_: *mut leanh::LeanObject,
    mut v_n_502_: *mut leanh::LeanObject,
    mut v_inst_503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_504_ =
        leanh::lean_alloc_closure(l_Vector_smul___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_504_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_504_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_504_, 2, v_n_502_);
    leanh::lean_closure_set(v___x_504_, 3, v_inst_503_);
    return v___x_504_;
}
pub unsafe fn l_Vector_instAddCommMonoid___redArg(
    mut v_n_505_: *mut leanh::LeanObject,
    mut v_inst_506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toZero_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAdd_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_511_: u8 = 0;
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toZero_507_ = leanh::lean_ctor_get(v_inst_506_, 0);
                v_toAdd_508_ = leanh::lean_ctor_get(v_inst_506_, 1);
                v_isSharedCheck_517_ = (!leanh::lean_is_exclusive(v_inst_506_)) as u8;
                if v_isSharedCheck_517_ == 0 {
                    v___x_510_ = v_inst_506_;
                    v_isShared_511_ = v_isSharedCheck_517_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toAdd_508_);
                    leanh::lean_inc(v_toZero_507_);
                    leanh::lean_dec(v_inst_506_);
                    v___x_510_ = leanh::lean_box(0);
                    v_isShared_511_ = v_isSharedCheck_517_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_n_505_);
                v___x_512_ = lean_mk_array(v_n_505_, v_toZero_507_);
                v___x_513_ = leanh::lean_alloc_closure(
                    l_Vector_add___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                leanh::lean_closure_set(v___x_513_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_513_, 1, v_n_505_);
                leanh::lean_closure_set(v___x_513_, 2, v_toAdd_508_);
                if v_isShared_511_ == 0 {
                    leanh::lean_ctor_set(v___x_510_, 1, v___x_513_);
                    leanh::lean_ctor_set(v___x_510_, 0, v___x_512_);
                    v___x_515_ = v___x_510_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_516_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_512_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_516_, 1, v___x_513_);
                    v___x_515_ = v_reuseFailAlloc_516_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Vector_instAddCommMonoid(
    mut v_00_u03b1_518_: *mut leanh::LeanObject,
    mut v_n_519_: *mut leanh::LeanObject,
    mut v_inst_520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_521_ = l_Vector_instAddCommMonoid___redArg(v_n_519_, v_inst_520_);
    return v___x_521_;
}
pub unsafe fn l_Vector_instAddCommGroup___redArg(
    mut v_n_522_: *mut leanh::LeanObject,
    mut v_inst_523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toAddCommMonoid_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toNeg_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSub_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_529_: u8 = 0;
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_536_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAddCommMonoid_524_ = leanh::lean_ctor_get(v_inst_523_, 0);
                v_toNeg_525_ = leanh::lean_ctor_get(v_inst_523_, 1);
                v_toSub_526_ = leanh::lean_ctor_get(v_inst_523_, 2);
                v_isSharedCheck_536_ = (!leanh::lean_is_exclusive(v_inst_523_)) as u8;
                if v_isSharedCheck_536_ == 0 {
                    v___x_528_ = v_inst_523_;
                    v_isShared_529_ = v_isSharedCheck_536_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toSub_526_);
                    leanh::lean_inc(v_toNeg_525_);
                    leanh::lean_inc(v_toAddCommMonoid_524_);
                    leanh::lean_dec(v_inst_523_);
                    v___x_528_ = leanh::lean_box(0);
                    v_isShared_529_ = v_isSharedCheck_536_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_n(v_n_522_, 2);
                v___x_530_ = l_Vector_instAddCommMonoid___redArg(v_n_522_, v_toAddCommMonoid_524_);
                v___x_531_ = leanh::lean_alloc_closure(
                    l_Vector_neg___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___x_531_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_531_, 1, v_n_522_);
                leanh::lean_closure_set(v___x_531_, 2, v_toNeg_525_);
                v___x_532_ = leanh::lean_alloc_closure(
                    l_Vector_sub___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                leanh::lean_closure_set(v___x_532_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_532_, 1, v_n_522_);
                leanh::lean_closure_set(v___x_532_, 2, v_toSub_526_);
                if v_isShared_529_ == 0 {
                    leanh::lean_ctor_set(v___x_528_, 2, v___x_532_);
                    leanh::lean_ctor_set(v___x_528_, 1, v___x_531_);
                    leanh::lean_ctor_set(v___x_528_, 0, v___x_530_);
                    v___x_534_ = v___x_528_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_535_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_530_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_535_, 2, v___x_532_);
                    v___x_534_ = v_reuseFailAlloc_535_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_534_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Vector_instAddCommGroup(
    mut v_00_u03b1_537_: *mut leanh::LeanObject,
    mut v_n_538_: *mut leanh::LeanObject,
    mut v_inst_539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_540_ = l_Vector_instAddCommGroup___redArg(v_n_538_, v_inst_539_);
    return v___x_540_;
}
pub unsafe fn l_Vector_instNatModule___redArg(
    mut v_n_541_: *mut leanh::LeanObject,
    mut v_inst_542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toAddCommMonoid_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nsmul_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_547_: u8 = 0;
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_553_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAddCommMonoid_543_ = leanh::lean_ctor_get(v_inst_542_, 0);
                v_nsmul_544_ = leanh::lean_ctor_get(v_inst_542_, 1);
                v_isSharedCheck_553_ = (!leanh::lean_is_exclusive(v_inst_542_)) as u8;
                if v_isSharedCheck_553_ == 0 {
                    v___x_546_ = v_inst_542_;
                    v_isShared_547_ = v_isSharedCheck_553_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nsmul_544_);
                    leanh::lean_inc(v_toAddCommMonoid_543_);
                    leanh::lean_dec(v_inst_542_);
                    v___x_546_ = leanh::lean_box(0);
                    v_isShared_547_ = v_isSharedCheck_553_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_n_541_);
                v___x_548_ = l_Vector_instAddCommMonoid___redArg(v_n_541_, v_toAddCommMonoid_543_);
                v___x_549_ = leanh::lean_alloc_closure(
                    l_Vector_smul___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                leanh::lean_closure_set(v___x_549_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_549_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_549_, 2, v_n_541_);
                leanh::lean_closure_set(v___x_549_, 3, v_nsmul_544_);
                if v_isShared_547_ == 0 {
                    leanh::lean_ctor_set(v___x_546_, 1, v___x_549_);
                    leanh::lean_ctor_set(v___x_546_, 0, v___x_548_);
                    v___x_551_ = v___x_546_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_552_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_548_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_549_);
                    v___x_551_ = v_reuseFailAlloc_552_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_551_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Vector_instNatModule(
    mut v_00_u03b1_554_: *mut leanh::LeanObject,
    mut v_n_555_: *mut leanh::LeanObject,
    mut v_inst_556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_557_ = l_Vector_instNatModule___redArg(v_n_555_, v_inst_556_);
    return v___x_557_;
}
pub unsafe fn l_Vector_instIntModule___redArg(
    mut v_n_558_: *mut leanh::LeanObject,
    mut v_inst_559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toAddCommGroup_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zsmul_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_566_: u8 = 0;
    let mut v_nsmul_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_573_: u8 = 0;
    let mut v_unused_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAddCommGroup_560_ = leanh::lean_ctor_get(v_inst_559_, 0);
                v_zsmul_561_ = leanh::lean_ctor_get(v_inst_559_, 2);
                leanh::lean_inc(v_zsmul_561_);
                leanh::lean_inc_ref(v_toAddCommGroup_560_);
                leanh::lean_inc(v_n_558_);
                v___x_562_ = l_Vector_instAddCommGroup___redArg(v_n_558_, v_toAddCommGroup_560_);
                v___x_563_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_559_);
                v_isSharedCheck_573_ = (!leanh::lean_is_exclusive(v_inst_559_)) as u8;
                if v_isSharedCheck_573_ == 0 {
                    v_unused_574_ = leanh::lean_ctor_get(v_inst_559_, 2);
                    leanh::lean_dec(v_unused_574_);
                    v_unused_575_ = leanh::lean_ctor_get(v_inst_559_, 1);
                    leanh::lean_dec(v_unused_575_);
                    v_unused_576_ = leanh::lean_ctor_get(v_inst_559_, 0);
                    leanh::lean_dec(v_unused_576_);
                    v___x_565_ = v_inst_559_;
                    v_isShared_566_ = v_isSharedCheck_573_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_inst_559_);
                    v___x_565_ = leanh::lean_box(0);
                    v_isShared_566_ = v_isSharedCheck_573_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_nsmul_567_ = leanh::lean_ctor_get(v___x_563_, 1);
                leanh::lean_inc(v_nsmul_567_);
                leanh::lean_dec_ref(v___x_563_);
                leanh::lean_inc(v_n_558_);
                v___x_568_ = leanh::lean_alloc_closure(
                    l_Vector_smul___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                leanh::lean_closure_set(v___x_568_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_568_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_568_, 2, v_n_558_);
                leanh::lean_closure_set(v___x_568_, 3, v_nsmul_567_);
                v___x_569_ = leanh::lean_alloc_closure(
                    l_Vector_smul___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                leanh::lean_closure_set(v___x_569_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_569_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_569_, 2, v_n_558_);
                leanh::lean_closure_set(v___x_569_, 3, v_zsmul_561_);
                if v_isShared_566_ == 0 {
                    leanh::lean_ctor_set(v___x_565_, 2, v___x_569_);
                    leanh::lean_ctor_set(v___x_565_, 1, v___x_568_);
                    leanh::lean_ctor_set(v___x_565_, 0, v___x_562_);
                    v___x_571_ = v___x_565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_572_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_562_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_572_, 1, v___x_568_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_572_, 2, v___x_569_);
                    v___x_571_ = v_reuseFailAlloc_572_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Vector_instIntModule(
    mut v_00_u03b1_577_: *mut leanh::LeanObject,
    mut v_n_578_: *mut leanh::LeanObject,
    mut v_inst_579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_580_ = l_Vector_instIntModule___redArg(v_n_578_, v_inst_579_);
    return v___x_580_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_Algebra(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_Algebra(
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
pub unsafe fn initialize_Init_Data_Vector_Algebra(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Algebra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_Algebra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Vector_Algebra(builtin);
}