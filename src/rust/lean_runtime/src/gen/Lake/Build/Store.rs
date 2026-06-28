// Lean compiler output
// Module: Lake.Build.Store
// Imports: Lake.Util.Store Lake.Build.Job.Basic
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Lake::Build::Job::Basic::{
    initialize_Lake_Build_Job_Basic, runtime_initialize_Lake_Build_Job_Basic,
};
use crate::r#gen::Lake::Util::Store::{
    initialize_Lake_Util_Store, runtime_initialize_Lake_Util_Store,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_forInStep___redArg;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
};
pub static mut l_Lake_BuildStore_empty: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__0_value:
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
static mut l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__1_value:
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
static mut l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__2_value:
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
static mut l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__3_value:
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
static mut l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__4_value:
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
static mut l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__5_value:
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
static mut l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__6_value:
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
static mut l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__10_value:
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
static mut l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [101, 120, 116, 101, 114, 110, 76, 105, 98, 0],
};
static mut l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 104, 97, 114, 101, 100, 0],
};
static mut l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3925673521345038251 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13440204898709017026 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lake_BuildStore_empty() -> *mut crate::leanh::LeanObject {
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_279_ = crate::leanh::lean_box(1);
    return v___x_279_;
}
pub unsafe fn l___private_Lake_Build_Store_0__Lake_BuildStore_getModuleFacetJob_x3f___redArg(
    mut v_facet_280_: *mut crate::leanh::LeanObject,
    mut v_k_281_: *mut crate::leanh::LeanObject,
    mut v_v_282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_target_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_287_: u8 = 0;
    let mut v_module_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_291_: u8 = 0;
    let mut v___x_292_: u8 = 0;
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_300_: u8 = 0;
    let mut v_isSharedCheck_301_: u8 = 0;
    let mut v_unused_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_307_: u8 = 0;
    let mut v___x_308_: u8 = 0;
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_314_: u8 = 0;
    let mut v_unused_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_k_281_) == 4 {
                    v_target_283_ = crate::leanh::lean_ctor_get(v_k_281_, 0);
                    crate::leanh::lean_inc_ref(v_target_283_);
                    match crate::leanh::lean_obj_tag(v_target_283_) {
                        0 => {
                            v_facet_284_ = crate::leanh::lean_ctor_get(v_k_281_, 1);
                            v_isSharedCheck_301_ =
                                (!crate::leanh::lean_is_exclusive(v_k_281_)) as u8;
                            if v_isSharedCheck_301_ == 0 {
                                v_unused_302_ = crate::leanh::lean_ctor_get(v_k_281_, 0);
                                crate::leanh::lean_dec(v_unused_302_);
                                v___x_286_ = v_k_281_;
                                v_isShared_287_ = v_isSharedCheck_301_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_facet_284_);
                                crate::leanh::lean_dec(v_k_281_);
                                v___x_286_ = crate::leanh::lean_box(0);
                                v_isShared_287_ = v_isSharedCheck_301_;
                                state = 1;
                                continue;
                            }
                        }
                        2 => {
                            v_facet_303_ = crate::leanh::lean_ctor_get(v_k_281_, 1);
                            crate::leanh::lean_inc(v_facet_303_);
                            crate::leanh::lean_dec_ref_known(v_k_281_, 2);
                            v_module_304_ = crate::leanh::lean_ctor_get(v_target_283_, 1);
                            v_isSharedCheck_314_ =
                                (!crate::leanh::lean_is_exclusive(v_target_283_)) as u8;
                            if v_isSharedCheck_314_ == 0 {
                                v_unused_315_ = crate::leanh::lean_ctor_get(v_target_283_, 0);
                                crate::leanh::lean_dec(v_unused_315_);
                                v___x_306_ = v_target_283_;
                                v_isShared_307_ = v_isSharedCheck_314_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_module_304_);
                                crate::leanh::lean_dec(v_target_283_);
                                v___x_306_ = crate::leanh::lean_box(0);
                                v_isShared_307_ = v_isSharedCheck_314_;
                                state = 5;
                                continue;
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec_ref_known(v_k_281_, 2);
                            crate::leanh::lean_dec_ref(v_target_283_);
                            crate::leanh::lean_dec_ref(v_v_282_);
                            v___x_316_ = crate::leanh::lean_box(0);
                            return v___x_316_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_v_282_);
                    crate::leanh::lean_dec_ref(v_k_281_);
                    v___x_317_ = crate::leanh::lean_box(0);
                    return v___x_317_;
                }
            }
            1 => {
                v_module_288_ = crate::leanh::lean_ctor_get(v_target_283_, 0);
                v_isSharedCheck_300_ = (!crate::leanh::lean_is_exclusive(v_target_283_)) as u8;
                if v_isSharedCheck_300_ == 0 {
                    v___x_290_ = v_target_283_;
                    v_isShared_291_ = v_isSharedCheck_300_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_module_288_);
                    crate::leanh::lean_dec(v_target_283_);
                    v___x_290_ = crate::leanh::lean_box(0);
                    v_isShared_291_ = v_isSharedCheck_300_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_292_ = lean_name_eq(v_facet_284_, v_facet_280_);
                crate::leanh::lean_dec(v_facet_284_);
                if v___x_292_ == 0 {
                    crate::leanh::lean_del_object(v___x_290_);
                    crate::leanh::lean_dec(v_module_288_);
                    crate::leanh::lean_del_object(v___x_286_);
                    crate::leanh::lean_dec_ref(v_v_282_);
                    v___x_293_ = crate::leanh::lean_box(0);
                    return v___x_293_;
                } else {
                    if v_isShared_287_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_286_, 0);
                        crate::leanh::lean_ctor_set(v___x_286_, 1, v_v_282_);
                        crate::leanh::lean_ctor_set(v___x_286_, 0, v_module_288_);
                        v___x_295_ = v___x_286_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_299_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_299_, 0, v_module_288_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_299_, 1, v_v_282_);
                        v___x_295_ = v_reuseFailAlloc_299_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_291_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_290_, 1);
                    crate::leanh::lean_ctor_set(v___x_290_, 0, v___x_295_);
                    v___x_297_ = v___x_290_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_298_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
                    v___x_297_ = v_reuseFailAlloc_298_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_297_;
            }
            5 => {
                v___x_308_ = lean_name_eq(v_facet_303_, v_facet_280_);
                crate::leanh::lean_dec(v_facet_303_);
                if v___x_308_ == 0 {
                    crate::leanh::lean_del_object(v___x_306_);
                    crate::leanh::lean_dec(v_module_304_);
                    crate::leanh::lean_dec_ref(v_v_282_);
                    v___x_309_ = crate::leanh::lean_box(0);
                    return v___x_309_;
                } else {
                    if v_isShared_307_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_306_, 0);
                        crate::leanh::lean_ctor_set(v___x_306_, 1, v_v_282_);
                        crate::leanh::lean_ctor_set(v___x_306_, 0, v_module_304_);
                        v___x_311_ = v___x_306_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_313_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_313_, 0, v_module_304_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_313_, 1, v_v_282_);
                        v___x_311_ = v_reuseFailAlloc_313_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_312_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_312_, 0, v___x_311_);
                return v___x_312_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Store_0__Lake_BuildStore_getModuleFacetJob_x3f___redArg___boxed(
    mut v_facet_318_: *mut crate::leanh::LeanObject,
    mut v_k_319_: *mut crate::leanh::LeanObject,
    mut v_v_320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_321_ = l___private_Lake_Build_Store_0__Lake_BuildStore_getModuleFacetJob_x3f___redArg(
        v_facet_318_,
        v_k_319_,
        v_v_320_,
    );
    crate::leanh::lean_dec(v_facet_318_);
    return v_res_321_;
}
pub unsafe fn l___private_Lake_Build_Store_0__Lake_BuildStore_getModuleFacetJob_x3f(
    mut v_00_u03b1_322_: *mut crate::leanh::LeanObject,
    mut v_facet_323_: *mut crate::leanh::LeanObject,
    mut v_inst_324_: *mut crate::leanh::LeanObject,
    mut v_k_325_: *mut crate::leanh::LeanObject,
    mut v_v_326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_327_ = l___private_Lake_Build_Store_0__Lake_BuildStore_getModuleFacetJob_x3f___redArg(
        v_facet_323_,
        v_k_325_,
        v_v_326_,
    );
    return v___x_327_;
}
pub unsafe fn l___private_Lake_Build_Store_0__Lake_BuildStore_getModuleFacetJob_x3f___boxed(
    mut v_00_u03b1_328_: *mut crate::leanh::LeanObject,
    mut v_facet_329_: *mut crate::leanh::LeanObject,
    mut v_inst_330_: *mut crate::leanh::LeanObject,
    mut v_k_331_: *mut crate::leanh::LeanObject,
    mut v_v_332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_333_ = l___private_Lake_Build_Store_0__Lake_BuildStore_getModuleFacetJob_x3f(
        v_00_u03b1_328_,
        v_facet_329_,
        v_inst_330_,
        v_k_331_,
        v_v_332_,
    );
    crate::leanh::lean_dec(v_facet_329_);
    return v_res_333_;
}
pub unsafe fn l_Lake_BuildStore_collectModuleFacetArray___redArg___lam__0(
    mut v_facet_334_: *mut crate::leanh::LeanObject,
    mut v_a_335_: *mut crate::leanh::LeanObject,
    mut v_b_336_: *mut crate::leanh::LeanObject,
    mut v_acc_337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_342_: u8 = 0;
    let mut v_snd_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_348_: u8 = 0;
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_338_ =
                    l___private_Lake_Build_Store_0__Lake_BuildStore_getModuleFacetJob_x3f___redArg(
                        v_facet_334_,
                        v_a_335_,
                        v_b_336_,
                    );
                if crate::leanh::lean_obj_tag(v___x_338_) == 1 {
                    v_val_339_ = crate::leanh::lean_ctor_get(v___x_338_, 0);
                    v_isSharedCheck_348_ = (!crate::leanh::lean_is_exclusive(v___x_338_)) as u8;
                    if v_isSharedCheck_348_ == 0 {
                        v___x_341_ = v___x_338_;
                        v_isShared_342_ = v_isSharedCheck_348_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_339_);
                        crate::leanh::lean_dec(v___x_338_);
                        v___x_341_ = crate::leanh::lean_box(0);
                        v_isShared_342_ = v_isSharedCheck_348_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_338_);
                    v___x_349_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_349_, 0, v_acc_337_);
                    return v___x_349_;
                }
            }
            1 => {
                v_snd_343_ = crate::leanh::lean_ctor_get(v_val_339_, 1);
                crate::leanh::lean_inc(v_snd_343_);
                crate::leanh::lean_dec(v_val_339_);
                v___x_344_ = lean_array_push(v_acc_337_, v_snd_343_);
                if v_isShared_342_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_341_, 0, v___x_344_);
                    v___x_346_ = v___x_341_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_347_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
                    v___x_346_ = v_reuseFailAlloc_347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildStore_collectModuleFacetArray___redArg___lam__0___boxed(
    mut v_facet_350_: *mut crate::leanh::LeanObject,
    mut v_a_351_: *mut crate::leanh::LeanObject,
    mut v_b_352_: *mut crate::leanh::LeanObject,
    mut v_acc_353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_354_ = l_Lake_BuildStore_collectModuleFacetArray___redArg___lam__0(
        v_facet_350_,
        v_a_351_,
        v_b_352_,
        v_acc_353_,
    );
    crate::leanh::lean_dec(v_facet_350_);
    return v_res_354_;
}
pub unsafe fn l_Lake_BuildStore_collectModuleFacetArray___redArg(
    mut v_self_376_: *mut crate::leanh::LeanObject,
    mut v_facet_377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_378_ = crate::leanh::lean_alloc_closure(
        l_Lake_BuildStore_collectModuleFacetArray___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_378_, 0, v_facet_377_);
    v___x_379_ = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9;
    v_res_380_ = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__10;
    v___x_381_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v___x_379_,
        v___f_378_,
        v_res_380_,
        v_self_376_,
    );
    v_a_382_ = crate::leanh::lean_ctor_get(v___x_381_, 0);
    crate::leanh::lean_inc(v_a_382_);
    crate::leanh::lean_dec(v___x_381_);
    return v_a_382_;
}
pub unsafe fn l_Lake_BuildStore_collectModuleFacetArray(
    mut v_00_u03b1_383_: *mut crate::leanh::LeanObject,
    mut v_self_384_: *mut crate::leanh::LeanObject,
    mut v_facet_385_: *mut crate::leanh::LeanObject,
    mut v_inst_386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_387_ = l_Lake_BuildStore_collectModuleFacetArray___redArg(v_self_384_, v_facet_385_);
    return v___x_387_;
}
pub unsafe fn l_Lake_BuildStore_collectModuleFacetMap___redArg___lam__0(
    mut v_facet_388_: *mut crate::leanh::LeanObject,
    mut v_a_389_: *mut crate::leanh::LeanObject,
    mut v_b_390_: *mut crate::leanh::LeanObject,
    mut v_acc_391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_396_: u8 = 0;
    let mut v_fst_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_403_: u8 = 0;
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_392_ =
                    l___private_Lake_Build_Store_0__Lake_BuildStore_getModuleFacetJob_x3f___redArg(
                        v_facet_388_,
                        v_a_389_,
                        v_b_390_,
                    );
                if crate::leanh::lean_obj_tag(v___x_392_) == 1 {
                    v_val_393_ = crate::leanh::lean_ctor_get(v___x_392_, 0);
                    v_isSharedCheck_403_ = (!crate::leanh::lean_is_exclusive(v___x_392_)) as u8;
                    if v_isSharedCheck_403_ == 0 {
                        v___x_395_ = v___x_392_;
                        v_isShared_396_ = v_isSharedCheck_403_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_393_);
                        crate::leanh::lean_dec(v___x_392_);
                        v___x_395_ = crate::leanh::lean_box(0);
                        v_isShared_396_ = v_isSharedCheck_403_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_392_);
                    v___x_404_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_404_, 0, v_acc_391_);
                    return v___x_404_;
                }
            }
            1 => {
                v_fst_397_ = crate::leanh::lean_ctor_get(v_val_393_, 0);
                crate::leanh::lean_inc(v_fst_397_);
                v_snd_398_ = crate::leanh::lean_ctor_get(v_val_393_, 1);
                crate::leanh::lean_inc(v_snd_398_);
                crate::leanh::lean_dec(v_val_393_);
                v___x_399_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_397_, v_snd_398_, v_acc_391_);
                if v_isShared_396_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_395_, 0, v___x_399_);
                    v___x_401_ = v___x_395_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_402_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
                    v___x_401_ = v_reuseFailAlloc_402_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildStore_collectModuleFacetMap___redArg___lam__0___boxed(
    mut v_facet_405_: *mut crate::leanh::LeanObject,
    mut v_a_406_: *mut crate::leanh::LeanObject,
    mut v_b_407_: *mut crate::leanh::LeanObject,
    mut v_acc_408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_409_ = l_Lake_BuildStore_collectModuleFacetMap___redArg___lam__0(
        v_facet_405_,
        v_a_406_,
        v_b_407_,
        v_acc_408_,
    );
    crate::leanh::lean_dec(v_facet_405_);
    return v_res_409_;
}
pub unsafe fn l_Lake_BuildStore_collectModuleFacetMap___redArg(
    mut v_self_410_: *mut crate::leanh::LeanObject,
    mut v_facet_411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_412_ = crate::leanh::lean_alloc_closure(
        l_Lake_BuildStore_collectModuleFacetMap___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_412_, 0, v_facet_411_);
    v___x_413_ = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9;
    v_res_414_ = crate::leanh::lean_box(1);
    v___x_415_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v___x_413_,
        v___f_412_,
        v_res_414_,
        v_self_410_,
    );
    v_a_416_ = crate::leanh::lean_ctor_get(v___x_415_, 0);
    crate::leanh::lean_inc(v_a_416_);
    crate::leanh::lean_dec(v___x_415_);
    return v_a_416_;
}
pub unsafe fn l_Lake_BuildStore_collectModuleFacetMap(
    mut v_00_u03b1_417_: *mut crate::leanh::LeanObject,
    mut v_self_418_: *mut crate::leanh::LeanObject,
    mut v_facet_419_: *mut crate::leanh::LeanObject,
    mut v_inst_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_421_ = l_Lake_BuildStore_collectModuleFacetMap___redArg(v_self_418_, v_facet_419_);
    return v___x_421_;
}
pub unsafe fn l___private_Lake_Build_Store_0__Lake_BuildStore_getPackageFacetJob_x3f___redArg(
    mut v_facet_422_: *mut crate::leanh::LeanObject,
    mut v_k_423_: *mut crate::leanh::LeanObject,
    mut v_v_424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_target_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_429_: u8 = 0;
    let mut v___x_430_: u8 = 0;
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_435_: u8 = 0;
    let mut v_unused_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_k_423_) == 4 {
                    v_target_425_ = crate::leanh::lean_ctor_get(v_k_423_, 0);
                    crate::leanh::lean_inc_ref(v_target_425_);
                    if crate::leanh::lean_obj_tag(v_target_425_) == 1 {
                        v_facet_426_ = crate::leanh::lean_ctor_get(v_k_423_, 1);
                        crate::leanh::lean_inc(v_facet_426_);
                        crate::leanh::lean_dec_ref_known(v_k_423_, 2);
                        v_isSharedCheck_435_ =
                            (!crate::leanh::lean_is_exclusive(v_target_425_)) as u8;
                        if v_isSharedCheck_435_ == 0 {
                            v_unused_436_ = crate::leanh::lean_ctor_get(v_target_425_, 0);
                            crate::leanh::lean_dec(v_unused_436_);
                            v___x_428_ = v_target_425_;
                            v_isShared_429_ = v_isSharedCheck_435_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_target_425_);
                            v___x_428_ = crate::leanh::lean_box(0);
                            v_isShared_429_ = v_isSharedCheck_435_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_target_425_);
                        crate::leanh::lean_dec_ref_known(v_k_423_, 2);
                        crate::leanh::lean_dec_ref(v_v_424_);
                        v___x_437_ = crate::leanh::lean_box(0);
                        return v___x_437_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_v_424_);
                    crate::leanh::lean_dec_ref(v_k_423_);
                    v___x_438_ = crate::leanh::lean_box(0);
                    return v___x_438_;
                }
            }
            1 => {
                v___x_430_ = lean_name_eq(v_facet_426_, v_facet_422_);
                crate::leanh::lean_dec(v_facet_426_);
                if v___x_430_ == 0 {
                    crate::leanh::lean_del_object(v___x_428_);
                    crate::leanh::lean_dec_ref(v_v_424_);
                    v___x_431_ = crate::leanh::lean_box(0);
                    return v___x_431_;
                } else {
                    if v_isShared_429_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_428_, 0, v_v_424_);
                        v___x_433_ = v___x_428_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_434_, 0, v_v_424_);
                        v___x_433_ = v_reuseFailAlloc_434_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Store_0__Lake_BuildStore_getPackageFacetJob_x3f___redArg___boxed(
    mut v_facet_439_: *mut crate::leanh::LeanObject,
    mut v_k_440_: *mut crate::leanh::LeanObject,
    mut v_v_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_442_ = l___private_Lake_Build_Store_0__Lake_BuildStore_getPackageFacetJob_x3f___redArg(
        v_facet_439_,
        v_k_440_,
        v_v_441_,
    );
    crate::leanh::lean_dec(v_facet_439_);
    return v_res_442_;
}
pub unsafe fn l___private_Lake_Build_Store_0__Lake_BuildStore_getPackageFacetJob_x3f(
    mut v_00_u03b1_443_: *mut crate::leanh::LeanObject,
    mut v_facet_444_: *mut crate::leanh::LeanObject,
    mut v_inst_445_: *mut crate::leanh::LeanObject,
    mut v_k_446_: *mut crate::leanh::LeanObject,
    mut v_v_447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_448_ = l___private_Lake_Build_Store_0__Lake_BuildStore_getPackageFacetJob_x3f___redArg(
        v_facet_444_,
        v_k_446_,
        v_v_447_,
    );
    return v___x_448_;
}
pub unsafe fn l___private_Lake_Build_Store_0__Lake_BuildStore_getPackageFacetJob_x3f___boxed(
    mut v_00_u03b1_449_: *mut crate::leanh::LeanObject,
    mut v_facet_450_: *mut crate::leanh::LeanObject,
    mut v_inst_451_: *mut crate::leanh::LeanObject,
    mut v_k_452_: *mut crate::leanh::LeanObject,
    mut v_v_453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_454_ = l___private_Lake_Build_Store_0__Lake_BuildStore_getPackageFacetJob_x3f(
        v_00_u03b1_449_,
        v_facet_450_,
        v_inst_451_,
        v_k_452_,
        v_v_453_,
    );
    crate::leanh::lean_dec(v_facet_450_);
    return v_res_454_;
}
pub unsafe fn l_Lake_BuildStore_collectPackageFacetArray___redArg___lam__0(
    mut v_facet_455_: *mut crate::leanh::LeanObject,
    mut v_a_456_: *mut crate::leanh::LeanObject,
    mut v_b_457_: *mut crate::leanh::LeanObject,
    mut v_acc_458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_463_: u8 = 0;
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_468_: u8 = 0;
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_459_ =
                    l___private_Lake_Build_Store_0__Lake_BuildStore_getPackageFacetJob_x3f___redArg(
                        v_facet_455_,
                        v_a_456_,
                        v_b_457_,
                    );
                if crate::leanh::lean_obj_tag(v___x_459_) == 1 {
                    v_val_460_ = crate::leanh::lean_ctor_get(v___x_459_, 0);
                    v_isSharedCheck_468_ = (!crate::leanh::lean_is_exclusive(v___x_459_)) as u8;
                    if v_isSharedCheck_468_ == 0 {
                        v___x_462_ = v___x_459_;
                        v_isShared_463_ = v_isSharedCheck_468_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_460_);
                        crate::leanh::lean_dec(v___x_459_);
                        v___x_462_ = crate::leanh::lean_box(0);
                        v_isShared_463_ = v_isSharedCheck_468_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_459_);
                    v___x_469_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_469_, 0, v_acc_458_);
                    return v___x_469_;
                }
            }
            1 => {
                v___x_464_ = lean_array_push(v_acc_458_, v_val_460_);
                if v_isShared_463_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_462_, 0, v___x_464_);
                    v___x_466_ = v___x_462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_467_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
                    v___x_466_ = v_reuseFailAlloc_467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildStore_collectPackageFacetArray___redArg___lam__0___boxed(
    mut v_facet_470_: *mut crate::leanh::LeanObject,
    mut v_a_471_: *mut crate::leanh::LeanObject,
    mut v_b_472_: *mut crate::leanh::LeanObject,
    mut v_acc_473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_474_ = l_Lake_BuildStore_collectPackageFacetArray___redArg___lam__0(
        v_facet_470_,
        v_a_471_,
        v_b_472_,
        v_acc_473_,
    );
    crate::leanh::lean_dec(v_facet_470_);
    return v_res_474_;
}
pub unsafe fn l_Lake_BuildStore_collectPackageFacetArray___redArg(
    mut v_self_475_: *mut crate::leanh::LeanObject,
    mut v_facet_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_477_ = crate::leanh::lean_alloc_closure(
        l_Lake_BuildStore_collectPackageFacetArray___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_477_, 0, v_facet_476_);
    v___x_478_ = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9;
    v_res_479_ = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__10;
    v___x_480_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v___x_478_,
        v___f_477_,
        v_res_479_,
        v_self_475_,
    );
    v_a_481_ = crate::leanh::lean_ctor_get(v___x_480_, 0);
    crate::leanh::lean_inc(v_a_481_);
    crate::leanh::lean_dec(v___x_480_);
    return v_a_481_;
}
pub unsafe fn l_Lake_BuildStore_collectPackageFacetArray(
    mut v_00_u03b1_482_: *mut crate::leanh::LeanObject,
    mut v_self_483_: *mut crate::leanh::LeanObject,
    mut v_facet_484_: *mut crate::leanh::LeanObject,
    mut v_inst_485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_486_ = l_Lake_BuildStore_collectPackageFacetArray___redArg(v_self_483_, v_facet_484_);
    return v___x_486_;
}
pub unsafe fn l___private_Lake_Build_Store_0__Lake_BuildStore_getTargetFacetJob_x3f___redArg(
    mut v_facet_487_: *mut crate::leanh::LeanObject,
    mut v_k_488_: *mut crate::leanh::LeanObject,
    mut v_v_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_k_488_) == 4 {
        let mut v_target_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_target_490_ = crate::leanh::lean_ctor_get(v_k_488_, 0);
        if crate::leanh::lean_obj_tag(v_target_490_) == 3 {
            let mut v_facet_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_492_: u8 = 0;
            v_facet_491_ = crate::leanh::lean_ctor_get(v_k_488_, 1);
            v___x_492_ = lean_name_eq(v_facet_491_, v_facet_487_);
            if v___x_492_ == 0 {
                let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_v_489_);
                v___x_493_ = crate::leanh::lean_box(0);
                return v___x_493_;
            } else {
                let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_494_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_494_, 0, v_v_489_);
                return v___x_494_;
            }
        } else {
            let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_v_489_);
            v___x_495_ = crate::leanh::lean_box(0);
            return v___x_495_;
        }
    } else {
        let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_v_489_);
        v___x_496_ = crate::leanh::lean_box(0);
        return v___x_496_;
    }
}
pub unsafe fn l___private_Lake_Build_Store_0__Lake_BuildStore_getTargetFacetJob_x3f___redArg___boxed(
    mut v_facet_497_: *mut crate::leanh::LeanObject,
    mut v_k_498_: *mut crate::leanh::LeanObject,
    mut v_v_499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_500_ = l___private_Lake_Build_Store_0__Lake_BuildStore_getTargetFacetJob_x3f___redArg(
        v_facet_497_,
        v_k_498_,
        v_v_499_,
    );
    crate::leanh::lean_dec_ref(v_k_498_);
    crate::leanh::lean_dec(v_facet_497_);
    return v_res_500_;
}
pub unsafe fn l___private_Lake_Build_Store_0__Lake_BuildStore_getTargetFacetJob_x3f(
    mut v_00_u03b1_501_: *mut crate::leanh::LeanObject,
    mut v_facet_502_: *mut crate::leanh::LeanObject,
    mut v_inst_503_: *mut crate::leanh::LeanObject,
    mut v_k_504_: *mut crate::leanh::LeanObject,
    mut v_v_505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_506_ = l___private_Lake_Build_Store_0__Lake_BuildStore_getTargetFacetJob_x3f___redArg(
        v_facet_502_,
        v_k_504_,
        v_v_505_,
    );
    return v___x_506_;
}
pub unsafe fn l___private_Lake_Build_Store_0__Lake_BuildStore_getTargetFacetJob_x3f___boxed(
    mut v_00_u03b1_507_: *mut crate::leanh::LeanObject,
    mut v_facet_508_: *mut crate::leanh::LeanObject,
    mut v_inst_509_: *mut crate::leanh::LeanObject,
    mut v_k_510_: *mut crate::leanh::LeanObject,
    mut v_v_511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_512_ = l___private_Lake_Build_Store_0__Lake_BuildStore_getTargetFacetJob_x3f(
        v_00_u03b1_507_,
        v_facet_508_,
        v_inst_509_,
        v_k_510_,
        v_v_511_,
    );
    crate::leanh::lean_dec_ref(v_k_510_);
    crate::leanh::lean_dec(v_facet_508_);
    return v_res_512_;
}
pub unsafe fn l_Lake_BuildStore_collectTargetFacetArray___redArg___lam__0(
    mut v_facet_513_: *mut crate::leanh::LeanObject,
    mut v_a_514_: *mut crate::leanh::LeanObject,
    mut v_b_515_: *mut crate::leanh::LeanObject,
    mut v_acc_516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_521_: u8 = 0;
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_526_: u8 = 0;
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_517_ =
                    l___private_Lake_Build_Store_0__Lake_BuildStore_getTargetFacetJob_x3f___redArg(
                        v_facet_513_,
                        v_a_514_,
                        v_b_515_,
                    );
                if crate::leanh::lean_obj_tag(v___x_517_) == 1 {
                    v_val_518_ = crate::leanh::lean_ctor_get(v___x_517_, 0);
                    v_isSharedCheck_526_ = (!crate::leanh::lean_is_exclusive(v___x_517_)) as u8;
                    if v_isSharedCheck_526_ == 0 {
                        v___x_520_ = v___x_517_;
                        v_isShared_521_ = v_isSharedCheck_526_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_518_);
                        crate::leanh::lean_dec(v___x_517_);
                        v___x_520_ = crate::leanh::lean_box(0);
                        v_isShared_521_ = v_isSharedCheck_526_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_517_);
                    v___x_527_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_527_, 0, v_acc_516_);
                    return v___x_527_;
                }
            }
            1 => {
                v___x_522_ = lean_array_push(v_acc_516_, v_val_518_);
                if v_isShared_521_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_520_, 0, v___x_522_);
                    v___x_524_ = v___x_520_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
                    v___x_524_ = v_reuseFailAlloc_525_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_524_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildStore_collectTargetFacetArray___redArg___lam__0___boxed(
    mut v_facet_528_: *mut crate::leanh::LeanObject,
    mut v_a_529_: *mut crate::leanh::LeanObject,
    mut v_b_530_: *mut crate::leanh::LeanObject,
    mut v_acc_531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_532_ = l_Lake_BuildStore_collectTargetFacetArray___redArg___lam__0(
        v_facet_528_,
        v_a_529_,
        v_b_530_,
        v_acc_531_,
    );
    crate::leanh::lean_dec_ref(v_a_529_);
    crate::leanh::lean_dec(v_facet_528_);
    return v_res_532_;
}
pub unsafe fn l_Lake_BuildStore_collectTargetFacetArray___redArg(
    mut v_self_533_: *mut crate::leanh::LeanObject,
    mut v_facet_534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_535_ = crate::leanh::lean_alloc_closure(
        l_Lake_BuildStore_collectTargetFacetArray___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_535_, 0, v_facet_534_);
    v___x_536_ = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9;
    v_res_537_ = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__10;
    v___x_538_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v___x_536_,
        v___f_535_,
        v_res_537_,
        v_self_533_,
    );
    v_a_539_ = crate::leanh::lean_ctor_get(v___x_538_, 0);
    crate::leanh::lean_inc(v_a_539_);
    crate::leanh::lean_dec(v___x_538_);
    return v_a_539_;
}
pub unsafe fn l_Lake_BuildStore_collectTargetFacetArray(
    mut v_00_u03b1_540_: *mut crate::leanh::LeanObject,
    mut v_self_541_: *mut crate::leanh::LeanObject,
    mut v_facet_542_: *mut crate::leanh::LeanObject,
    mut v_inst_543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ = l_Lake_BuildStore_collectTargetFacetArray___redArg(v_self_541_, v_facet_542_);
    return v___x_544_;
}
pub unsafe fn l_Lake_BuildStore_collectSharedExternLibs___redArg(
    mut v_self_550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__2;
    v___x_552_ = l_Lake_BuildStore_collectTargetFacetArray___redArg(v_self_550_, v___x_551_);
    return v___x_552_;
}
pub unsafe fn l_Lake_BuildStore_collectSharedExternLibs(
    mut v_00_u03b1_553_: *mut crate::leanh::LeanObject,
    mut v_self_554_: *mut crate::leanh::LeanObject,
    mut v_inst_555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = l_Lake_BuildStore_collectSharedExternLibs___redArg(v_self_554_);
    return v___x_556_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Store(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Store(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_BuildStore_empty = _init_l_Lake_BuildStore_empty();
    crate::leanh::lean_mark_persistent(l_Lake_BuildStore_empty);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Store(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Store(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Store(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Job_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Store(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Store(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Store(builtin);
}
