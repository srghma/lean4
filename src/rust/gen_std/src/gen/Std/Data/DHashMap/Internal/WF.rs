// Lean compiler output
// Module: Std.Data.DHashMap.Internal.WF
// Imports: Std.Data.Internal.List.Associative Std.Data.DHashMap.Raw Std.Data.DHashMap.Internal.Defs Std.Data.DHashMap.Internal.Model Std.Data.DHashMap.Internal.AssocList.Basic Std.Data.DHashMap.RawDef Init.Data.Array.Bootstrap Init.Data.List.Nat.TakeDrop Init.Data.List.TakeDrop
use crate::ffi::{
    lean_array_get_size, lean_mk_array, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::{
    initialize_Std_Data_DHashMap_Internal_AssocList_Basic,
    l_Std_DHashMap_Internal_AssocList_foldlM___redArg,
    runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    initialize_Std_Data_DHashMap_Internal_Defs, runtime_initialize_Std_Data_DHashMap_Internal_Defs,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Model::{
    initialize_Std_Data_DHashMap_Internal_Model,
    l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg,
    runtime_initialize_Std_Data_DHashMap_Internal_Model,
};
use crate::r#gen::Std::Data::DHashMap::Raw::{
    initialize_Std_Data_DHashMap_Raw, runtime_initialize_Std_Data_DHashMap_Raw,
};
use crate::r#gen::Std::Data::DHashMap::RawDef::{
    initialize_Std_Data_DHashMap_RawDef, runtime_initialize_Std_Data_DHashMap_RawDef,
};
use crate::r#gen::Std::Data::Internal::List::Associative::{
    initialize_Std_Data_Internal_List_Associative,
    runtime_initialize_Std_Data_Internal_List_Associative,
};
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__0_value:
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
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__1_value:
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
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__2_value:
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
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__3_value:
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
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__4_value:
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
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__5_value:
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
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__6_value:
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
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__7_value:
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
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__8_value:
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
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__7_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9_value:
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
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__6_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9_value
) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter___redArg(
    mut v_x_302_: *mut crate::leanh::LeanObject,
    mut v_x_303_: *mut crate::leanh::LeanObject,
    mut v_h__1_304_: *mut crate::leanh::LeanObject,
    mut v_h__2_305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_303_) == 0 {
        let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_305_);
        v___x_306_ = crate::leanh::lean_apply_1(v_h__1_304_, v_x_302_);
        return v___x_306_;
    } else {
        let mut v_key_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_304_);
        v_key_307_ = crate::leanh::lean_ctor_get(v_x_303_, 0);
        crate::leanh::lean_inc(v_key_307_);
        v_value_308_ = crate::leanh::lean_ctor_get(v_x_303_, 1);
        crate::leanh::lean_inc(v_value_308_);
        v_tail_309_ = crate::leanh::lean_ctor_get(v_x_303_, 2);
        crate::leanh::lean_inc(v_tail_309_);
        crate::leanh::lean_dec_ref_known(v_x_303_, 3);
        v___x_310_ = crate::leanh::lean_apply_4(
            v_h__2_305_,
            v_x_302_,
            v_key_307_,
            v_value_308_,
            v_tail_309_,
        );
        return v___x_310_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter(
    mut v_00_u03b1_311_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_312_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_313_: *mut crate::leanh::LeanObject,
    mut v_motive_314_: *mut crate::leanh::LeanObject,
    mut v_x_315_: *mut crate::leanh::LeanObject,
    mut v_x_316_: *mut crate::leanh::LeanObject,
    mut v_h__1_317_: *mut crate::leanh::LeanObject,
    mut v_h__2_318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_316_) == 0 {
        let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_318_);
        v___x_319_ = crate::leanh::lean_apply_1(v_h__1_317_, v_x_315_);
        return v___x_319_;
    } else {
        let mut v_key_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_317_);
        v_key_320_ = crate::leanh::lean_ctor_get(v_x_316_, 0);
        crate::leanh::lean_inc(v_key_320_);
        v_value_321_ = crate::leanh::lean_ctor_get(v_x_316_, 1);
        crate::leanh::lean_inc(v_value_321_);
        v_tail_322_ = crate::leanh::lean_ctor_get(v_x_316_, 2);
        crate::leanh::lean_inc(v_tail_322_);
        crate::leanh::lean_dec_ref_known(v_x_316_, 3);
        v___x_323_ = crate::leanh::lean_apply_4(
            v_h__2_318_,
            v_x_315_,
            v_key_320_,
            v_value_321_,
            v_tail_322_,
        );
        return v___x_323_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__3_splitter___redArg(
    mut v_x_324_: *mut crate::leanh::LeanObject,
    mut v_x_325_: *mut crate::leanh::LeanObject,
    mut v_h__1_326_: *mut crate::leanh::LeanObject,
    mut v_h__2_327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_324_) == 0 {
        let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_327_);
        v___x_328_ = crate::leanh::lean_apply_1(v_h__1_326_, v_x_325_);
        return v___x_328_;
    } else {
        let mut v_key_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_326_);
        v_key_329_ = crate::leanh::lean_ctor_get(v_x_324_, 0);
        crate::leanh::lean_inc(v_key_329_);
        v_value_330_ = crate::leanh::lean_ctor_get(v_x_324_, 1);
        crate::leanh::lean_inc(v_value_330_);
        v_tail_331_ = crate::leanh::lean_ctor_get(v_x_324_, 2);
        crate::leanh::lean_inc(v_tail_331_);
        crate::leanh::lean_dec_ref_known(v_x_324_, 3);
        v___x_332_ = crate::leanh::lean_apply_4(
            v_h__2_327_,
            v_key_329_,
            v_value_330_,
            v_tail_331_,
            v_x_325_,
        );
        return v___x_332_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__3_splitter(
    mut v_00_u03b1_333_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_334_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_335_: *mut crate::leanh::LeanObject,
    mut v_motive_336_: *mut crate::leanh::LeanObject,
    mut v_x_337_: *mut crate::leanh::LeanObject,
    mut v_x_338_: *mut crate::leanh::LeanObject,
    mut v_h__1_339_: *mut crate::leanh::LeanObject,
    mut v_h__2_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_337_) == 0 {
        let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_340_);
        v___x_341_ = crate::leanh::lean_apply_1(v_h__1_339_, v_x_338_);
        return v___x_341_;
    } else {
        let mut v_key_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_339_);
        v_key_342_ = crate::leanh::lean_ctor_get(v_x_337_, 0);
        crate::leanh::lean_inc(v_key_342_);
        v_value_343_ = crate::leanh::lean_ctor_get(v_x_337_, 1);
        crate::leanh::lean_inc(v_value_343_);
        v_tail_344_ = crate::leanh::lean_ctor_get(v_x_337_, 2);
        crate::leanh::lean_inc(v_tail_344_);
        crate::leanh::lean_dec_ref_known(v_x_337_, 3);
        v___x_345_ = crate::leanh::lean_apply_4(
            v_h__2_340_,
            v_key_342_,
            v_value_343_,
            v_tail_344_,
            v_x_338_,
        );
        return v___x_345_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter___redArg(
    mut v_____do__lift_346_: *mut crate::leanh::LeanObject,
    mut v_h__1_347_: *mut crate::leanh::LeanObject,
    mut v_h__2_348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_346_) == 0 {
        let mut v_a_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_348_);
        v_a_349_ = crate::leanh::lean_ctor_get(v_____do__lift_346_, 0);
        crate::leanh::lean_inc(v_a_349_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_346_, 1);
        v___x_350_ = crate::leanh::lean_apply_1(v_h__1_347_, v_a_349_);
        return v___x_350_;
    } else {
        let mut v_a_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_347_);
        v_a_351_ = crate::leanh::lean_ctor_get(v_____do__lift_346_, 0);
        crate::leanh::lean_inc(v_a_351_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_346_, 1);
        v___x_352_ = crate::leanh::lean_apply_1(v_h__2_348_, v_a_351_);
        return v___x_352_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter(
    mut v_00_u03b4_353_: *mut crate::leanh::LeanObject,
    mut v_motive_354_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_355_: *mut crate::leanh::LeanObject,
    mut v_h__1_356_: *mut crate::leanh::LeanObject,
    mut v_h__2_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_355_) == 0 {
        let mut v_a_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_357_);
        v_a_358_ = crate::leanh::lean_ctor_get(v_____do__lift_355_, 0);
        crate::leanh::lean_inc(v_a_358_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_355_, 1);
        v___x_359_ = crate::leanh::lean_apply_1(v_h__1_356_, v_a_358_);
        return v___x_359_;
    } else {
        let mut v_a_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_356_);
        v_a_360_ = crate::leanh::lean_ctor_get(v_____do__lift_355_, 0);
        crate::leanh::lean_inc(v_a_360_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_355_, 1);
        v___x_361_ = crate::leanh::lean_apply_1(v_h__2_357_, v_a_360_);
        return v___x_361_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_362_: *mut crate::leanh::LeanObject,
    mut v_h__1_363_: *mut crate::leanh::LeanObject,
    mut v_h__2_364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_362_) == 0 {
        let mut v_a_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_364_);
        v_a_365_ = crate::leanh::lean_ctor_get(v_x_362_, 0);
        crate::leanh::lean_inc(v_a_365_);
        crate::leanh::lean_dec_ref_known(v_x_362_, 1);
        v___x_366_ = crate::leanh::lean_apply_1(v_h__1_363_, v_a_365_);
        return v___x_366_;
    } else {
        let mut v_a_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_363_);
        v_a_367_ = crate::leanh::lean_ctor_get(v_x_362_, 0);
        crate::leanh::lean_inc(v_a_367_);
        crate::leanh::lean_dec_ref_known(v_x_362_, 1);
        v___x_368_ = crate::leanh::lean_apply_1(v_h__2_364_, v_a_367_);
        return v___x_368_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_369_: *mut crate::leanh::LeanObject,
    mut v_motive_370_: *mut crate::leanh::LeanObject,
    mut v_x_371_: *mut crate::leanh::LeanObject,
    mut v_h__1_372_: *mut crate::leanh::LeanObject,
    mut v_h__2_373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_371_) == 0 {
        let mut v_a_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_373_);
        v_a_374_ = crate::leanh::lean_ctor_get(v_x_371_, 0);
        crate::leanh::lean_inc(v_a_374_);
        crate::leanh::lean_dec_ref_known(v_x_371_, 1);
        v___x_375_ = crate::leanh::lean_apply_1(v_h__1_372_, v_a_374_);
        return v___x_375_;
    } else {
        let mut v_a_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_372_);
        v_a_376_ = crate::leanh::lean_ctor_get(v_x_371_, 0);
        crate::leanh::lean_inc(v_a_376_);
        crate::leanh::lean_dec_ref_known(v_x_371_, 1);
        v___x_377_ = crate::leanh::lean_apply_1(v_h__2_373_, v_a_376_);
        return v___x_377_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter___redArg(
    mut v_x_378_: *mut crate::leanh::LeanObject,
    mut v_h__1_379_: *mut crate::leanh::LeanObject,
    mut v_h__2_380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_378_) == 0 {
        let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_379_);
        v___x_381_ = crate::leanh::lean_box(0);
        v___x_382_ = crate::leanh::lean_apply_1(v_h__2_380_, v___x_381_);
        return v___x_382_;
    } else {
        let mut v_val_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_380_);
        v_val_383_ = crate::leanh::lean_ctor_get(v_x_378_, 0);
        crate::leanh::lean_inc(v_val_383_);
        crate::leanh::lean_dec_ref_known(v_x_378_, 1);
        v___x_384_ = crate::leanh::lean_apply_1(v_h__1_379_, v_val_383_);
        return v___x_384_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_385_: *mut crate::leanh::LeanObject,
    mut v_motive_386_: *mut crate::leanh::LeanObject,
    mut v_x_387_: *mut crate::leanh::LeanObject,
    mut v_h__1_388_: *mut crate::leanh::LeanObject,
    mut v_h__2_389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_387_) == 0 {
        let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_388_);
        v___x_390_ = crate::leanh::lean_box(0);
        v___x_391_ = crate::leanh::lean_apply_1(v_h__2_389_, v___x_390_);
        return v___x_391_;
    } else {
        let mut v_val_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_389_);
        v_val_392_ = crate::leanh::lean_ctor_get(v_x_387_, 0);
        crate::leanh::lean_inc(v_val_392_);
        crate::leanh::lean_dec_ref_known(v_x_387_, 1);
        v___x_393_ = crate::leanh::lean_apply_1(v_h__1_388_, v_val_392_);
        return v___x_393_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__3_splitter___redArg(
    mut v_data_394_: *mut crate::leanh::LeanObject,
    mut v_h__1_395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_396_ = crate::leanh::lean_apply_2(v_h__1_395_, v_data_394_, crate::leanh::lean_box(0));
    return v___x_396_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__3_splitter(
    mut v_00_u03b1_397_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_398_: *mut crate::leanh::LeanObject,
    mut v_motive_399_: *mut crate::leanh::LeanObject,
    mut v_data_400_: *mut crate::leanh::LeanObject,
    mut v_h__1_401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = crate::leanh::lean_apply_2(v_h__1_401_, v_data_400_, crate::leanh::lean_box(0));
    return v___x_402_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter___redArg(
    mut v_m_403_: *mut crate::leanh::LeanObject,
    mut v_h__1_404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_405_ = crate::leanh::lean_ctor_get(v_m_403_, 0);
    crate::leanh::lean_inc(v_size_405_);
    v_buckets_406_ = crate::leanh::lean_ctor_get(v_m_403_, 1);
    crate::leanh::lean_inc_ref(v_buckets_406_);
    crate::leanh::lean_dec_ref(v_m_403_);
    v___x_407_ = crate::leanh::lean_apply_3(
        v_h__1_404_,
        v_size_405_,
        v_buckets_406_,
        crate::leanh::lean_box(0),
    );
    return v___x_407_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter(
    mut v_00_u03b1_408_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_409_: *mut crate::leanh::LeanObject,
    mut v_motive_410_: *mut crate::leanh::LeanObject,
    mut v_m_411_: *mut crate::leanh::LeanObject,
    mut v_h__1_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_413_ = crate::leanh::lean_ctor_get(v_m_411_, 0);
    crate::leanh::lean_inc(v_size_413_);
    v_buckets_414_ = crate::leanh::lean_ctor_get(v_m_411_, 1);
    crate::leanh::lean_inc_ref(v_buckets_414_);
    crate::leanh::lean_dec_ref(v_m_411_);
    v___x_415_ = crate::leanh::lean_apply_3(
        v_h__1_412_,
        v_size_413_,
        v_buckets_414_,
        crate::leanh::lean_box(0),
    );
    return v___x_415_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(
    mut v_x_416_: *mut crate::leanh::LeanObject,
    mut v_h__1_417_: *mut crate::leanh::LeanObject,
    mut v_h__2_418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_416_) == 0 {
        let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_418_);
        v___x_419_ = crate::leanh::lean_box(0);
        v___x_420_ = crate::leanh::lean_apply_1(v_h__1_417_, v___x_419_);
        return v___x_420_;
    } else {
        let mut v_val_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_417_);
        v_val_421_ = crate::leanh::lean_ctor_get(v_x_416_, 0);
        crate::leanh::lean_inc(v_val_421_);
        crate::leanh::lean_dec_ref_known(v_x_416_, 1);
        v___x_422_ = crate::leanh::lean_apply_1(v_h__2_418_, v_val_421_);
        return v___x_422_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(
    mut v_00_u03b1_423_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_424_: *mut crate::leanh::LeanObject,
    mut v_a_425_: *mut crate::leanh::LeanObject,
    mut v_motive_426_: *mut crate::leanh::LeanObject,
    mut v_x_427_: *mut crate::leanh::LeanObject,
    mut v_h__1_428_: *mut crate::leanh::LeanObject,
    mut v_h__2_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_427_) == 0 {
        let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_429_);
        v___x_430_ = crate::leanh::lean_box(0);
        v___x_431_ = crate::leanh::lean_apply_1(v_h__1_428_, v___x_430_);
        return v___x_431_;
    } else {
        let mut v_val_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_428_);
        v_val_432_ = crate::leanh::lean_ctor_get(v_x_427_, 0);
        crate::leanh::lean_inc(v_val_432_);
        crate::leanh::lean_dec_ref_known(v_x_427_, 1);
        v___x_433_ = crate::leanh::lean_apply_1(v_h__2_429_, v_val_432_);
        return v___x_433_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___boxed(
    mut v_00_u03b1_434_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_435_: *mut crate::leanh::LeanObject,
    mut v_a_436_: *mut crate::leanh::LeanObject,
    mut v_motive_437_: *mut crate::leanh::LeanObject,
    mut v_x_438_: *mut crate::leanh::LeanObject,
    mut v_h__1_439_: *mut crate::leanh::LeanObject,
    mut v_h__2_440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_441_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(v_00_u03b1_434_, v_00_u03b2_435_, v_a_436_, v_motive_437_, v_x_438_, v_h__1_439_, v_h__2_440_);
    crate::leanh::lean_dec(v_a_436_);
    return v_res_441_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(
    mut v_x_442_: *mut crate::leanh::LeanObject,
    mut v_h__1_443_: *mut crate::leanh::LeanObject,
    mut v_h__2_444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_442_) == 0 {
        let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_444_);
        v___x_445_ = crate::leanh::lean_box(0);
        v___x_446_ = crate::leanh::lean_apply_1(v_h__1_443_, v___x_445_);
        return v___x_446_;
    } else {
        let mut v_val_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_443_);
        v_val_447_ = crate::leanh::lean_ctor_get(v_x_442_, 0);
        crate::leanh::lean_inc(v_val_447_);
        crate::leanh::lean_dec_ref_known(v_x_442_, 1);
        v___x_448_ = crate::leanh::lean_apply_1(v_h__2_444_, v_val_447_);
        return v___x_448_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(
    mut v_00_u03b2_449_: *mut crate::leanh::LeanObject,
    mut v_motive_450_: *mut crate::leanh::LeanObject,
    mut v_x_451_: *mut crate::leanh::LeanObject,
    mut v_h__1_452_: *mut crate::leanh::LeanObject,
    mut v_h__2_453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_451_) == 0 {
        let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_453_);
        v___x_454_ = crate::leanh::lean_box(0);
        v___x_455_ = crate::leanh::lean_apply_1(v_h__1_452_, v___x_454_);
        return v___x_455_;
    } else {
        let mut v_val_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_452_);
        v_val_456_ = crate::leanh::lean_ctor_get(v_x_451_, 0);
        crate::leanh::lean_inc(v_val_456_);
        crate::leanh::lean_dec_ref_known(v_x_451_, 1);
        v___x_457_ = crate::leanh::lean_apply_1(v_h__2_453_, v_val_456_);
        return v___x_457_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(
    mut v_x_458_: *mut crate::leanh::LeanObject,
    mut v_h__1_459_: *mut crate::leanh::LeanObject,
    mut v_h__2_460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_458_) == 0 {
        let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_460_);
        v___x_461_ = crate::leanh::lean_box(0);
        v___x_462_ = crate::leanh::lean_apply_1(v_h__1_459_, v___x_461_);
        return v___x_462_;
    } else {
        let mut v_head_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_459_);
        v_head_463_ = crate::leanh::lean_ctor_get(v_x_458_, 0);
        crate::leanh::lean_inc(v_head_463_);
        v_tail_464_ = crate::leanh::lean_ctor_get(v_x_458_, 1);
        crate::leanh::lean_inc(v_tail_464_);
        crate::leanh::lean_dec_ref_known(v_x_458_, 2);
        v_fst_465_ = crate::leanh::lean_ctor_get(v_head_463_, 0);
        crate::leanh::lean_inc(v_fst_465_);
        v_snd_466_ = crate::leanh::lean_ctor_get(v_head_463_, 1);
        crate::leanh::lean_inc(v_snd_466_);
        crate::leanh::lean_dec(v_head_463_);
        v___x_467_ = crate::leanh::lean_apply_3(v_h__2_460_, v_fst_465_, v_snd_466_, v_tail_464_);
        return v___x_467_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter(
    mut v_00_u03b1_468_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_469_: *mut crate::leanh::LeanObject,
    mut v_motive_470_: *mut crate::leanh::LeanObject,
    mut v_x_471_: *mut crate::leanh::LeanObject,
    mut v_h__1_472_: *mut crate::leanh::LeanObject,
    mut v_h__2_473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_471_) == 0 {
        let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_473_);
        v___x_474_ = crate::leanh::lean_box(0);
        v___x_475_ = crate::leanh::lean_apply_1(v_h__1_472_, v___x_474_);
        return v___x_475_;
    } else {
        let mut v_head_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_472_);
        v_head_476_ = crate::leanh::lean_ctor_get(v_x_471_, 0);
        crate::leanh::lean_inc(v_head_476_);
        v_tail_477_ = crate::leanh::lean_ctor_get(v_x_471_, 1);
        crate::leanh::lean_inc(v_tail_477_);
        crate::leanh::lean_dec_ref_known(v_x_471_, 2);
        v_fst_478_ = crate::leanh::lean_ctor_get(v_head_476_, 0);
        crate::leanh::lean_inc(v_fst_478_);
        v_snd_479_ = crate::leanh::lean_ctor_get(v_head_476_, 1);
        crate::leanh::lean_inc(v_snd_479_);
        crate::leanh::lean_dec(v_head_476_);
        v___x_480_ = crate::leanh::lean_apply_3(v_h__2_473_, v_fst_478_, v_snd_479_, v_tail_477_);
        return v___x_480_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(
    mut v_toInsert_481_: *mut crate::leanh::LeanObject,
    mut v_h__1_482_: *mut crate::leanh::LeanObject,
    mut v_h__2_483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_toInsert_481_) == 0 {
        let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_483_);
        v___x_484_ = crate::leanh::lean_box(0);
        v___x_485_ = crate::leanh::lean_apply_1(v_h__1_482_, v___x_484_);
        return v___x_485_;
    } else {
        let mut v_head_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_482_);
        v_head_486_ = crate::leanh::lean_ctor_get(v_toInsert_481_, 0);
        crate::leanh::lean_inc(v_head_486_);
        v_tail_487_ = crate::leanh::lean_ctor_get(v_toInsert_481_, 1);
        crate::leanh::lean_inc(v_tail_487_);
        crate::leanh::lean_dec_ref_known(v_toInsert_481_, 2);
        v___x_488_ = crate::leanh::lean_apply_2(v_h__2_483_, v_head_486_, v_tail_487_);
        return v___x_488_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(
    mut v_00_u03b1_489_: *mut crate::leanh::LeanObject,
    mut v_motive_490_: *mut crate::leanh::LeanObject,
    mut v_toInsert_491_: *mut crate::leanh::LeanObject,
    mut v_h__1_492_: *mut crate::leanh::LeanObject,
    mut v_h__2_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_toInsert_491_) == 0 {
        let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_493_);
        v___x_494_ = crate::leanh::lean_box(0);
        v___x_495_ = crate::leanh::lean_apply_1(v_h__1_492_, v___x_494_);
        return v___x_495_;
    } else {
        let mut v_head_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_492_);
        v_head_496_ = crate::leanh::lean_ctor_get(v_toInsert_491_, 0);
        crate::leanh::lean_inc(v_head_496_);
        v_tail_497_ = crate::leanh::lean_ctor_get(v_toInsert_491_, 1);
        crate::leanh::lean_inc(v_tail_497_);
        crate::leanh::lean_dec_ref_known(v_toInsert_491_, 2);
        v___x_498_ = crate::leanh::lean_apply_2(v_h__2_493_, v_head_496_, v_tail_497_);
        return v___x_498_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter___redArg(
    mut v_x_499_: *mut crate::leanh::LeanObject,
    mut v_h__1_500_: *mut crate::leanh::LeanObject,
    mut v_h__2_501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_499_) == 0 {
        let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_500_);
        v___x_502_ = crate::leanh::lean_box(0);
        v___x_503_ = crate::leanh::lean_apply_1(v_h__2_501_, v___x_502_);
        return v___x_503_;
    } else {
        let mut v_val_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_501_);
        v_val_504_ = crate::leanh::lean_ctor_get(v_x_499_, 0);
        crate::leanh::lean_inc(v_val_504_);
        crate::leanh::lean_dec_ref_known(v_x_499_, 1);
        v___x_505_ = crate::leanh::lean_apply_1(v_h__1_500_, v_val_504_);
        return v___x_505_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter(
    mut v_00_u03b1_506_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_507_: *mut crate::leanh::LeanObject,
    mut v_motive_508_: *mut crate::leanh::LeanObject,
    mut v_x_509_: *mut crate::leanh::LeanObject,
    mut v_h__1_510_: *mut crate::leanh::LeanObject,
    mut v_h__2_511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_509_) == 0 {
        let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_510_);
        v___x_512_ = crate::leanh::lean_box(0);
        v___x_513_ = crate::leanh::lean_apply_1(v_h__2_511_, v___x_512_);
        return v___x_513_;
    } else {
        let mut v_val_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_511_);
        v_val_514_ = crate::leanh::lean_ctor_get(v_x_509_, 0);
        crate::leanh::lean_inc(v_val_514_);
        crate::leanh::lean_dec_ref_known(v_x_509_, 1);
        v___x_515_ = crate::leanh::lean_apply_1(v_h__1_510_, v_val_514_);
        return v___x_515_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter___redArg(
    mut v_x_516_: *mut crate::leanh::LeanObject,
    mut v_h__1_517_: *mut crate::leanh::LeanObject,
    mut v_h__2_518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_516_) == 0 {
        let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_517_);
        v___x_519_ = crate::leanh::lean_box(0);
        v___x_520_ = crate::leanh::lean_apply_1(v_h__2_518_, v___x_519_);
        return v___x_520_;
    } else {
        let mut v_val_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_518_);
        v_val_521_ = crate::leanh::lean_ctor_get(v_x_516_, 0);
        crate::leanh::lean_inc(v_val_521_);
        crate::leanh::lean_dec_ref_known(v_x_516_, 1);
        v___x_522_ = crate::leanh::lean_apply_1(v_h__1_517_, v_val_521_);
        return v___x_522_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter(
    mut v_00_u03b1_523_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_524_: *mut crate::leanh::LeanObject,
    mut v_motive_525_: *mut crate::leanh::LeanObject,
    mut v_x_526_: *mut crate::leanh::LeanObject,
    mut v_h__1_527_: *mut crate::leanh::LeanObject,
    mut v_h__2_528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_526_) == 0 {
        let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_527_);
        v___x_529_ = crate::leanh::lean_box(0);
        v___x_530_ = crate::leanh::lean_apply_1(v_h__2_528_, v___x_529_);
        return v___x_530_;
    } else {
        let mut v_val_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_528_);
        v_val_531_ = crate::leanh::lean_ctor_get(v_x_526_, 0);
        crate::leanh::lean_inc(v_val_531_);
        crate::leanh::lean_dec_ref_known(v_x_526_, 1);
        v___x_532_ = crate::leanh::lean_apply_1(v_h__1_527_, v_val_531_);
        return v___x_532_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0(
    mut v_inst_533_: *mut crate::leanh::LeanObject,
    mut v_inst_534_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_535_: *mut crate::leanh::LeanObject,
    mut v_x1_536_: *mut crate::leanh::LeanObject,
    mut v_x2_537_: *mut crate::leanh::LeanObject,
    mut v_x3_538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(
        v_inst_533_,
        v_inst_534_,
        v_m_u2081_535_,
        v_x1_536_,
        v_x2_537_,
    );
    return v___x_539_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0___boxed(
    mut v_inst_540_: *mut crate::leanh::LeanObject,
    mut v_inst_541_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_542_: *mut crate::leanh::LeanObject,
    mut v_x1_543_: *mut crate::leanh::LeanObject,
    mut v_x2_544_: *mut crate::leanh::LeanObject,
    mut v_x3_545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_546_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0(
        v_inst_540_,
        v_inst_541_,
        v_m_u2081_542_,
        v_x1_543_,
        v_x2_544_,
        v_x3_545_,
    );
    crate::leanh::lean_dec(v_x3_545_);
    crate::leanh::lean_dec_ref(v_m_u2081_542_);
    return v_res_546_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__1(
    mut v___x_547_: *mut crate::leanh::LeanObject,
    mut v___f_548_: *mut crate::leanh::LeanObject,
    mut v_acc_549_: *mut crate::leanh::LeanObject,
    mut v_l_550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_547_, v___f_548_, v_acc_549_, v_l_550_,
    );
    return v___x_551_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_571_ = crate::leanh::lean_box(0);
    v___x_572_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_573_ = lean_mk_array(v___x_572_, v___x_571_);
    return v___x_573_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_574_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10_once
        ),
        _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10,
    );
    v___x_575_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_576_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_576_, 0, v___x_575_);
    crate::leanh::lean_ctor_set(v___x_576_, 1, v___x_574_);
    return v___x_576_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg(
    mut v_inst_577_: *mut crate::leanh::LeanObject,
    mut v_inst_578_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_579_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u8 = 0;
    v___x_581_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9;
    v_buckets_582_ = crate::leanh::lean_ctor_get(v_m_u2082_580_, 1);
    crate::leanh::lean_inc_ref(v_buckets_582_);
    crate::leanh::lean_dec_ref(v_m_u2082_580_);
    v___x_583_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_584_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11_once
        ),
        _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11,
    );
    v___x_585_ = lean_array_get_size(v_buckets_582_);
    v___x_586_ = lean_nat_dec_lt(v___x_583_, v___x_585_);
    if v___x_586_ == 0 {
        crate::leanh::lean_dec_ref(v_buckets_582_);
        crate::leanh::lean_dec_ref(v_m_u2081_579_);
        crate::leanh::lean_dec_ref(v_inst_578_);
        crate::leanh::lean_dec_ref(v_inst_577_);
        return v___x_584_;
    } else {
        let mut v___f_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_589_: u8 = 0;
        v___f_587_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            3,
        );
        crate::leanh::lean_closure_set(v___f_587_, 0, v_inst_577_);
        crate::leanh::lean_closure_set(v___f_587_, 1, v_inst_578_);
        crate::leanh::lean_closure_set(v___f_587_, 2, v_m_u2081_579_);
        v___f_588_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__1
                as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_588_, 0, v___x_581_);
        crate::leanh::lean_closure_set(v___f_588_, 1, v___f_587_);
        v___x_589_ = lean_nat_dec_le(v___x_585_, v___x_585_);
        if v___x_589_ == 0 {
            if v___x_586_ == 0 {
                crate::leanh::lean_dec_ref(v___f_588_);
                crate::leanh::lean_dec_ref(v_buckets_582_);
                return v___x_584_;
            } else {
                let mut v___x_590_: usize = 0;
                let mut v___x_591_: usize = 0;
                let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_590_ = 0usize;
                v___x_591_ = lean_usize_of_nat(v___x_585_);
                v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_581_,
                    v___f_588_,
                    v_buckets_582_,
                    v___x_590_,
                    v___x_591_,
                    v___x_584_,
                );
                return v___x_592_;
            }
        } else {
            let mut v___x_593_: usize = 0;
            let mut v___x_594_: usize = 0;
            let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_593_ = 0usize;
            v___x_594_ = lean_usize_of_nat(v___x_585_);
            v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_581_,
                v___f_588_,
                v_buckets_582_,
                v___x_593_,
                v___x_594_,
                v___x_584_,
            );
            return v___x_595_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098(
    mut v_00_u03b1_596_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_597_: *mut crate::leanh::LeanObject,
    mut v_inst_598_: *mut crate::leanh::LeanObject,
    mut v_inst_599_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_600_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_602_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg(
        v_inst_598_,
        v_inst_599_,
        v_m_u2081_600_,
        v_m_u2082_601_,
    );
    return v___x_602_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Internal_WF(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_RawDef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Internal_WF(
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
pub unsafe fn initialize_Std_Data_DHashMap_Internal_WF(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Internal_List_Associative(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Raw(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_RawDef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_WF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Internal_WF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Internal_WF(builtin);
}
