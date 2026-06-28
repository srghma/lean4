// Lean compiler output
// Module: Std.Data.DHashMap.Internal.WF
// Imports: Std.Data.Internal.List.Associative Std.Data.DHashMap.Raw Std.Data.DHashMap.Internal.Defs Std.Data.DHashMap.Internal.Model Std.Data.DHashMap.Internal.AssocList.Basic Std.Data.DHashMap.RawDef Init.Data.Array.Bootstrap Init.Data.List.Nat.TakeDrop Init.Data.List.TakeDrop
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_dec_le, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__2_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__2_value
) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__3_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__3_value
) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__4_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__4_value
) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__5_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__5_value
) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__6_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__6_value
) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__7_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__7_value
) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__8_value:
    LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__7_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__8_value
) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__8_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__6_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9_value
) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter___redArg(
    mut v_x_302_: *mut LeanObject,
    mut v_x_303_: *mut LeanObject,
    mut v_h__1_304_: *mut LeanObject,
    mut v_h__2_305_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_303_) == 0 {
        let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_305_);
        v___x_306_ = lean_apply_1(v_h__1_304_, v_x_302_);
        return v___x_306_;
    } else {
        let mut v_key_307_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_308_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_304_);
        v_key_307_ = lean_ctor_get(v_x_303_, 0);
        lean_inc(v_key_307_);
        v_value_308_ = lean_ctor_get(v_x_303_, 1);
        lean_inc(v_value_308_);
        v_tail_309_ = lean_ctor_get(v_x_303_, 2);
        lean_inc(v_tail_309_);
        lean_dec_ref_known(v_x_303_, 3);
        v___x_310_ = lean_apply_4(v_h__2_305_, v_x_302_, v_key_307_, v_value_308_, v_tail_309_);
        return v___x_310_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter(
    mut v_00_u03b1_311_: *mut LeanObject,
    mut v_00_u03b2_312_: *mut LeanObject,
    mut v_00_u03b4_313_: *mut LeanObject,
    mut v_motive_314_: *mut LeanObject,
    mut v_x_315_: *mut LeanObject,
    mut v_x_316_: *mut LeanObject,
    mut v_h__1_317_: *mut LeanObject,
    mut v_h__2_318_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_316_) == 0 {
        let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_318_);
        v___x_319_ = lean_apply_1(v_h__1_317_, v_x_315_);
        return v___x_319_;
    } else {
        let mut v_key_320_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_321_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_317_);
        v_key_320_ = lean_ctor_get(v_x_316_, 0);
        lean_inc(v_key_320_);
        v_value_321_ = lean_ctor_get(v_x_316_, 1);
        lean_inc(v_value_321_);
        v_tail_322_ = lean_ctor_get(v_x_316_, 2);
        lean_inc(v_tail_322_);
        lean_dec_ref_known(v_x_316_, 3);
        v___x_323_ = lean_apply_4(v_h__2_318_, v_x_315_, v_key_320_, v_value_321_, v_tail_322_);
        return v___x_323_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__3_splitter___redArg(
    mut v_x_324_: *mut LeanObject,
    mut v_x_325_: *mut LeanObject,
    mut v_h__1_326_: *mut LeanObject,
    mut v_h__2_327_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_324_) == 0 {
        let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_327_);
        v___x_328_ = lean_apply_1(v_h__1_326_, v_x_325_);
        return v___x_328_;
    } else {
        let mut v_key_329_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_330_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_331_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_326_);
        v_key_329_ = lean_ctor_get(v_x_324_, 0);
        lean_inc(v_key_329_);
        v_value_330_ = lean_ctor_get(v_x_324_, 1);
        lean_inc(v_value_330_);
        v_tail_331_ = lean_ctor_get(v_x_324_, 2);
        lean_inc(v_tail_331_);
        lean_dec_ref_known(v_x_324_, 3);
        v___x_332_ = lean_apply_4(v_h__2_327_, v_key_329_, v_value_330_, v_tail_331_, v_x_325_);
        return v___x_332_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__3_splitter(
    mut v_00_u03b1_333_: *mut LeanObject,
    mut v_00_u03b2_334_: *mut LeanObject,
    mut v_00_u03b4_335_: *mut LeanObject,
    mut v_motive_336_: *mut LeanObject,
    mut v_x_337_: *mut LeanObject,
    mut v_x_338_: *mut LeanObject,
    mut v_h__1_339_: *mut LeanObject,
    mut v_h__2_340_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_337_) == 0 {
        let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_340_);
        v___x_341_ = lean_apply_1(v_h__1_339_, v_x_338_);
        return v___x_341_;
    } else {
        let mut v_key_342_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_343_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_344_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_339_);
        v_key_342_ = lean_ctor_get(v_x_337_, 0);
        lean_inc(v_key_342_);
        v_value_343_ = lean_ctor_get(v_x_337_, 1);
        lean_inc(v_value_343_);
        v_tail_344_ = lean_ctor_get(v_x_337_, 2);
        lean_inc(v_tail_344_);
        lean_dec_ref_known(v_x_337_, 3);
        v___x_345_ = lean_apply_4(v_h__2_340_, v_key_342_, v_value_343_, v_tail_344_, v_x_338_);
        return v___x_345_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter___redArg(
    mut v_____do__lift_346_: *mut LeanObject,
    mut v_h__1_347_: *mut LeanObject,
    mut v_h__2_348_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_346_) == 0 {
        let mut v_a_349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_348_);
        v_a_349_ = lean_ctor_get(v_____do__lift_346_, 0);
        lean_inc(v_a_349_);
        lean_dec_ref_known(v_____do__lift_346_, 1);
        v___x_350_ = lean_apply_1(v_h__1_347_, v_a_349_);
        return v___x_350_;
    } else {
        let mut v_a_351_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_347_);
        v_a_351_ = lean_ctor_get(v_____do__lift_346_, 0);
        lean_inc(v_a_351_);
        lean_dec_ref_known(v_____do__lift_346_, 1);
        v___x_352_ = lean_apply_1(v_h__2_348_, v_a_351_);
        return v___x_352_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter(
    mut v_00_u03b4_353_: *mut LeanObject,
    mut v_motive_354_: *mut LeanObject,
    mut v_____do__lift_355_: *mut LeanObject,
    mut v_h__1_356_: *mut LeanObject,
    mut v_h__2_357_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_355_) == 0 {
        let mut v_a_358_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_357_);
        v_a_358_ = lean_ctor_get(v_____do__lift_355_, 0);
        lean_inc(v_a_358_);
        lean_dec_ref_known(v_____do__lift_355_, 1);
        v___x_359_ = lean_apply_1(v_h__1_356_, v_a_358_);
        return v___x_359_;
    } else {
        let mut v_a_360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_356_);
        v_a_360_ = lean_ctor_get(v_____do__lift_355_, 0);
        lean_inc(v_a_360_);
        lean_dec_ref_known(v_____do__lift_355_, 1);
        v___x_361_ = lean_apply_1(v_h__2_357_, v_a_360_);
        return v___x_361_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_362_: *mut LeanObject,
    mut v_h__1_363_: *mut LeanObject,
    mut v_h__2_364_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_362_) == 0 {
        let mut v_a_365_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_364_);
        v_a_365_ = lean_ctor_get(v_x_362_, 0);
        lean_inc(v_a_365_);
        lean_dec_ref_known(v_x_362_, 1);
        v___x_366_ = lean_apply_1(v_h__1_363_, v_a_365_);
        return v___x_366_;
    } else {
        let mut v_a_367_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_363_);
        v_a_367_ = lean_ctor_get(v_x_362_, 0);
        lean_inc(v_a_367_);
        lean_dec_ref_known(v_x_362_, 1);
        v___x_368_ = lean_apply_1(v_h__2_364_, v_a_367_);
        return v___x_368_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_369_: *mut LeanObject,
    mut v_motive_370_: *mut LeanObject,
    mut v_x_371_: *mut LeanObject,
    mut v_h__1_372_: *mut LeanObject,
    mut v_h__2_373_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_371_) == 0 {
        let mut v_a_374_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_373_);
        v_a_374_ = lean_ctor_get(v_x_371_, 0);
        lean_inc(v_a_374_);
        lean_dec_ref_known(v_x_371_, 1);
        v___x_375_ = lean_apply_1(v_h__1_372_, v_a_374_);
        return v___x_375_;
    } else {
        let mut v_a_376_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_372_);
        v_a_376_ = lean_ctor_get(v_x_371_, 0);
        lean_inc(v_a_376_);
        lean_dec_ref_known(v_x_371_, 1);
        v___x_377_ = lean_apply_1(v_h__2_373_, v_a_376_);
        return v___x_377_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter___redArg(
    mut v_x_378_: *mut LeanObject,
    mut v_h__1_379_: *mut LeanObject,
    mut v_h__2_380_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_378_) == 0 {
        let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_379_);
        v___x_381_ = lean_box(0);
        v___x_382_ = lean_apply_1(v_h__2_380_, v___x_381_);
        return v___x_382_;
    } else {
        let mut v_val_383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_380_);
        v_val_383_ = lean_ctor_get(v_x_378_, 0);
        lean_inc(v_val_383_);
        lean_dec_ref_known(v_x_378_, 1);
        v___x_384_ = lean_apply_1(v_h__1_379_, v_val_383_);
        return v___x_384_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_385_: *mut LeanObject,
    mut v_motive_386_: *mut LeanObject,
    mut v_x_387_: *mut LeanObject,
    mut v_h__1_388_: *mut LeanObject,
    mut v_h__2_389_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_387_) == 0 {
        let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_388_);
        v___x_390_ = lean_box(0);
        v___x_391_ = lean_apply_1(v_h__2_389_, v___x_390_);
        return v___x_391_;
    } else {
        let mut v_val_392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_389_);
        v_val_392_ = lean_ctor_get(v_x_387_, 0);
        lean_inc(v_val_392_);
        lean_dec_ref_known(v_x_387_, 1);
        v___x_393_ = lean_apply_1(v_h__1_388_, v_val_392_);
        return v___x_393_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__3_splitter___redArg(
    mut v_data_394_: *mut LeanObject,
    mut v_h__1_395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    v___x_396_ = lean_apply_2(v_h__1_395_, v_data_394_, lean_box(0));
    return v___x_396_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__3_splitter(
    mut v_00_u03b1_397_: *mut LeanObject,
    mut v_00_u03b2_398_: *mut LeanObject,
    mut v_motive_399_: *mut LeanObject,
    mut v_data_400_: *mut LeanObject,
    mut v_h__1_401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    v___x_402_ = lean_apply_2(v_h__1_401_, v_data_400_, lean_box(0));
    return v___x_402_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter___redArg(
    mut v_m_403_: *mut LeanObject,
    mut v_h__1_404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    v_size_405_ = lean_ctor_get(v_m_403_, 0);
    lean_inc(v_size_405_);
    v_buckets_406_ = lean_ctor_get(v_m_403_, 1);
    lean_inc_ref(v_buckets_406_);
    lean_dec_ref(v_m_403_);
    v___x_407_ = lean_apply_3(v_h__1_404_, v_size_405_, v_buckets_406_, lean_box(0));
    return v___x_407_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter(
    mut v_00_u03b1_408_: *mut LeanObject,
    mut v_00_u03b2_409_: *mut LeanObject,
    mut v_motive_410_: *mut LeanObject,
    mut v_m_411_: *mut LeanObject,
    mut v_h__1_412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    v_size_413_ = lean_ctor_get(v_m_411_, 0);
    lean_inc(v_size_413_);
    v_buckets_414_ = lean_ctor_get(v_m_411_, 1);
    lean_inc_ref(v_buckets_414_);
    lean_dec_ref(v_m_411_);
    v___x_415_ = lean_apply_3(v_h__1_412_, v_size_413_, v_buckets_414_, lean_box(0));
    return v___x_415_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(
    mut v_x_416_: *mut LeanObject,
    mut v_h__1_417_: *mut LeanObject,
    mut v_h__2_418_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_416_) == 0 {
        let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_418_);
        v___x_419_ = lean_box(0);
        v___x_420_ = lean_apply_1(v_h__1_417_, v___x_419_);
        return v___x_420_;
    } else {
        let mut v_val_421_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_417_);
        v_val_421_ = lean_ctor_get(v_x_416_, 0);
        lean_inc(v_val_421_);
        lean_dec_ref_known(v_x_416_, 1);
        v___x_422_ = lean_apply_1(v_h__2_418_, v_val_421_);
        return v___x_422_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(
    mut v_00_u03b1_423_: *mut LeanObject,
    mut v_00_u03b2_424_: *mut LeanObject,
    mut v_a_425_: *mut LeanObject,
    mut v_motive_426_: *mut LeanObject,
    mut v_x_427_: *mut LeanObject,
    mut v_h__1_428_: *mut LeanObject,
    mut v_h__2_429_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_427_) == 0 {
        let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_429_);
        v___x_430_ = lean_box(0);
        v___x_431_ = lean_apply_1(v_h__1_428_, v___x_430_);
        return v___x_431_;
    } else {
        let mut v_val_432_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_428_);
        v_val_432_ = lean_ctor_get(v_x_427_, 0);
        lean_inc(v_val_432_);
        lean_dec_ref_known(v_x_427_, 1);
        v___x_433_ = lean_apply_1(v_h__2_429_, v_val_432_);
        return v___x_433_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___boxed(
    mut v_00_u03b1_434_: *mut LeanObject,
    mut v_00_u03b2_435_: *mut LeanObject,
    mut v_a_436_: *mut LeanObject,
    mut v_motive_437_: *mut LeanObject,
    mut v_x_438_: *mut LeanObject,
    mut v_h__1_439_: *mut LeanObject,
    mut v_h__2_440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_441_: *mut LeanObject = core::ptr::null_mut();
    v_res_441_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(v_00_u03b1_434_, v_00_u03b2_435_, v_a_436_, v_motive_437_, v_x_438_, v_h__1_439_, v_h__2_440_);
    lean_dec(v_a_436_);
    return v_res_441_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(
    mut v_x_442_: *mut LeanObject,
    mut v_h__1_443_: *mut LeanObject,
    mut v_h__2_444_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_442_) == 0 {
        let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_444_);
        v___x_445_ = lean_box(0);
        v___x_446_ = lean_apply_1(v_h__1_443_, v___x_445_);
        return v___x_446_;
    } else {
        let mut v_val_447_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_443_);
        v_val_447_ = lean_ctor_get(v_x_442_, 0);
        lean_inc(v_val_447_);
        lean_dec_ref_known(v_x_442_, 1);
        v___x_448_ = lean_apply_1(v_h__2_444_, v_val_447_);
        return v___x_448_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(
    mut v_00_u03b2_449_: *mut LeanObject,
    mut v_motive_450_: *mut LeanObject,
    mut v_x_451_: *mut LeanObject,
    mut v_h__1_452_: *mut LeanObject,
    mut v_h__2_453_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_451_) == 0 {
        let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_453_);
        v___x_454_ = lean_box(0);
        v___x_455_ = lean_apply_1(v_h__1_452_, v___x_454_);
        return v___x_455_;
    } else {
        let mut v_val_456_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_452_);
        v_val_456_ = lean_ctor_get(v_x_451_, 0);
        lean_inc(v_val_456_);
        lean_dec_ref_known(v_x_451_, 1);
        v___x_457_ = lean_apply_1(v_h__2_453_, v_val_456_);
        return v___x_457_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(
    mut v_x_458_: *mut LeanObject,
    mut v_h__1_459_: *mut LeanObject,
    mut v_h__2_460_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_458_) == 0 {
        let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_460_);
        v___x_461_ = lean_box(0);
        v___x_462_ = lean_apply_1(v_h__1_459_, v___x_461_);
        return v___x_462_;
    } else {
        let mut v_head_463_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_464_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_465_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_466_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_459_);
        v_head_463_ = lean_ctor_get(v_x_458_, 0);
        lean_inc(v_head_463_);
        v_tail_464_ = lean_ctor_get(v_x_458_, 1);
        lean_inc(v_tail_464_);
        lean_dec_ref_known(v_x_458_, 2);
        v_fst_465_ = lean_ctor_get(v_head_463_, 0);
        lean_inc(v_fst_465_);
        v_snd_466_ = lean_ctor_get(v_head_463_, 1);
        lean_inc(v_snd_466_);
        lean_dec(v_head_463_);
        v___x_467_ = lean_apply_3(v_h__2_460_, v_fst_465_, v_snd_466_, v_tail_464_);
        return v___x_467_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter(
    mut v_00_u03b1_468_: *mut LeanObject,
    mut v_00_u03b2_469_: *mut LeanObject,
    mut v_motive_470_: *mut LeanObject,
    mut v_x_471_: *mut LeanObject,
    mut v_h__1_472_: *mut LeanObject,
    mut v_h__2_473_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_471_) == 0 {
        let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_473_);
        v___x_474_ = lean_box(0);
        v___x_475_ = lean_apply_1(v_h__1_472_, v___x_474_);
        return v___x_475_;
    } else {
        let mut v_head_476_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_477_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_478_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_472_);
        v_head_476_ = lean_ctor_get(v_x_471_, 0);
        lean_inc(v_head_476_);
        v_tail_477_ = lean_ctor_get(v_x_471_, 1);
        lean_inc(v_tail_477_);
        lean_dec_ref_known(v_x_471_, 2);
        v_fst_478_ = lean_ctor_get(v_head_476_, 0);
        lean_inc(v_fst_478_);
        v_snd_479_ = lean_ctor_get(v_head_476_, 1);
        lean_inc(v_snd_479_);
        lean_dec(v_head_476_);
        v___x_480_ = lean_apply_3(v_h__2_473_, v_fst_478_, v_snd_479_, v_tail_477_);
        return v___x_480_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(
    mut v_toInsert_481_: *mut LeanObject,
    mut v_h__1_482_: *mut LeanObject,
    mut v_h__2_483_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_toInsert_481_) == 0 {
        let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_483_);
        v___x_484_ = lean_box(0);
        v___x_485_ = lean_apply_1(v_h__1_482_, v___x_484_);
        return v___x_485_;
    } else {
        let mut v_head_486_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_487_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_482_);
        v_head_486_ = lean_ctor_get(v_toInsert_481_, 0);
        lean_inc(v_head_486_);
        v_tail_487_ = lean_ctor_get(v_toInsert_481_, 1);
        lean_inc(v_tail_487_);
        lean_dec_ref_known(v_toInsert_481_, 2);
        v___x_488_ = lean_apply_2(v_h__2_483_, v_head_486_, v_tail_487_);
        return v___x_488_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(
    mut v_00_u03b1_489_: *mut LeanObject,
    mut v_motive_490_: *mut LeanObject,
    mut v_toInsert_491_: *mut LeanObject,
    mut v_h__1_492_: *mut LeanObject,
    mut v_h__2_493_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_toInsert_491_) == 0 {
        let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_493_);
        v___x_494_ = lean_box(0);
        v___x_495_ = lean_apply_1(v_h__1_492_, v___x_494_);
        return v___x_495_;
    } else {
        let mut v_head_496_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_497_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_492_);
        v_head_496_ = lean_ctor_get(v_toInsert_491_, 0);
        lean_inc(v_head_496_);
        v_tail_497_ = lean_ctor_get(v_toInsert_491_, 1);
        lean_inc(v_tail_497_);
        lean_dec_ref_known(v_toInsert_491_, 2);
        v___x_498_ = lean_apply_2(v_h__2_493_, v_head_496_, v_tail_497_);
        return v___x_498_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter___redArg(
    mut v_x_499_: *mut LeanObject,
    mut v_h__1_500_: *mut LeanObject,
    mut v_h__2_501_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_499_) == 0 {
        let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_500_);
        v___x_502_ = lean_box(0);
        v___x_503_ = lean_apply_1(v_h__2_501_, v___x_502_);
        return v___x_503_;
    } else {
        let mut v_val_504_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_501_);
        v_val_504_ = lean_ctor_get(v_x_499_, 0);
        lean_inc(v_val_504_);
        lean_dec_ref_known(v_x_499_, 1);
        v___x_505_ = lean_apply_1(v_h__1_500_, v_val_504_);
        return v___x_505_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter(
    mut v_00_u03b1_506_: *mut LeanObject,
    mut v_00_u03b2_507_: *mut LeanObject,
    mut v_motive_508_: *mut LeanObject,
    mut v_x_509_: *mut LeanObject,
    mut v_h__1_510_: *mut LeanObject,
    mut v_h__2_511_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_509_) == 0 {
        let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_510_);
        v___x_512_ = lean_box(0);
        v___x_513_ = lean_apply_1(v_h__2_511_, v___x_512_);
        return v___x_513_;
    } else {
        let mut v_val_514_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_511_);
        v_val_514_ = lean_ctor_get(v_x_509_, 0);
        lean_inc(v_val_514_);
        lean_dec_ref_known(v_x_509_, 1);
        v___x_515_ = lean_apply_1(v_h__1_510_, v_val_514_);
        return v___x_515_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter___redArg(
    mut v_x_516_: *mut LeanObject,
    mut v_h__1_517_: *mut LeanObject,
    mut v_h__2_518_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_516_) == 0 {
        let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_517_);
        v___x_519_ = lean_box(0);
        v___x_520_ = lean_apply_1(v_h__2_518_, v___x_519_);
        return v___x_520_;
    } else {
        let mut v_val_521_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_518_);
        v_val_521_ = lean_ctor_get(v_x_516_, 0);
        lean_inc(v_val_521_);
        lean_dec_ref_known(v_x_516_, 1);
        v___x_522_ = lean_apply_1(v_h__1_517_, v_val_521_);
        return v___x_522_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter(
    mut v_00_u03b1_523_: *mut LeanObject,
    mut v_00_u03b2_524_: *mut LeanObject,
    mut v_motive_525_: *mut LeanObject,
    mut v_x_526_: *mut LeanObject,
    mut v_h__1_527_: *mut LeanObject,
    mut v_h__2_528_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_526_) == 0 {
        let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_527_);
        v___x_529_ = lean_box(0);
        v___x_530_ = lean_apply_1(v_h__2_528_, v___x_529_);
        return v___x_530_;
    } else {
        let mut v_val_531_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_528_);
        v_val_531_ = lean_ctor_get(v_x_526_, 0);
        lean_inc(v_val_531_);
        lean_dec_ref_known(v_x_526_, 1);
        v___x_532_ = lean_apply_1(v_h__1_527_, v_val_531_);
        return v___x_532_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0(
    mut v_inst_533_: *mut LeanObject,
    mut v_inst_534_: *mut LeanObject,
    mut v_m_u2081_535_: *mut LeanObject,
    mut v_x1_536_: *mut LeanObject,
    mut v_x2_537_: *mut LeanObject,
    mut v_x3_538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_540_: *mut LeanObject,
    mut v_inst_541_: *mut LeanObject,
    mut v_m_u2081_542_: *mut LeanObject,
    mut v_x1_543_: *mut LeanObject,
    mut v_x2_544_: *mut LeanObject,
    mut v_x3_545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_546_: *mut LeanObject = core::ptr::null_mut();
    v_res_546_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0(
        v_inst_540_,
        v_inst_541_,
        v_m_u2081_542_,
        v_x1_543_,
        v_x2_544_,
        v_x3_545_,
    );
    lean_dec(v_x3_545_);
    lean_dec_ref(v_m_u2081_542_);
    return v_res_546_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__1(
    mut v___x_547_: *mut LeanObject,
    mut v___f_548_: *mut LeanObject,
    mut v_acc_549_: *mut LeanObject,
    mut v_l_550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    v___x_551_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_547_, v___f_548_, v_acc_549_, v_l_550_,
    );
    return v___x_551_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10()
-> *mut LeanObject {
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    v___x_571_ = lean_box(0);
    v___x_572_ = lean_unsigned_to_nat(16);
    v___x_573_ = lean_mk_array(v___x_572_, v___x_571_);
    return v___x_573_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    v___x_574_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10_once
        ),
        _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10,
    );
    v___x_575_ = lean_unsigned_to_nat(0);
    v___x_576_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_576_, 0, v___x_575_);
    lean_ctor_set(v___x_576_, 1, v___x_574_);
    return v___x_576_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg(
    mut v_inst_577_: *mut LeanObject,
    mut v_inst_578_: *mut LeanObject,
    mut v_m_u2081_579_: *mut LeanObject,
    mut v_m_u2082_580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u8 = 0;
    v___x_581_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9;
    v_buckets_582_ = lean_ctor_get(v_m_u2082_580_, 1);
    lean_inc_ref(v_buckets_582_);
    lean_dec_ref(v_m_u2082_580_);
    v___x_583_ = lean_unsigned_to_nat(0);
    v___x_584_ = lean_obj_once(
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
        lean_dec_ref(v_buckets_582_);
        lean_dec_ref(v_m_u2081_579_);
        lean_dec_ref(v_inst_578_);
        lean_dec_ref(v_inst_577_);
        return v___x_584_;
    } else {
        let mut v___f_587_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_588_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_589_: u8 = 0;
        v___f_587_ = lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            3,
        );
        lean_closure_set(v___f_587_, 0, v_inst_577_);
        lean_closure_set(v___f_587_, 1, v_inst_578_);
        lean_closure_set(v___f_587_, 2, v_m_u2081_579_);
        v___f_588_ = lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__1
                as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_588_, 0, v___x_581_);
        lean_closure_set(v___f_588_, 1, v___f_587_);
        v___x_589_ = lean_nat_dec_le(v___x_585_, v___x_585_);
        if v___x_589_ == 0 {
            if v___x_586_ == 0 {
                lean_dec_ref(v___f_588_);
                lean_dec_ref(v_buckets_582_);
                return v___x_584_;
            } else {
                let mut v___x_590_: usize = 0;
                let mut v___x_591_: usize = 0;
                let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
                v___x_590_ = 0usize;
                v___x_591_ = lean_usize_of_nat(v___x_585_);
                v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
            v___x_593_ = 0usize;
            v___x_594_ = lean_usize_of_nat(v___x_585_);
            v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_596_: *mut LeanObject,
    mut v_00_u03b2_597_: *mut LeanObject,
    mut v_inst_598_: *mut LeanObject,
    mut v_inst_599_: *mut LeanObject,
    mut v_m_u2081_600_: *mut LeanObject,
    mut v_m_u2082_601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    v___x_602_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg(
        v_inst_598_,
        v_inst_599_,
        v_m_u2081_600_,
        v_m_u2082_601_,
    );
    return v___x_602_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Internal_WF(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Model(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_RawDef(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Internal_WF(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DHashMap_Internal_WF(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Internal_List_Associative(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_Model(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_RawDef(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_WF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Internal_WF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Internal_WF(builtin);
}
