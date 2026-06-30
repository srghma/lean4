// Lean compiler output
// Module: Std.Data.DHashMap.Internal.Defs
// Imports: Init.Data.Array.Lemmas Std.Data.DHashMap.RawDef Std.Data.Internal.List.Defs Std.Data.DHashMap.Internal.Index Init.Data.Nat.Power2.Basic Init.Data.List.Impl Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
    l_List_foldl___at___00Array_appendList_spec__0___redArg,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::List::Impl::{
    initialize_Init_Data_List_Impl, runtime_initialize_Init_Data_List_Impl,
};
use crate::r#gen::Init::Data::Nat::Power2::Basic::{
    initialize_Init_Data_Nat_Power2_Basic, l_Nat_nextPowerOfTwo,
    runtime_initialize_Init_Data_Nat_Power2_Basic,
};
use crate::r#gen::Init::Data::Option::Basic::l_Option_instBEq_beq___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::{
    l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go,
    l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go,
    l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go,
    l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go,
    l_Std_DHashMap_Internal_AssocList_Const_alter___redArg,
    l_Std_DHashMap_Internal_AssocList_Const_modify___redArg,
    l_Std_DHashMap_Internal_AssocList_alter___redArg,
    l_Std_DHashMap_Internal_AssocList_contains___redArg,
    l_Std_DHashMap_Internal_AssocList_erase___redArg,
    l_Std_DHashMap_Internal_AssocList_foldlM___redArg,
    l_Std_DHashMap_Internal_AssocList_get___redArg,
    l_Std_DHashMap_Internal_AssocList_get_x3f___redArg,
    l_Std_DHashMap_Internal_AssocList_get_x21___redArg,
    l_Std_DHashMap_Internal_AssocList_getCast___redArg,
    l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg,
    l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg,
    l_Std_DHashMap_Internal_AssocList_getCastD___redArg,
    l_Std_DHashMap_Internal_AssocList_getD___redArg,
    l_Std_DHashMap_Internal_AssocList_getEntry___redArg,
    l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg,
    l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg,
    l_Std_DHashMap_Internal_AssocList_getEntryD___redArg,
    l_Std_DHashMap_Internal_AssocList_getKey___redArg,
    l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg,
    l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg,
    l_Std_DHashMap_Internal_AssocList_getKeyD___redArg,
    l_Std_DHashMap_Internal_AssocList_length___redArg,
    l_Std_DHashMap_Internal_AssocList_modify___redArg,
    l_Std_DHashMap_Internal_AssocList_replace___redArg,
    l_Std_DHashMap_Internal_AssocList_toList___redArg,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Index::{
    initialize_Std_Data_DHashMap_Internal_Index,
    runtime_initialize_Std_Data_DHashMap_Internal_Index,
};
use crate::r#gen::Std::Data::DHashMap::RawDef::{
    initialize_Std_Data_DHashMap_RawDef,
    l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2,
    runtime_initialize_Std_Data_DHashMap_RawDef,
};
use crate::r#gen::Std::Data::Internal::List::Defs::{
    initialize_Std_Data_Internal_List_Defs, runtime_initialize_Std_Data_Internal_List_Defs,
};
pub static l_Std_DHashMap_Internal_toListModel___redArg___closed__0_value:
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
static mut l_Std_DHashMap_Internal_toListModel___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_toListModel___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_computeSize___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_computeSize___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_computeSize___redArg___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_computeSize___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_computeSize___redArg___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_computeSize___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_computeSize___redArg___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_computeSize___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_computeSize___redArg___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_computeSize___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_computeSize___redArg___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_computeSize___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_computeSize___redArg___closed__6_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_computeSize___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_computeSize___redArg___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_computeSize___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_computeSize___redArg___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_computeSize___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_computeSize___redArg___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_computeSize___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_computeSize___redArg___closed__10_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DHashMap_Internal_computeSize___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_computeSize___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_computeSize___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_numBucketsForCapacity(
    mut v_capacity_2465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2466_ = leanh::lean_unsigned_to_nat(4);
    v___x_2467_ = lean_nat_mul(v_capacity_2465_, v___x_2466_);
    v___x_2468_ = leanh::lean_unsigned_to_nat(3);
    v___x_2469_ = lean_nat_div(v___x_2467_, v___x_2468_);
    leanh::lean_dec(v___x_2467_);
    return v___x_2469_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_numBucketsForCapacity___boxed(
    mut v_capacity_2470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2471_ =
        l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_numBucketsForCapacity(
            v_capacity_2470_,
        );
    leanh::lean_dec(v_capacity_2470_);
    return v_res_2471_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg(
    mut v_a_2472_: *mut leanh::LeanObject,
    mut v_a_2473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2472_) == 0 {
                    v___x_2474_ = lean_array_to_list(v_a_2473_);
                    return v___x_2474_;
                } else {
                    v_head_2475_ = leanh::lean_ctor_get(v_a_2472_, 0);
                    v_tail_2476_ = leanh::lean_ctor_get(v_a_2472_, 1);
                    v___x_2477_ = l_Std_DHashMap_Internal_AssocList_toList___redArg(v_head_2475_);
                    v___x_2478_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_2473_,
                        v___x_2477_,
                    );
                    v_a_2472_ = v_tail_2476_;
                    v_a_2473_ = v___x_2478_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg___boxed(
    mut v_a_2480_: *mut leanh::LeanObject,
    mut v_a_2481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2482_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg(v_a_2480_, v_a_2481_);
    leanh::lean_dec(v_a_2480_);
    return v_res_2482_;
}
pub unsafe fn l_Std_DHashMap_Internal_toListModel___redArg(
    mut v_buckets_2485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2486_ = lean_array_to_list(v_buckets_2485_);
    v___x_2487_ = l_Std_DHashMap_Internal_toListModel___redArg___closed__0;
    v___x_2488_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg(v___x_2486_, v___x_2487_);
    leanh::lean_dec(v___x_2486_);
    return v___x_2488_;
}
pub unsafe fn l_Std_DHashMap_Internal_toListModel(
    mut v_00_u03b1_2489_: *mut leanh::LeanObject,
    mut v_00_u03b2_2490_: *mut leanh::LeanObject,
    mut v_buckets_2491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2492_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_2491_);
    return v___x_2492_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0(
    mut v_00_u03b1_2493_: *mut leanh::LeanObject,
    mut v_00_u03b2_2494_: *mut leanh::LeanObject,
    mut v_a_2495_: *mut leanh::LeanObject,
    mut v_a_2496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2497_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg(v_a_2495_, v_a_2496_);
    return v___x_2497_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___boxed(
    mut v_00_u03b1_2498_: *mut leanh::LeanObject,
    mut v_00_u03b2_2499_: *mut leanh::LeanObject,
    mut v_a_2500_: *mut leanh::LeanObject,
    mut v_a_2501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2502_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0(v_00_u03b1_2498_, v_00_u03b2_2499_, v_a_2500_, v_a_2501_);
    leanh::lean_dec(v_a_2500_);
    return v_res_2502_;
}
pub unsafe fn l_Std_DHashMap_Internal_computeSize___redArg___lam__0(
    mut v_x1_2503_: *mut leanh::LeanObject,
    mut v_x2_2504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2505_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v_x2_2504_);
    v___x_2506_ = lean_nat_add(v_x1_2503_, v___x_2505_);
    leanh::lean_dec(v___x_2505_);
    return v___x_2506_;
}
pub unsafe fn l_Std_DHashMap_Internal_computeSize___redArg___lam__0___boxed(
    mut v_x1_2507_: *mut leanh::LeanObject,
    mut v_x2_2508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_Std_DHashMap_Internal_computeSize___redArg___lam__0(v_x1_2507_, v_x2_2508_);
    leanh::lean_dec(v_x2_2508_);
    leanh::lean_dec(v_x1_2507_);
    return v_res_2509_;
}
pub unsafe fn l_Std_DHashMap_Internal_computeSize___redArg(
    mut v_buckets_2530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: u8 = 0;
    v___x_2531_ = leanh::lean_unsigned_to_nat(0);
    v___x_2532_ = lean_array_get_size(v_buckets_2530_);
    v___x_2533_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__9;
    v___x_2534_ = lean_nat_dec_lt(v___x_2531_, v___x_2532_);
    if v___x_2534_ == 0 {
        leanh::lean_dec_ref(v_buckets_2530_);
        return v___x_2531_;
    } else {
        let mut v___f_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2536_: u8 = 0;
        v___f_2535_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__10;
        v___x_2536_ = lean_nat_dec_le(v___x_2532_, v___x_2532_);
        if v___x_2536_ == 0 {
            if v___x_2534_ == 0 {
                leanh::lean_dec_ref(v_buckets_2530_);
                return v___x_2531_;
            } else {
                let mut v___x_2537_: usize = 0;
                let mut v___x_2538_: usize = 0;
                let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2537_ = 0usize;
                v___x_2538_ = lean_usize_of_nat(v___x_2532_);
                v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2533_,
                    v___f_2535_,
                    v_buckets_2530_,
                    v___x_2537_,
                    v___x_2538_,
                    v___x_2531_,
                );
                return v___x_2539_;
            }
        } else {
            let mut v___x_2540_: usize = 0;
            let mut v___x_2541_: usize = 0;
            let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2540_ = 0usize;
            v___x_2541_ = lean_usize_of_nat(v___x_2532_);
            v___x_2542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_2533_,
                v___f_2535_,
                v_buckets_2530_,
                v___x_2540_,
                v___x_2541_,
                v___x_2531_,
            );
            return v___x_2542_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_computeSize(
    mut v_00_u03b1_2543_: *mut leanh::LeanObject,
    mut v_00_u03b2_2544_: *mut leanh::LeanObject,
    mut v_buckets_2545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: u8 = 0;
    v___x_2546_ = leanh::lean_unsigned_to_nat(0);
    v___x_2547_ = lean_array_get_size(v_buckets_2545_);
    v___x_2548_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__9;
    v___x_2549_ = lean_nat_dec_lt(v___x_2546_, v___x_2547_);
    if v___x_2549_ == 0 {
        leanh::lean_dec_ref(v_buckets_2545_);
        return v___x_2546_;
    } else {
        let mut v___f_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2551_: u8 = 0;
        v___f_2550_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__10;
        v___x_2551_ = lean_nat_dec_le(v___x_2547_, v___x_2547_);
        if v___x_2551_ == 0 {
            if v___x_2549_ == 0 {
                leanh::lean_dec_ref(v_buckets_2545_);
                return v___x_2546_;
            } else {
                let mut v___x_2552_: usize = 0;
                let mut v___x_2553_: usize = 0;
                let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2552_ = 0usize;
                v___x_2553_ = lean_usize_of_nat(v___x_2547_);
                v___x_2554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2548_,
                    v___f_2550_,
                    v_buckets_2545_,
                    v___x_2552_,
                    v___x_2553_,
                    v___x_2546_,
                );
                return v___x_2554_;
            }
        } else {
            let mut v___x_2555_: usize = 0;
            let mut v___x_2556_: usize = 0;
            let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2555_ = 0usize;
            v___x_2556_ = lean_usize_of_nat(v___x_2547_);
            v___x_2557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_2548_,
                v___f_2550_,
                v_buckets_2545_,
                v___x_2555_,
                v___x_2556_,
                v___x_2546_,
            );
            return v___x_2557_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg(
    mut v_capacity_2558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2559_ = leanh::lean_unsigned_to_nat(0);
    v___x_2560_ = leanh::lean_unsigned_to_nat(4);
    v___x_2561_ = lean_nat_mul(v_capacity_2558_, v___x_2560_);
    v___x_2562_ = leanh::lean_unsigned_to_nat(3);
    v___x_2563_ = lean_nat_div(v___x_2561_, v___x_2562_);
    leanh::lean_dec(v___x_2561_);
    v___x_2564_ = l_Nat_nextPowerOfTwo(v___x_2563_);
    leanh::lean_dec(v___x_2563_);
    v___x_2565_ = leanh::lean_box(0);
    v___x_2566_ = lean_mk_array(v___x_2564_, v___x_2565_);
    v___x_2567_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2567_, 0, v___x_2559_);
    leanh::lean_ctor_set(v___x_2567_, 1, v___x_2566_);
    return v___x_2567_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg___boxed(
    mut v_capacity_2568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2569_ = l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg(v_capacity_2568_);
    leanh::lean_dec(v_capacity_2568_);
    return v_res_2569_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity(
    mut v_00_u03b1_2570_: *mut leanh::LeanObject,
    mut v_00_u03b2_2571_: *mut leanh::LeanObject,
    mut v_capacity_2572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2573_ = leanh::lean_unsigned_to_nat(0);
    v___x_2574_ = leanh::lean_unsigned_to_nat(4);
    v___x_2575_ = lean_nat_mul(v_capacity_2572_, v___x_2574_);
    v___x_2576_ = leanh::lean_unsigned_to_nat(3);
    v___x_2577_ = lean_nat_div(v___x_2575_, v___x_2576_);
    leanh::lean_dec(v___x_2575_);
    v___x_2578_ = l_Nat_nextPowerOfTwo(v___x_2577_);
    leanh::lean_dec(v___x_2577_);
    v___x_2579_ = leanh::lean_box(0);
    v___x_2580_ = lean_mk_array(v___x_2578_, v___x_2579_);
    v___x_2581_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2581_, 0, v___x_2573_);
    leanh::lean_ctor_set(v___x_2581_, 1, v___x_2580_);
    return v___x_2581_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___boxed(
    mut v_00_u03b1_2582_: *mut leanh::LeanObject,
    mut v_00_u03b2_2583_: *mut leanh::LeanObject,
    mut v_capacity_2584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2585_ = l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity(
        v_00_u03b1_2582_,
        v_00_u03b2_2583_,
        v_capacity_2584_,
    );
    leanh::lean_dec(v_capacity_2584_);
    return v_res_2585_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_reinsertAux___redArg(
    mut v_hash_2586_: *mut leanh::LeanObject,
    mut v_data_2587_: *mut leanh::LeanObject,
    mut v_a_2588_: *mut leanh::LeanObject,
    mut v_b_2589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: u64 = 0;
    let mut v___x_2593_: u64 = 0;
    let mut v___x_2594_: u64 = 0;
    let mut v___x_2595_: u64 = 0;
    let mut v_fold_2596_: u64 = 0;
    let mut v___x_2597_: u64 = 0;
    let mut v___x_2598_: u64 = 0;
    let mut v___x_2599_: u64 = 0;
    let mut v___x_2600_: usize = 0;
    let mut v___x_2601_: usize = 0;
    let mut v___x_2602_: usize = 0;
    let mut v___x_2603_: usize = 0;
    let mut v___x_2604_: usize = 0;
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2590_ = lean_array_get_size(v_data_2587_);
    leanh::lean_inc(v_a_2588_);
    v___x_2591_ = leanh::lean_apply_1(v_hash_2586_, v_a_2588_);
    v___x_2592_ = 32u64;
    v___x_2593_ = leanh::lean_unbox_uint64(v___x_2591_);
    v___x_2594_ = lean_uint64_shift_right(v___x_2593_, v___x_2592_);
    v___x_2595_ = leanh::lean_unbox_uint64(v___x_2591_);
    leanh::lean_dec_ref(v___x_2591_);
    v_fold_2596_ = lean_uint64_xor(v___x_2595_, v___x_2594_);
    v___x_2597_ = 16u64;
    v___x_2598_ = lean_uint64_shift_right(v_fold_2596_, v___x_2597_);
    v___x_2599_ = lean_uint64_xor(v_fold_2596_, v___x_2598_);
    v___x_2600_ = lean_uint64_to_usize(v___x_2599_);
    v___x_2601_ = lean_usize_of_nat(v___x_2590_);
    v___x_2602_ = 1usize;
    v___x_2603_ = lean_usize_sub(v___x_2601_, v___x_2602_);
    v___x_2604_ = lean_usize_land(v___x_2600_, v___x_2603_);
    v___x_2605_ = lean_array_uget_borrowed(v_data_2587_, v___x_2604_);
    leanh::lean_inc(v___x_2605_);
    v___x_2606_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2606_, 0, v_a_2588_);
    leanh::lean_ctor_set(v___x_2606_, 1, v_b_2589_);
    leanh::lean_ctor_set(v___x_2606_, 2, v___x_2605_);
    v___x_2607_ = lean_array_uset(v_data_2587_, v___x_2604_, v___x_2606_);
    return v___x_2607_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_reinsertAux(
    mut v_00_u03b1_2608_: *mut leanh::LeanObject,
    mut v_00_u03b2_2609_: *mut leanh::LeanObject,
    mut v_hash_2610_: *mut leanh::LeanObject,
    mut v_data_2611_: *mut leanh::LeanObject,
    mut v_a_2612_: *mut leanh::LeanObject,
    mut v_b_2613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: u64 = 0;
    let mut v___x_2617_: u64 = 0;
    let mut v___x_2618_: u64 = 0;
    let mut v___x_2619_: u64 = 0;
    let mut v_fold_2620_: u64 = 0;
    let mut v___x_2621_: u64 = 0;
    let mut v___x_2622_: u64 = 0;
    let mut v___x_2623_: u64 = 0;
    let mut v___x_2624_: usize = 0;
    let mut v___x_2625_: usize = 0;
    let mut v___x_2626_: usize = 0;
    let mut v___x_2627_: usize = 0;
    let mut v___x_2628_: usize = 0;
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2614_ = lean_array_get_size(v_data_2611_);
    leanh::lean_inc(v_a_2612_);
    v___x_2615_ = leanh::lean_apply_1(v_hash_2610_, v_a_2612_);
    v___x_2616_ = 32u64;
    v___x_2617_ = leanh::lean_unbox_uint64(v___x_2615_);
    v___x_2618_ = lean_uint64_shift_right(v___x_2617_, v___x_2616_);
    v___x_2619_ = leanh::lean_unbox_uint64(v___x_2615_);
    leanh::lean_dec_ref(v___x_2615_);
    v_fold_2620_ = lean_uint64_xor(v___x_2619_, v___x_2618_);
    v___x_2621_ = 16u64;
    v___x_2622_ = lean_uint64_shift_right(v_fold_2620_, v___x_2621_);
    v___x_2623_ = lean_uint64_xor(v_fold_2620_, v___x_2622_);
    v___x_2624_ = lean_uint64_to_usize(v___x_2623_);
    v___x_2625_ = lean_usize_of_nat(v___x_2614_);
    v___x_2626_ = 1usize;
    v___x_2627_ = lean_usize_sub(v___x_2625_, v___x_2626_);
    v___x_2628_ = lean_usize_land(v___x_2624_, v___x_2627_);
    v___x_2629_ = lean_array_uget_borrowed(v_data_2611_, v___x_2628_);
    leanh::lean_inc(v___x_2629_);
    v___x_2630_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2630_, 0, v_a_2612_);
    leanh::lean_ctor_set(v___x_2630_, 1, v_b_2613_);
    leanh::lean_ctor_set(v___x_2630_, 2, v___x_2629_);
    v___x_2631_ = lean_array_uset(v_data_2611_, v___x_2628_, v___x_2630_);
    return v___x_2631_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg___lam__0(
    mut v_inst_2632_: *mut leanh::LeanObject,
    mut v_x1_2633_: *mut leanh::LeanObject,
    mut v_x2_2634_: *mut leanh::LeanObject,
    mut v_x3_2635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: u64 = 0;
    let mut v___x_2639_: u64 = 0;
    let mut v___x_2640_: u64 = 0;
    let mut v___x_2641_: u64 = 0;
    let mut v_fold_2642_: u64 = 0;
    let mut v___x_2643_: u64 = 0;
    let mut v___x_2644_: u64 = 0;
    let mut v___x_2645_: u64 = 0;
    let mut v___x_2646_: usize = 0;
    let mut v___x_2647_: usize = 0;
    let mut v___x_2648_: usize = 0;
    let mut v___x_2649_: usize = 0;
    let mut v___x_2650_: usize = 0;
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2636_ = lean_array_get_size(v_x1_2633_);
    leanh::lean_inc(v_x2_2634_);
    v___x_2637_ = leanh::lean_apply_1(v_inst_2632_, v_x2_2634_);
    v___x_2638_ = 32u64;
    v___x_2639_ = leanh::lean_unbox_uint64(v___x_2637_);
    v___x_2640_ = lean_uint64_shift_right(v___x_2639_, v___x_2638_);
    v___x_2641_ = leanh::lean_unbox_uint64(v___x_2637_);
    leanh::lean_dec_ref(v___x_2637_);
    v_fold_2642_ = lean_uint64_xor(v___x_2641_, v___x_2640_);
    v___x_2643_ = 16u64;
    v___x_2644_ = lean_uint64_shift_right(v_fold_2642_, v___x_2643_);
    v___x_2645_ = lean_uint64_xor(v_fold_2642_, v___x_2644_);
    v___x_2646_ = lean_uint64_to_usize(v___x_2645_);
    v___x_2647_ = lean_usize_of_nat(v___x_2636_);
    v___x_2648_ = 1usize;
    v___x_2649_ = lean_usize_sub(v___x_2647_, v___x_2648_);
    v___x_2650_ = lean_usize_land(v___x_2646_, v___x_2649_);
    v___x_2651_ = lean_array_uget_borrowed(v_x1_2633_, v___x_2650_);
    leanh::lean_inc(v___x_2651_);
    v___x_2652_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2652_, 0, v_x2_2634_);
    leanh::lean_ctor_set(v___x_2652_, 1, v_x3_2635_);
    leanh::lean_ctor_set(v___x_2652_, 2, v___x_2651_);
    v___x_2653_ = lean_array_uset(v_x1_2633_, v___x_2650_, v___x_2652_);
    return v___x_2653_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg(
    mut v_inst_2654_: *mut leanh::LeanObject,
    mut v_i_2655_: *mut leanh::LeanObject,
    mut v_source_2656_: *mut leanh::LeanObject,
    mut v_target_2657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: u8 = 0;
    let mut v___f_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_es_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2658_ = lean_array_get_size(v_source_2656_);
                v___x_2659_ = lean_nat_dec_lt(v_i_2655_, v___x_2658_);
                if v___x_2659_ == 0 {
                    leanh::lean_dec_ref(v_source_2656_);
                    leanh::lean_dec(v_i_2655_);
                    leanh::lean_dec_ref(v_inst_2654_);
                    return v_target_2657_;
                } else {
                    leanh::lean_inc_ref(v_inst_2654_);
                    v___f_2660_ = leanh::lean_alloc_closure(l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
                    leanh::lean_closure_set(v___f_2660_, 0, v_inst_2654_);
                    v_es_2661_ = lean_array_fget(v_source_2656_, v_i_2655_);
                    v___x_2662_ = leanh::lean_box(0);
                    v_source_2663_ = lean_array_fset(v_source_2656_, v_i_2655_, v___x_2662_);
                    v___x_2664_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__9;
                    v_target_2665_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
                        v___x_2664_,
                        v___f_2660_,
                        v_target_2657_,
                        v_es_2661_,
                    );
                    v___x_2666_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2667_ = lean_nat_add(v_i_2655_, v___x_2666_);
                    leanh::lean_dec(v_i_2655_);
                    v_i_2655_ = v___x_2667_;
                    v_source_2656_ = v_source_2663_;
                    v_target_2657_ = v_target_2665_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go(
    mut v_00_u03b1_2669_: *mut leanh::LeanObject,
    mut v_00_u03b2_2670_: *mut leanh::LeanObject,
    mut v_inst_2671_: *mut leanh::LeanObject,
    mut v_i_2672_: *mut leanh::LeanObject,
    mut v_source_2673_: *mut leanh::LeanObject,
    mut v_target_2674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2675_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg(v_inst_2671_, v_i_2672_, v_source_2673_, v_target_2674_);
    return v___x_2675_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
    mut v_inst_2676_: *mut leanh::LeanObject,
    mut v_data_2677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2678_ = lean_array_get_size(v_data_2677_);
    v___x_2679_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2680_ = lean_nat_mul(v___x_2678_, v___x_2679_);
    v___x_2681_ = leanh::lean_unsigned_to_nat(0);
    v___x_2682_ = leanh::lean_box(0);
    v___x_2683_ = lean_mk_array(v_nbuckets_2680_, v___x_2682_);
    v___x_2684_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg(v_inst_2676_, v___x_2681_, v_data_2677_, v___x_2683_);
    return v___x_2684_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand(
    mut v_00_u03b1_2685_: *mut leanh::LeanObject,
    mut v_00_u03b2_2686_: *mut leanh::LeanObject,
    mut v_inst_2687_: *mut leanh::LeanObject,
    mut v_data_2688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2689_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2687_, v_data_2688_);
    return v___x_2689_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary___redArg(
    mut v_inst_2690_: *mut leanh::LeanObject,
    mut v_m_2691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: u8 = 0;
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2702_: u8 = 0;
    let mut v_val_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2707_: u8 = 0;
    let mut v_unused_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2692_ = leanh::lean_ctor_get(v_m_2691_, 0);
                v_buckets_2693_ = leanh::lean_ctor_get(v_m_2691_, 1);
                v___x_2694_ = leanh::lean_unsigned_to_nat(4);
                v___x_2695_ = lean_nat_mul(v_size_2692_, v___x_2694_);
                v___x_2696_ = leanh::lean_unsigned_to_nat(3);
                v___x_2697_ = lean_nat_div(v___x_2695_, v___x_2696_);
                leanh::lean_dec(v___x_2695_);
                v___x_2698_ = lean_array_get_size(v_buckets_2693_);
                v___x_2699_ = lean_nat_dec_le(v___x_2697_, v___x_2698_);
                leanh::lean_dec(v___x_2697_);
                if v___x_2699_ == 0 {
                    leanh::lean_inc_ref(v_buckets_2693_);
                    leanh::lean_inc(v_size_2692_);
                    v_isSharedCheck_2707_ = (!leanh::lean_is_exclusive(v_m_2691_)) as u8;
                    if v_isSharedCheck_2707_ == 0 {
                        v_unused_2708_ = leanh::lean_ctor_get(v_m_2691_, 1);
                        leanh::lean_dec(v_unused_2708_);
                        v_unused_2709_ = leanh::lean_ctor_get(v_m_2691_, 0);
                        leanh::lean_dec(v_unused_2709_);
                        v___x_2701_ = v_m_2691_;
                        v_isShared_2702_ = v_isSharedCheck_2707_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2691_);
                        v___x_2701_ = leanh::lean_box(0);
                        v_isShared_2702_ = v_isSharedCheck_2707_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_2690_);
                    return v_m_2691_;
                }
            }
            1 => {
                v_val_2703_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                    v_inst_2690_,
                    v_buckets_2693_,
                );
                if v_isShared_2702_ == 0 {
                    leanh::lean_ctor_set(v___x_2701_, 1, v_val_2703_);
                    v___x_2705_ = v___x_2701_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2706_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_size_2692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_val_2703_);
                    v___x_2705_ = v_reuseFailAlloc_2706_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary(
    mut v_00_u03b1_2710_: *mut leanh::LeanObject,
    mut v_00_u03b2_2711_: *mut leanh::LeanObject,
    mut v_inst_2712_: *mut leanh::LeanObject,
    mut v_inst_2713_: *mut leanh::LeanObject,
    mut v_m_2714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: u8 = 0;
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2725_: u8 = 0;
    let mut v_val_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2730_: u8 = 0;
    let mut v_unused_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2715_ = leanh::lean_ctor_get(v_m_2714_, 0);
                v_buckets_2716_ = leanh::lean_ctor_get(v_m_2714_, 1);
                v___x_2717_ = leanh::lean_unsigned_to_nat(4);
                v___x_2718_ = lean_nat_mul(v_size_2715_, v___x_2717_);
                v___x_2719_ = leanh::lean_unsigned_to_nat(3);
                v___x_2720_ = lean_nat_div(v___x_2718_, v___x_2719_);
                leanh::lean_dec(v___x_2718_);
                v___x_2721_ = lean_array_get_size(v_buckets_2716_);
                v___x_2722_ = lean_nat_dec_le(v___x_2720_, v___x_2721_);
                leanh::lean_dec(v___x_2720_);
                if v___x_2722_ == 0 {
                    leanh::lean_inc_ref(v_buckets_2716_);
                    leanh::lean_inc(v_size_2715_);
                    v_isSharedCheck_2730_ = (!leanh::lean_is_exclusive(v_m_2714_)) as u8;
                    if v_isSharedCheck_2730_ == 0 {
                        v_unused_2731_ = leanh::lean_ctor_get(v_m_2714_, 1);
                        leanh::lean_dec(v_unused_2731_);
                        v_unused_2732_ = leanh::lean_ctor_get(v_m_2714_, 0);
                        leanh::lean_dec(v_unused_2732_);
                        v___x_2724_ = v_m_2714_;
                        v_isShared_2725_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2714_);
                        v___x_2724_ = leanh::lean_box(0);
                        v_isShared_2725_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_2713_);
                    return v_m_2714_;
                }
            }
            1 => {
                v_val_2726_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                    v_inst_2713_,
                    v_buckets_2716_,
                );
                if v_isShared_2725_ == 0 {
                    leanh::lean_ctor_set(v___x_2724_, 1, v_val_2726_);
                    v___x_2728_ = v___x_2724_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2729_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_size_2715_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_val_2726_);
                    v___x_2728_ = v_reuseFailAlloc_2729_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2728_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary___boxed(
    mut v_00_u03b1_2733_: *mut leanh::LeanObject,
    mut v_00_u03b2_2734_: *mut leanh::LeanObject,
    mut v_inst_2735_: *mut leanh::LeanObject,
    mut v_inst_2736_: *mut leanh::LeanObject,
    mut v_m_2737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2738_ = l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary(
        v_00_u03b1_2733_,
        v_00_u03b2_2734_,
        v_inst_2735_,
        v_inst_2736_,
        v_m_2737_,
    );
    leanh::lean_dec_ref(v_inst_2735_);
    return v_res_2738_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
    mut v_inst_2739_: *mut leanh::LeanObject,
    mut v_inst_2740_: *mut leanh::LeanObject,
    mut v_m_2741_: *mut leanh::LeanObject,
    mut v_a_2742_: *mut leanh::LeanObject,
    mut v_b_2743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2748_: u8 = 0;
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: u64 = 0;
    let mut v___x_2752_: u64 = 0;
    let mut v___x_2753_: u64 = 0;
    let mut v___x_2754_: u64 = 0;
    let mut v_fold_2755_: u64 = 0;
    let mut v___x_2756_: u64 = 0;
    let mut v___x_2757_: u64 = 0;
    let mut v___x_2758_: u64 = 0;
    let mut v___x_2759_: usize = 0;
    let mut v___x_2760_: usize = 0;
    let mut v___x_2761_: usize = 0;
    let mut v___x_2762_: usize = 0;
    let mut v___x_2763_: usize = 0;
    let mut v_bkt_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: u8 = 0;
    let mut v_val_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2744_ = leanh::lean_ctor_get(v_m_2741_, 0);
                v_buckets_2745_ = leanh::lean_ctor_get(v_m_2741_, 1);
                v_isSharedCheck_2790_ = (!leanh::lean_is_exclusive(v_m_2741_)) as u8;
                if v_isSharedCheck_2790_ == 0 {
                    v___x_2747_ = v_m_2741_;
                    v_isShared_2748_ = v_isSharedCheck_2790_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_2745_);
                    leanh::lean_inc(v_size_2744_);
                    leanh::lean_dec(v_m_2741_);
                    v___x_2747_ = leanh::lean_box(0);
                    v_isShared_2748_ = v_isSharedCheck_2790_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2749_ = lean_array_get_size(v_buckets_2745_);
                leanh::lean_inc_ref(v_inst_2740_);
                leanh::lean_inc_n(v_a_2742_, 2);
                v___x_2750_ = leanh::lean_apply_1(v_inst_2740_, v_a_2742_);
                v___x_2751_ = 32u64;
                v___x_2752_ = leanh::lean_unbox_uint64(v___x_2750_);
                v___x_2753_ = lean_uint64_shift_right(v___x_2752_, v___x_2751_);
                v___x_2754_ = leanh::lean_unbox_uint64(v___x_2750_);
                leanh::lean_dec_ref(v___x_2750_);
                v_fold_2755_ = lean_uint64_xor(v___x_2754_, v___x_2753_);
                v___x_2756_ = 16u64;
                v___x_2757_ = lean_uint64_shift_right(v_fold_2755_, v___x_2756_);
                v___x_2758_ = lean_uint64_xor(v_fold_2755_, v___x_2757_);
                v___x_2759_ = lean_uint64_to_usize(v___x_2758_);
                v___x_2760_ = lean_usize_of_nat(v___x_2749_);
                v___x_2761_ = 1usize;
                v___x_2762_ = lean_usize_sub(v___x_2760_, v___x_2761_);
                v___x_2763_ = lean_usize_land(v___x_2759_, v___x_2762_);
                v_bkt_2764_ = lean_array_uget_borrowed(v_buckets_2745_, v___x_2763_);
                leanh::lean_inc(v_bkt_2764_);
                leanh::lean_inc_ref(v_inst_2739_);
                v___x_2765_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2739_,
                    v_a_2742_,
                    v_bkt_2764_,
                );
                if v___x_2765_ == 0 {
                    leanh::lean_dec_ref(v_inst_2739_);
                    v___x_2766_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2767_ = lean_nat_add(v_size_2744_, v___x_2766_);
                    leanh::lean_dec(v_size_2744_);
                    leanh::lean_inc(v_bkt_2764_);
                    v___x_2768_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2768_, 0, v_a_2742_);
                    leanh::lean_ctor_set(v___x_2768_, 1, v_b_2743_);
                    leanh::lean_ctor_set(v___x_2768_, 2, v_bkt_2764_);
                    v_buckets_x27_2769_ =
                        lean_array_uset(v_buckets_2745_, v___x_2763_, v___x_2768_);
                    v___x_2770_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2771_ = lean_nat_mul(v_size_x27_2767_, v___x_2770_);
                    v___x_2772_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2773_ = lean_nat_div(v___x_2771_, v___x_2772_);
                    leanh::lean_dec(v___x_2771_);
                    v___x_2774_ = lean_array_get_size(v_buckets_x27_2769_);
                    v___x_2775_ = lean_nat_dec_le(v___x_2773_, v___x_2774_);
                    leanh::lean_dec(v___x_2773_);
                    if v___x_2775_ == 0 {
                        v_val_2776_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_inst_2740_,
                            v_buckets_x27_2769_,
                        );
                        if v_isShared_2748_ == 0 {
                            leanh::lean_ctor_set(v___x_2747_, 1, v_val_2776_);
                            leanh::lean_ctor_set(v___x_2747_, 0, v_size_x27_2767_);
                            v___x_2778_ = v___x_2747_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2779_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2779_,
                                0,
                                v_size_x27_2767_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_val_2776_);
                            v___x_2778_ = v_reuseFailAlloc_2779_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_inst_2740_);
                        if v_isShared_2748_ == 0 {
                            leanh::lean_ctor_set(v___x_2747_, 1, v_buckets_x27_2769_);
                            leanh::lean_ctor_set(v___x_2747_, 0, v_size_x27_2767_);
                            v___x_2781_ = v___x_2747_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2782_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2782_,
                                0,
                                v_size_x27_2767_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2782_,
                                1,
                                v_buckets_x27_2769_,
                            );
                            v___x_2781_ = v_reuseFailAlloc_2782_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_2764_);
                    leanh::lean_dec_ref(v_inst_2740_);
                    v___x_2783_ = leanh::lean_box(0);
                    v_buckets_x27_2784_ =
                        lean_array_uset(v_buckets_2745_, v___x_2763_, v___x_2783_);
                    v___x_2785_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_inst_2739_,
                        v_a_2742_,
                        v_b_2743_,
                        v_bkt_2764_,
                    );
                    v___x_2786_ = lean_array_uset(v_buckets_x27_2784_, v___x_2763_, v___x_2785_);
                    if v_isShared_2748_ == 0 {
                        leanh::lean_ctor_set(v___x_2747_, 1, v___x_2786_);
                        v___x_2788_ = v___x_2747_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2789_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_size_2744_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2789_, 1, v___x_2786_);
                        v___x_2788_ = v_reuseFailAlloc_2789_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2778_;
            }
            3 => {
                return v___x_2781_;
            }
            4 => {
                return v___x_2788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert(
    mut v_00_u03b1_2791_: *mut leanh::LeanObject,
    mut v_00_u03b2_2792_: *mut leanh::LeanObject,
    mut v_inst_2793_: *mut leanh::LeanObject,
    mut v_inst_2794_: *mut leanh::LeanObject,
    mut v_m_2795_: *mut leanh::LeanObject,
    mut v_a_2796_: *mut leanh::LeanObject,
    mut v_b_2797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2798_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_inst_2793_,
        v_inst_2794_,
        v_m_2795_,
        v_a_2796_,
        v_b_2797_,
    );
    return v___x_2798_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(
    mut v_inst_2799_: *mut leanh::LeanObject,
    mut v_inst_2800_: *mut leanh::LeanObject,
    mut v_m_2801_: *mut leanh::LeanObject,
    mut v_a_2802_: *mut leanh::LeanObject,
    mut v_f_2803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: u64 = 0;
    let mut v___x_2809_: u64 = 0;
    let mut v___x_2810_: u64 = 0;
    let mut v___x_2811_: u64 = 0;
    let mut v_fold_2812_: u64 = 0;
    let mut v___x_2813_: u64 = 0;
    let mut v___x_2814_: u64 = 0;
    let mut v___x_2815_: u64 = 0;
    let mut v___x_2816_: usize = 0;
    let mut v___x_2817_: usize = 0;
    let mut v___x_2818_: usize = 0;
    let mut v___x_2819_: usize = 0;
    let mut v___x_2820_: usize = 0;
    let mut v_bucket_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: u8 = 0;
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bucket_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2833_: u8 = 0;
    let mut v_unused_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2804_ = leanh::lean_ctor_get(v_m_2801_, 0);
                v_buckets_2805_ = leanh::lean_ctor_get(v_m_2801_, 1);
                v___x_2806_ = lean_array_get_size(v_buckets_2805_);
                leanh::lean_inc_n(v_a_2802_, 2);
                v___x_2807_ = leanh::lean_apply_1(v_inst_2800_, v_a_2802_);
                v___x_2808_ = 32u64;
                v___x_2809_ = leanh::lean_unbox_uint64(v___x_2807_);
                v___x_2810_ = lean_uint64_shift_right(v___x_2809_, v___x_2808_);
                v___x_2811_ = leanh::lean_unbox_uint64(v___x_2807_);
                leanh::lean_dec_ref(v___x_2807_);
                v_fold_2812_ = lean_uint64_xor(v___x_2811_, v___x_2810_);
                v___x_2813_ = 16u64;
                v___x_2814_ = lean_uint64_shift_right(v_fold_2812_, v___x_2813_);
                v___x_2815_ = lean_uint64_xor(v_fold_2812_, v___x_2814_);
                v___x_2816_ = lean_uint64_to_usize(v___x_2815_);
                v___x_2817_ = lean_usize_of_nat(v___x_2806_);
                v___x_2818_ = 1usize;
                v___x_2819_ = lean_usize_sub(v___x_2817_, v___x_2818_);
                v___x_2820_ = lean_usize_land(v___x_2816_, v___x_2819_);
                v_bucket_2821_ = lean_array_uget_borrowed(v_buckets_2805_, v___x_2820_);
                leanh::lean_inc(v_bucket_2821_);
                leanh::lean_inc_ref(v_inst_2799_);
                v___x_2822_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2799_,
                    v_a_2802_,
                    v_bucket_2821_,
                );
                if v___x_2822_ == 0 {
                    leanh::lean_dec(v_f_2803_);
                    leanh::lean_dec(v_a_2802_);
                    leanh::lean_dec_ref(v_inst_2799_);
                    return v_m_2801_;
                } else {
                    leanh::lean_inc(v_bucket_2821_);
                    leanh::lean_inc_ref(v_buckets_2805_);
                    leanh::lean_inc(v_size_2804_);
                    v_isSharedCheck_2833_ = (!leanh::lean_is_exclusive(v_m_2801_)) as u8;
                    if v_isSharedCheck_2833_ == 0 {
                        v_unused_2834_ = leanh::lean_ctor_get(v_m_2801_, 1);
                        leanh::lean_dec(v_unused_2834_);
                        v_unused_2835_ = leanh::lean_ctor_get(v_m_2801_, 0);
                        leanh::lean_dec(v_unused_2835_);
                        v___x_2824_ = v_m_2801_;
                        v_isShared_2825_ = v_isSharedCheck_2833_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2801_);
                        v___x_2824_ = leanh::lean_box(0);
                        v_isShared_2825_ = v_isSharedCheck_2833_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2826_ = leanh::lean_box(0);
                v_buckets_2827_ = lean_array_uset(v_buckets_2805_, v___x_2820_, v___x_2826_);
                v_bucket_2828_ = l_Std_DHashMap_Internal_AssocList_modify___redArg(
                    v_inst_2799_,
                    v_a_2802_,
                    v_f_2803_,
                    v_bucket_2821_,
                );
                v___x_2829_ = lean_array_uset(v_buckets_2827_, v___x_2820_, v_bucket_2828_);
                if v_isShared_2825_ == 0 {
                    leanh::lean_ctor_set(v___x_2824_, 1, v___x_2829_);
                    v___x_2831_ = v___x_2824_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2832_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_size_2804_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 1, v___x_2829_);
                    v___x_2831_ = v_reuseFailAlloc_2832_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2831_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_modify(
    mut v_00_u03b1_2836_: *mut leanh::LeanObject,
    mut v_00_u03b2_2837_: *mut leanh::LeanObject,
    mut v_inst_2838_: *mut leanh::LeanObject,
    mut v_inst_2839_: *mut leanh::LeanObject,
    mut v_inst_2840_: *mut leanh::LeanObject,
    mut v_m_2841_: *mut leanh::LeanObject,
    mut v_a_2842_: *mut leanh::LeanObject,
    mut v_f_2843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2844_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(
        v_inst_2838_,
        v_inst_2839_,
        v_m_2841_,
        v_a_2842_,
        v_f_2843_,
    );
    return v___x_2844_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
    mut v_inst_2845_: *mut leanh::LeanObject,
    mut v_inst_2846_: *mut leanh::LeanObject,
    mut v_m_2847_: *mut leanh::LeanObject,
    mut v_a_2848_: *mut leanh::LeanObject,
    mut v_f_2849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: u64 = 0;
    let mut v___x_2855_: u64 = 0;
    let mut v___x_2856_: u64 = 0;
    let mut v___x_2857_: u64 = 0;
    let mut v_fold_2858_: u64 = 0;
    let mut v___x_2859_: u64 = 0;
    let mut v___x_2860_: u64 = 0;
    let mut v___x_2861_: u64 = 0;
    let mut v___x_2862_: usize = 0;
    let mut v___x_2863_: usize = 0;
    let mut v___x_2864_: usize = 0;
    let mut v___x_2865_: usize = 0;
    let mut v___x_2866_: usize = 0;
    let mut v_bucket_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: u8 = 0;
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2871_: u8 = 0;
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bucket_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2879_: u8 = 0;
    let mut v_unused_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2850_ = leanh::lean_ctor_get(v_m_2847_, 0);
                v_buckets_2851_ = leanh::lean_ctor_get(v_m_2847_, 1);
                v___x_2852_ = lean_array_get_size(v_buckets_2851_);
                leanh::lean_inc_n(v_a_2848_, 2);
                v___x_2853_ = leanh::lean_apply_1(v_inst_2846_, v_a_2848_);
                v___x_2854_ = 32u64;
                v___x_2855_ = leanh::lean_unbox_uint64(v___x_2853_);
                v___x_2856_ = lean_uint64_shift_right(v___x_2855_, v___x_2854_);
                v___x_2857_ = leanh::lean_unbox_uint64(v___x_2853_);
                leanh::lean_dec_ref(v___x_2853_);
                v_fold_2858_ = lean_uint64_xor(v___x_2857_, v___x_2856_);
                v___x_2859_ = 16u64;
                v___x_2860_ = lean_uint64_shift_right(v_fold_2858_, v___x_2859_);
                v___x_2861_ = lean_uint64_xor(v_fold_2858_, v___x_2860_);
                v___x_2862_ = lean_uint64_to_usize(v___x_2861_);
                v___x_2863_ = lean_usize_of_nat(v___x_2852_);
                v___x_2864_ = 1usize;
                v___x_2865_ = lean_usize_sub(v___x_2863_, v___x_2864_);
                v___x_2866_ = lean_usize_land(v___x_2862_, v___x_2865_);
                v_bucket_2867_ = lean_array_uget_borrowed(v_buckets_2851_, v___x_2866_);
                leanh::lean_inc(v_bucket_2867_);
                leanh::lean_inc_ref(v_inst_2845_);
                v___x_2868_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2845_,
                    v_a_2848_,
                    v_bucket_2867_,
                );
                if v___x_2868_ == 0 {
                    leanh::lean_dec(v_f_2849_);
                    leanh::lean_dec(v_a_2848_);
                    leanh::lean_dec_ref(v_inst_2845_);
                    return v_m_2847_;
                } else {
                    leanh::lean_inc(v_bucket_2867_);
                    leanh::lean_inc_ref(v_buckets_2851_);
                    leanh::lean_inc(v_size_2850_);
                    v_isSharedCheck_2879_ = (!leanh::lean_is_exclusive(v_m_2847_)) as u8;
                    if v_isSharedCheck_2879_ == 0 {
                        v_unused_2880_ = leanh::lean_ctor_get(v_m_2847_, 1);
                        leanh::lean_dec(v_unused_2880_);
                        v_unused_2881_ = leanh::lean_ctor_get(v_m_2847_, 0);
                        leanh::lean_dec(v_unused_2881_);
                        v___x_2870_ = v_m_2847_;
                        v_isShared_2871_ = v_isSharedCheck_2879_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2847_);
                        v___x_2870_ = leanh::lean_box(0);
                        v_isShared_2871_ = v_isSharedCheck_2879_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2872_ = leanh::lean_box(0);
                v_buckets_2873_ = lean_array_uset(v_buckets_2851_, v___x_2866_, v___x_2872_);
                v_bucket_2874_ = l_Std_DHashMap_Internal_AssocList_Const_modify___redArg(
                    v_inst_2845_,
                    v_a_2848_,
                    v_f_2849_,
                    v_bucket_2867_,
                );
                v___x_2875_ = lean_array_uset(v_buckets_2873_, v___x_2866_, v_bucket_2874_);
                if v_isShared_2871_ == 0 {
                    leanh::lean_ctor_set(v___x_2870_, 1, v___x_2875_);
                    v___x_2877_ = v___x_2870_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2878_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_size_2850_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2878_, 1, v___x_2875_);
                    v___x_2877_ = v_reuseFailAlloc_2878_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2877_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_modify(
    mut v_00_u03b1_2882_: *mut leanh::LeanObject,
    mut v_inst_2883_: *mut leanh::LeanObject,
    mut v_00_u03b2_2884_: *mut leanh::LeanObject,
    mut v_inst_2885_: *mut leanh::LeanObject,
    mut v_m_2886_: *mut leanh::LeanObject,
    mut v_a_2887_: *mut leanh::LeanObject,
    mut v_f_2888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2889_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(
        v_inst_2883_,
        v_inst_2885_,
        v_m_2886_,
        v_a_2887_,
        v_f_2888_,
    );
    return v___x_2889_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(
    mut v_inst_2890_: *mut leanh::LeanObject,
    mut v_inst_2891_: *mut leanh::LeanObject,
    mut v_m_2892_: *mut leanh::LeanObject,
    mut v_a_2893_: *mut leanh::LeanObject,
    mut v_f_2894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: u64 = 0;
    let mut v___x_2900_: u64 = 0;
    let mut v___x_2901_: u64 = 0;
    let mut v___x_2902_: u64 = 0;
    let mut v_fold_2903_: u64 = 0;
    let mut v___x_2904_: u64 = 0;
    let mut v___x_2905_: u64 = 0;
    let mut v___x_2906_: u64 = 0;
    let mut v___x_2907_: usize = 0;
    let mut v___x_2908_: usize = 0;
    let mut v___x_2909_: usize = 0;
    let mut v___x_2910_: usize = 0;
    let mut v___x_2911_: usize = 0;
    let mut v_bkt_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: u8 = 0;
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2918_: u8 = 0;
    let mut v_val_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: u8 = 0;
    let mut v_val_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2937_: u8 = 0;
    let mut v_unused_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2942_: u8 = 0;
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: u8 = 0;
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2955_: u8 = 0;
    let mut v_unused_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2895_ = leanh::lean_ctor_get(v_m_2892_, 0);
                v_buckets_2896_ = leanh::lean_ctor_get(v_m_2892_, 1);
                v___x_2897_ = lean_array_get_size(v_buckets_2896_);
                leanh::lean_inc_ref(v_inst_2891_);
                leanh::lean_inc_n(v_a_2893_, 2);
                v___x_2898_ = leanh::lean_apply_1(v_inst_2891_, v_a_2893_);
                v___x_2899_ = 32u64;
                v___x_2900_ = leanh::lean_unbox_uint64(v___x_2898_);
                v___x_2901_ = lean_uint64_shift_right(v___x_2900_, v___x_2899_);
                v___x_2902_ = leanh::lean_unbox_uint64(v___x_2898_);
                leanh::lean_dec_ref(v___x_2898_);
                v_fold_2903_ = lean_uint64_xor(v___x_2902_, v___x_2901_);
                v___x_2904_ = 16u64;
                v___x_2905_ = lean_uint64_shift_right(v_fold_2903_, v___x_2904_);
                v___x_2906_ = lean_uint64_xor(v_fold_2903_, v___x_2905_);
                v___x_2907_ = lean_uint64_to_usize(v___x_2906_);
                v___x_2908_ = lean_usize_of_nat(v___x_2897_);
                v___x_2909_ = 1usize;
                v___x_2910_ = lean_usize_sub(v___x_2908_, v___x_2909_);
                v___x_2911_ = lean_usize_land(v___x_2907_, v___x_2910_);
                v_bkt_2912_ = lean_array_uget_borrowed(v_buckets_2896_, v___x_2911_);
                leanh::lean_inc(v_bkt_2912_);
                leanh::lean_inc_ref(v_inst_2890_);
                v___x_2913_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2890_,
                    v_a_2893_,
                    v_bkt_2912_,
                );
                if v___x_2913_ == 0 {
                    leanh::lean_dec_ref(v_inst_2890_);
                    v___x_2914_ = leanh::lean_box(0);
                    v___x_2915_ = leanh::lean_apply_1(v_f_2894_, v___x_2914_);
                    if leanh::lean_obj_tag(v___x_2915_) == 0 {
                        leanh::lean_dec(v_a_2893_);
                        leanh::lean_dec_ref(v_inst_2891_);
                        return v_m_2892_;
                    } else {
                        leanh::lean_inc_ref(v_buckets_2896_);
                        leanh::lean_inc(v_size_2895_);
                        v_isSharedCheck_2937_ = (!leanh::lean_is_exclusive(v_m_2892_)) as u8;
                        if v_isSharedCheck_2937_ == 0 {
                            v_unused_2938_ = leanh::lean_ctor_get(v_m_2892_, 1);
                            leanh::lean_dec(v_unused_2938_);
                            v_unused_2939_ = leanh::lean_ctor_get(v_m_2892_, 0);
                            leanh::lean_dec(v_unused_2939_);
                            v___x_2917_ = v_m_2892_;
                            v_isShared_2918_ = v_isSharedCheck_2937_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_m_2892_);
                            v___x_2917_ = leanh::lean_box(0);
                            v_isShared_2918_ = v_isSharedCheck_2937_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_2912_);
                    leanh::lean_inc_ref(v_buckets_2896_);
                    leanh::lean_inc(v_size_2895_);
                    leanh::lean_dec_ref(v_inst_2891_);
                    v_isSharedCheck_2955_ = (!leanh::lean_is_exclusive(v_m_2892_)) as u8;
                    if v_isSharedCheck_2955_ == 0 {
                        v_unused_2956_ = leanh::lean_ctor_get(v_m_2892_, 1);
                        leanh::lean_dec(v_unused_2956_);
                        v_unused_2957_ = leanh::lean_ctor_get(v_m_2892_, 0);
                        leanh::lean_dec(v_unused_2957_);
                        v___x_2941_ = v_m_2892_;
                        v_isShared_2942_ = v_isSharedCheck_2955_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2892_);
                        v___x_2941_ = leanh::lean_box(0);
                        v_isShared_2942_ = v_isSharedCheck_2955_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_val_2919_ = leanh::lean_ctor_get(v___x_2915_, 0);
                leanh::lean_inc(v_val_2919_);
                leanh::lean_dec_ref_known(v___x_2915_, 1);
                v___x_2920_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2921_ = lean_nat_add(v_size_2895_, v___x_2920_);
                leanh::lean_dec(v_size_2895_);
                leanh::lean_inc(v_bkt_2912_);
                v___x_2922_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2922_, 0, v_a_2893_);
                leanh::lean_ctor_set(v___x_2922_, 1, v_val_2919_);
                leanh::lean_ctor_set(v___x_2922_, 2, v_bkt_2912_);
                v_buckets_x27_2923_ = lean_array_uset(v_buckets_2896_, v___x_2911_, v___x_2922_);
                v___x_2924_ = leanh::lean_unsigned_to_nat(4);
                v___x_2925_ = lean_nat_mul(v_size_x27_2921_, v___x_2924_);
                v___x_2926_ = leanh::lean_unsigned_to_nat(3);
                v___x_2927_ = lean_nat_div(v___x_2925_, v___x_2926_);
                leanh::lean_dec(v___x_2925_);
                v___x_2928_ = lean_array_get_size(v_buckets_x27_2923_);
                v___x_2929_ = lean_nat_dec_le(v___x_2927_, v___x_2928_);
                leanh::lean_dec(v___x_2927_);
                if v___x_2929_ == 0 {
                    v_val_2930_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_2891_,
                        v_buckets_x27_2923_,
                    );
                    if v_isShared_2918_ == 0 {
                        leanh::lean_ctor_set(v___x_2917_, 1, v_val_2930_);
                        leanh::lean_ctor_set(v___x_2917_, 0, v_size_x27_2921_);
                        v___x_2932_ = v___x_2917_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2933_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_size_x27_2921_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_val_2930_);
                        v___x_2932_ = v_reuseFailAlloc_2933_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_2891_);
                    if v_isShared_2918_ == 0 {
                        leanh::lean_ctor_set(v___x_2917_, 1, v_buckets_x27_2923_);
                        leanh::lean_ctor_set(v___x_2917_, 0, v_size_x27_2921_);
                        v___x_2935_ = v___x_2917_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2936_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_size_x27_2921_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_buckets_x27_2923_);
                        v___x_2935_ = v_reuseFailAlloc_2936_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2932_;
            }
            3 => {
                return v___x_2935_;
            }
            4 => {
                v___x_2943_ = leanh::lean_box(0);
                v_buckets_x27_2944_ = lean_array_uset(v_buckets_2896_, v___x_2911_, v___x_2943_);
                leanh::lean_inc(v_a_2893_);
                leanh::lean_inc_ref(v_inst_2890_);
                v_bkt_x27_2945_ = l_Std_DHashMap_Internal_AssocList_alter___redArg(
                    v_inst_2890_,
                    v_a_2893_,
                    v_f_2894_,
                    v_bkt_2912_,
                );
                leanh::lean_inc(v_bkt_x27_2945_);
                v___x_2952_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2890_,
                    v_a_2893_,
                    v_bkt_x27_2945_,
                );
                if v___x_2952_ == 0 {
                    v___x_2953_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2954_ = lean_nat_sub(v_size_2895_, v___x_2953_);
                    leanh::lean_dec(v_size_2895_);
                    v___y_2947_ = v___x_2954_;
                    state = 5;
                    continue;
                } else {
                    v___y_2947_ = v_size_2895_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2948_ = lean_array_uset(v_buckets_x27_2944_, v___x_2911_, v_bkt_x27_2945_);
                if v_isShared_2942_ == 0 {
                    leanh::lean_ctor_set(v___x_2941_, 1, v___x_2948_);
                    leanh::lean_ctor_set(v___x_2941_, 0, v___y_2947_);
                    v___x_2950_ = v___x_2941_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2951_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___y_2947_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 1, v___x_2948_);
                    v___x_2950_ = v_reuseFailAlloc_2951_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_alter(
    mut v_00_u03b1_2958_: *mut leanh::LeanObject,
    mut v_00_u03b2_2959_: *mut leanh::LeanObject,
    mut v_inst_2960_: *mut leanh::LeanObject,
    mut v_inst_2961_: *mut leanh::LeanObject,
    mut v_inst_2962_: *mut leanh::LeanObject,
    mut v_m_2963_: *mut leanh::LeanObject,
    mut v_a_2964_: *mut leanh::LeanObject,
    mut v_f_2965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2966_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(
        v_inst_2960_,
        v_inst_2961_,
        v_m_2963_,
        v_a_2964_,
        v_f_2965_,
    );
    return v___x_2966_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
    mut v_inst_2967_: *mut leanh::LeanObject,
    mut v_inst_2968_: *mut leanh::LeanObject,
    mut v_m_2969_: *mut leanh::LeanObject,
    mut v_a_2970_: *mut leanh::LeanObject,
    mut v_f_2971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: u64 = 0;
    let mut v___x_2977_: u64 = 0;
    let mut v___x_2978_: u64 = 0;
    let mut v___x_2979_: u64 = 0;
    let mut v_fold_2980_: u64 = 0;
    let mut v___x_2981_: u64 = 0;
    let mut v___x_2982_: u64 = 0;
    let mut v___x_2983_: u64 = 0;
    let mut v___x_2984_: usize = 0;
    let mut v___x_2985_: usize = 0;
    let mut v___x_2986_: usize = 0;
    let mut v___x_2987_: usize = 0;
    let mut v___x_2988_: usize = 0;
    let mut v_bkt_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: u8 = 0;
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2995_: u8 = 0;
    let mut v_val_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: u8 = 0;
    let mut v_val_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut v_unused_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3019_: u8 = 0;
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: u8 = 0;
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3032_: u8 = 0;
    let mut v_unused_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2972_ = leanh::lean_ctor_get(v_m_2969_, 0);
                v_buckets_2973_ = leanh::lean_ctor_get(v_m_2969_, 1);
                v___x_2974_ = lean_array_get_size(v_buckets_2973_);
                leanh::lean_inc_ref(v_inst_2968_);
                leanh::lean_inc_n(v_a_2970_, 2);
                v___x_2975_ = leanh::lean_apply_1(v_inst_2968_, v_a_2970_);
                v___x_2976_ = 32u64;
                v___x_2977_ = leanh::lean_unbox_uint64(v___x_2975_);
                v___x_2978_ = lean_uint64_shift_right(v___x_2977_, v___x_2976_);
                v___x_2979_ = leanh::lean_unbox_uint64(v___x_2975_);
                leanh::lean_dec_ref(v___x_2975_);
                v_fold_2980_ = lean_uint64_xor(v___x_2979_, v___x_2978_);
                v___x_2981_ = 16u64;
                v___x_2982_ = lean_uint64_shift_right(v_fold_2980_, v___x_2981_);
                v___x_2983_ = lean_uint64_xor(v_fold_2980_, v___x_2982_);
                v___x_2984_ = lean_uint64_to_usize(v___x_2983_);
                v___x_2985_ = lean_usize_of_nat(v___x_2974_);
                v___x_2986_ = 1usize;
                v___x_2987_ = lean_usize_sub(v___x_2985_, v___x_2986_);
                v___x_2988_ = lean_usize_land(v___x_2984_, v___x_2987_);
                v_bkt_2989_ = lean_array_uget_borrowed(v_buckets_2973_, v___x_2988_);
                leanh::lean_inc(v_bkt_2989_);
                leanh::lean_inc_ref(v_inst_2967_);
                v___x_2990_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2967_,
                    v_a_2970_,
                    v_bkt_2989_,
                );
                if v___x_2990_ == 0 {
                    leanh::lean_dec_ref(v_inst_2967_);
                    v___x_2991_ = leanh::lean_box(0);
                    v___x_2992_ = leanh::lean_apply_1(v_f_2971_, v___x_2991_);
                    if leanh::lean_obj_tag(v___x_2992_) == 0 {
                        leanh::lean_dec(v_a_2970_);
                        leanh::lean_dec_ref(v_inst_2968_);
                        return v_m_2969_;
                    } else {
                        leanh::lean_inc_ref(v_buckets_2973_);
                        leanh::lean_inc(v_size_2972_);
                        v_isSharedCheck_3014_ = (!leanh::lean_is_exclusive(v_m_2969_)) as u8;
                        if v_isSharedCheck_3014_ == 0 {
                            v_unused_3015_ = leanh::lean_ctor_get(v_m_2969_, 1);
                            leanh::lean_dec(v_unused_3015_);
                            v_unused_3016_ = leanh::lean_ctor_get(v_m_2969_, 0);
                            leanh::lean_dec(v_unused_3016_);
                            v___x_2994_ = v_m_2969_;
                            v_isShared_2995_ = v_isSharedCheck_3014_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_m_2969_);
                            v___x_2994_ = leanh::lean_box(0);
                            v_isShared_2995_ = v_isSharedCheck_3014_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_2989_);
                    leanh::lean_inc_ref(v_buckets_2973_);
                    leanh::lean_inc(v_size_2972_);
                    leanh::lean_dec_ref(v_inst_2968_);
                    v_isSharedCheck_3032_ = (!leanh::lean_is_exclusive(v_m_2969_)) as u8;
                    if v_isSharedCheck_3032_ == 0 {
                        v_unused_3033_ = leanh::lean_ctor_get(v_m_2969_, 1);
                        leanh::lean_dec(v_unused_3033_);
                        v_unused_3034_ = leanh::lean_ctor_get(v_m_2969_, 0);
                        leanh::lean_dec(v_unused_3034_);
                        v___x_3018_ = v_m_2969_;
                        v_isShared_3019_ = v_isSharedCheck_3032_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2969_);
                        v___x_3018_ = leanh::lean_box(0);
                        v_isShared_3019_ = v_isSharedCheck_3032_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_val_2996_ = leanh::lean_ctor_get(v___x_2992_, 0);
                leanh::lean_inc(v_val_2996_);
                leanh::lean_dec_ref_known(v___x_2992_, 1);
                v___x_2997_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2998_ = lean_nat_add(v_size_2972_, v___x_2997_);
                leanh::lean_dec(v_size_2972_);
                leanh::lean_inc(v_bkt_2989_);
                v___x_2999_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2999_, 0, v_a_2970_);
                leanh::lean_ctor_set(v___x_2999_, 1, v_val_2996_);
                leanh::lean_ctor_set(v___x_2999_, 2, v_bkt_2989_);
                v_buckets_x27_3000_ = lean_array_uset(v_buckets_2973_, v___x_2988_, v___x_2999_);
                v___x_3001_ = leanh::lean_unsigned_to_nat(4);
                v___x_3002_ = lean_nat_mul(v_size_x27_2998_, v___x_3001_);
                v___x_3003_ = leanh::lean_unsigned_to_nat(3);
                v___x_3004_ = lean_nat_div(v___x_3002_, v___x_3003_);
                leanh::lean_dec(v___x_3002_);
                v___x_3005_ = lean_array_get_size(v_buckets_x27_3000_);
                v___x_3006_ = lean_nat_dec_le(v___x_3004_, v___x_3005_);
                leanh::lean_dec(v___x_3004_);
                if v___x_3006_ == 0 {
                    v_val_3007_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_2968_,
                        v_buckets_x27_3000_,
                    );
                    if v_isShared_2995_ == 0 {
                        leanh::lean_ctor_set(v___x_2994_, 1, v_val_3007_);
                        leanh::lean_ctor_set(v___x_2994_, 0, v_size_x27_2998_);
                        v___x_3009_ = v___x_2994_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3010_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_size_x27_2998_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_val_3007_);
                        v___x_3009_ = v_reuseFailAlloc_3010_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_2968_);
                    if v_isShared_2995_ == 0 {
                        leanh::lean_ctor_set(v___x_2994_, 1, v_buckets_x27_3000_);
                        leanh::lean_ctor_set(v___x_2994_, 0, v_size_x27_2998_);
                        v___x_3012_ = v___x_2994_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3013_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_size_x27_2998_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_buckets_x27_3000_);
                        v___x_3012_ = v_reuseFailAlloc_3013_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3009_;
            }
            3 => {
                return v___x_3012_;
            }
            4 => {
                v___x_3020_ = leanh::lean_box(0);
                v_buckets_x27_3021_ = lean_array_uset(v_buckets_2973_, v___x_2988_, v___x_3020_);
                leanh::lean_inc(v_a_2970_);
                leanh::lean_inc_ref(v_inst_2967_);
                v_bkt_x27_3022_ = l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(
                    v_inst_2967_,
                    v_a_2970_,
                    v_f_2971_,
                    v_bkt_2989_,
                );
                leanh::lean_inc(v_bkt_x27_3022_);
                v___x_3029_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_2967_,
                    v_a_2970_,
                    v_bkt_x27_3022_,
                );
                if v___x_3029_ == 0 {
                    v___x_3030_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3031_ = lean_nat_sub(v_size_2972_, v___x_3030_);
                    leanh::lean_dec(v_size_2972_);
                    v___y_3024_ = v___x_3031_;
                    state = 5;
                    continue;
                } else {
                    v___y_3024_ = v_size_2972_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3025_ = lean_array_uset(v_buckets_x27_3021_, v___x_2988_, v_bkt_x27_3022_);
                if v_isShared_3019_ == 0 {
                    leanh::lean_ctor_set(v___x_3018_, 1, v___x_3025_);
                    leanh::lean_ctor_set(v___x_3018_, 0, v___y_3024_);
                    v___x_3027_ = v___x_3018_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3028_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___y_3024_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3028_, 1, v___x_3025_);
                    v___x_3027_ = v_reuseFailAlloc_3028_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3027_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter(
    mut v_00_u03b1_3035_: *mut leanh::LeanObject,
    mut v_inst_3036_: *mut leanh::LeanObject,
    mut v_inst_3037_: *mut leanh::LeanObject,
    mut v_00_u03b2_3038_: *mut leanh::LeanObject,
    mut v_m_3039_: *mut leanh::LeanObject,
    mut v_a_3040_: *mut leanh::LeanObject,
    mut v_f_3041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3042_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v_inst_3036_,
        v_inst_3037_,
        v_m_3039_,
        v_a_3040_,
        v_f_3041_,
    );
    return v___x_3042_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_containsThenInsert___redArg(
    mut v_inst_3043_: *mut leanh::LeanObject,
    mut v_inst_3044_: *mut leanh::LeanObject,
    mut v_m_3045_: *mut leanh::LeanObject,
    mut v_a_3046_: *mut leanh::LeanObject,
    mut v_b_3047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3052_: u8 = 0;
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: u64 = 0;
    let mut v___x_3056_: u64 = 0;
    let mut v___x_3057_: u64 = 0;
    let mut v___x_3058_: u64 = 0;
    let mut v_fold_3059_: u64 = 0;
    let mut v___x_3060_: u64 = 0;
    let mut v___x_3061_: u64 = 0;
    let mut v___x_3062_: u64 = 0;
    let mut v___x_3063_: usize = 0;
    let mut v___x_3064_: usize = 0;
    let mut v___x_3065_: usize = 0;
    let mut v___x_3066_: usize = 0;
    let mut v___x_3067_: usize = 0;
    let mut v_bkt_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: u8 = 0;
    let mut v_val_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3100_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3048_ = leanh::lean_ctor_get(v_m_3045_, 0);
                v_buckets_3049_ = leanh::lean_ctor_get(v_m_3045_, 1);
                v_isSharedCheck_3100_ = (!leanh::lean_is_exclusive(v_m_3045_)) as u8;
                if v_isSharedCheck_3100_ == 0 {
                    v___x_3051_ = v_m_3045_;
                    v_isShared_3052_ = v_isSharedCheck_3100_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3049_);
                    leanh::lean_inc(v_size_3048_);
                    leanh::lean_dec(v_m_3045_);
                    v___x_3051_ = leanh::lean_box(0);
                    v_isShared_3052_ = v_isSharedCheck_3100_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3053_ = lean_array_get_size(v_buckets_3049_);
                leanh::lean_inc_ref(v_inst_3044_);
                leanh::lean_inc_n(v_a_3046_, 2);
                v___x_3054_ = leanh::lean_apply_1(v_inst_3044_, v_a_3046_);
                v___x_3055_ = 32u64;
                v___x_3056_ = leanh::lean_unbox_uint64(v___x_3054_);
                v___x_3057_ = lean_uint64_shift_right(v___x_3056_, v___x_3055_);
                v___x_3058_ = leanh::lean_unbox_uint64(v___x_3054_);
                leanh::lean_dec_ref(v___x_3054_);
                v_fold_3059_ = lean_uint64_xor(v___x_3058_, v___x_3057_);
                v___x_3060_ = 16u64;
                v___x_3061_ = lean_uint64_shift_right(v_fold_3059_, v___x_3060_);
                v___x_3062_ = lean_uint64_xor(v_fold_3059_, v___x_3061_);
                v___x_3063_ = lean_uint64_to_usize(v___x_3062_);
                v___x_3064_ = lean_usize_of_nat(v___x_3053_);
                v___x_3065_ = 1usize;
                v___x_3066_ = lean_usize_sub(v___x_3064_, v___x_3065_);
                v___x_3067_ = lean_usize_land(v___x_3063_, v___x_3066_);
                v_bkt_3068_ = lean_array_uget_borrowed(v_buckets_3049_, v___x_3067_);
                leanh::lean_inc(v_bkt_3068_);
                leanh::lean_inc_ref(v_inst_3043_);
                v___x_3069_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_3043_,
                    v_a_3046_,
                    v_bkt_3068_,
                );
                if v___x_3069_ == 0 {
                    leanh::lean_dec_ref(v_inst_3043_);
                    v___x_3070_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3071_ = lean_nat_add(v_size_3048_, v___x_3070_);
                    leanh::lean_dec(v_size_3048_);
                    leanh::lean_inc(v_bkt_3068_);
                    v___x_3072_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3072_, 0, v_a_3046_);
                    leanh::lean_ctor_set(v___x_3072_, 1, v_b_3047_);
                    leanh::lean_ctor_set(v___x_3072_, 2, v_bkt_3068_);
                    v_buckets_x27_3073_ =
                        lean_array_uset(v_buckets_3049_, v___x_3067_, v___x_3072_);
                    v___x_3074_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3075_ = lean_nat_mul(v_size_x27_3071_, v___x_3074_);
                    v___x_3076_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3077_ = lean_nat_div(v___x_3075_, v___x_3076_);
                    leanh::lean_dec(v___x_3075_);
                    v___x_3078_ = lean_array_get_size(v_buckets_x27_3073_);
                    v___x_3079_ = lean_nat_dec_le(v___x_3077_, v___x_3078_);
                    leanh::lean_dec(v___x_3077_);
                    if v___x_3079_ == 0 {
                        v_val_3080_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_inst_3044_,
                            v_buckets_x27_3073_,
                        );
                        if v_isShared_3052_ == 0 {
                            leanh::lean_ctor_set(v___x_3051_, 1, v_val_3080_);
                            leanh::lean_ctor_set(v___x_3051_, 0, v_size_x27_3071_);
                            v___x_3082_ = v___x_3051_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3085_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3085_,
                                0,
                                v_size_x27_3071_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_val_3080_);
                            v___x_3082_ = v_reuseFailAlloc_3085_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_inst_3044_);
                        if v_isShared_3052_ == 0 {
                            leanh::lean_ctor_set(v___x_3051_, 1, v_buckets_x27_3073_);
                            leanh::lean_ctor_set(v___x_3051_, 0, v_size_x27_3071_);
                            v___x_3087_ = v___x_3051_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3090_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3090_,
                                0,
                                v_size_x27_3071_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3090_,
                                1,
                                v_buckets_x27_3073_,
                            );
                            v___x_3087_ = v_reuseFailAlloc_3090_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_3068_);
                    leanh::lean_dec_ref(v_inst_3044_);
                    v___x_3091_ = leanh::lean_box(0);
                    v_buckets_x27_3092_ =
                        lean_array_uset(v_buckets_3049_, v___x_3067_, v___x_3091_);
                    v___x_3093_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_inst_3043_,
                        v_a_3046_,
                        v_b_3047_,
                        v_bkt_3068_,
                    );
                    v___x_3094_ = lean_array_uset(v_buckets_x27_3092_, v___x_3067_, v___x_3093_);
                    if v_isShared_3052_ == 0 {
                        leanh::lean_ctor_set(v___x_3051_, 1, v___x_3094_);
                        v___x_3096_ = v___x_3051_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3099_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_size_3048_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 1, v___x_3094_);
                        v___x_3096_ = v_reuseFailAlloc_3099_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3083_ = leanh::lean_box((v___x_3069_) as usize);
                v___x_3084_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3084_, 0, v___x_3083_);
                leanh::lean_ctor_set(v___x_3084_, 1, v___x_3082_);
                return v___x_3084_;
            }
            3 => {
                v___x_3088_ = leanh::lean_box((v___x_3069_) as usize);
                v___x_3089_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3089_, 0, v___x_3088_);
                leanh::lean_ctor_set(v___x_3089_, 1, v___x_3087_);
                return v___x_3089_;
            }
            4 => {
                v___x_3097_ = leanh::lean_box((v___x_3069_) as usize);
                v___x_3098_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3098_, 0, v___x_3097_);
                leanh::lean_ctor_set(v___x_3098_, 1, v___x_3096_);
                return v___x_3098_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_containsThenInsert(
    mut v_00_u03b1_3101_: *mut leanh::LeanObject,
    mut v_00_u03b2_3102_: *mut leanh::LeanObject,
    mut v_inst_3103_: *mut leanh::LeanObject,
    mut v_inst_3104_: *mut leanh::LeanObject,
    mut v_m_3105_: *mut leanh::LeanObject,
    mut v_a_3106_: *mut leanh::LeanObject,
    mut v_b_3107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3112_: u8 = 0;
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: u64 = 0;
    let mut v___x_3116_: u64 = 0;
    let mut v___x_3117_: u64 = 0;
    let mut v___x_3118_: u64 = 0;
    let mut v_fold_3119_: u64 = 0;
    let mut v___x_3120_: u64 = 0;
    let mut v___x_3121_: u64 = 0;
    let mut v___x_3122_: u64 = 0;
    let mut v___x_3123_: usize = 0;
    let mut v___x_3124_: usize = 0;
    let mut v___x_3125_: usize = 0;
    let mut v___x_3126_: usize = 0;
    let mut v___x_3127_: usize = 0;
    let mut v_bkt_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: u8 = 0;
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    let mut v_val_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3108_ = leanh::lean_ctor_get(v_m_3105_, 0);
                v_buckets_3109_ = leanh::lean_ctor_get(v_m_3105_, 1);
                v_isSharedCheck_3160_ = (!leanh::lean_is_exclusive(v_m_3105_)) as u8;
                if v_isSharedCheck_3160_ == 0 {
                    v___x_3111_ = v_m_3105_;
                    v_isShared_3112_ = v_isSharedCheck_3160_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3109_);
                    leanh::lean_inc(v_size_3108_);
                    leanh::lean_dec(v_m_3105_);
                    v___x_3111_ = leanh::lean_box(0);
                    v_isShared_3112_ = v_isSharedCheck_3160_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3113_ = lean_array_get_size(v_buckets_3109_);
                leanh::lean_inc_ref(v_inst_3104_);
                leanh::lean_inc_n(v_a_3106_, 2);
                v___x_3114_ = leanh::lean_apply_1(v_inst_3104_, v_a_3106_);
                v___x_3115_ = 32u64;
                v___x_3116_ = leanh::lean_unbox_uint64(v___x_3114_);
                v___x_3117_ = lean_uint64_shift_right(v___x_3116_, v___x_3115_);
                v___x_3118_ = leanh::lean_unbox_uint64(v___x_3114_);
                leanh::lean_dec_ref(v___x_3114_);
                v_fold_3119_ = lean_uint64_xor(v___x_3118_, v___x_3117_);
                v___x_3120_ = 16u64;
                v___x_3121_ = lean_uint64_shift_right(v_fold_3119_, v___x_3120_);
                v___x_3122_ = lean_uint64_xor(v_fold_3119_, v___x_3121_);
                v___x_3123_ = lean_uint64_to_usize(v___x_3122_);
                v___x_3124_ = lean_usize_of_nat(v___x_3113_);
                v___x_3125_ = 1usize;
                v___x_3126_ = lean_usize_sub(v___x_3124_, v___x_3125_);
                v___x_3127_ = lean_usize_land(v___x_3123_, v___x_3126_);
                v_bkt_3128_ = lean_array_uget_borrowed(v_buckets_3109_, v___x_3127_);
                leanh::lean_inc(v_bkt_3128_);
                leanh::lean_inc_ref(v_inst_3103_);
                v___x_3129_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_3103_,
                    v_a_3106_,
                    v_bkt_3128_,
                );
                if v___x_3129_ == 0 {
                    leanh::lean_dec_ref(v_inst_3103_);
                    v___x_3130_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3131_ = lean_nat_add(v_size_3108_, v___x_3130_);
                    leanh::lean_dec(v_size_3108_);
                    leanh::lean_inc(v_bkt_3128_);
                    v___x_3132_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3132_, 0, v_a_3106_);
                    leanh::lean_ctor_set(v___x_3132_, 1, v_b_3107_);
                    leanh::lean_ctor_set(v___x_3132_, 2, v_bkt_3128_);
                    v_buckets_x27_3133_ =
                        lean_array_uset(v_buckets_3109_, v___x_3127_, v___x_3132_);
                    v___x_3134_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3135_ = lean_nat_mul(v_size_x27_3131_, v___x_3134_);
                    v___x_3136_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3137_ = lean_nat_div(v___x_3135_, v___x_3136_);
                    leanh::lean_dec(v___x_3135_);
                    v___x_3138_ = lean_array_get_size(v_buckets_x27_3133_);
                    v___x_3139_ = lean_nat_dec_le(v___x_3137_, v___x_3138_);
                    leanh::lean_dec(v___x_3137_);
                    if v___x_3139_ == 0 {
                        v_val_3140_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                            v_inst_3104_,
                            v_buckets_x27_3133_,
                        );
                        if v_isShared_3112_ == 0 {
                            leanh::lean_ctor_set(v___x_3111_, 1, v_val_3140_);
                            leanh::lean_ctor_set(v___x_3111_, 0, v_size_x27_3131_);
                            v___x_3142_ = v___x_3111_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3145_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3145_,
                                0,
                                v_size_x27_3131_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_val_3140_);
                            v___x_3142_ = v_reuseFailAlloc_3145_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_inst_3104_);
                        if v_isShared_3112_ == 0 {
                            leanh::lean_ctor_set(v___x_3111_, 1, v_buckets_x27_3133_);
                            leanh::lean_ctor_set(v___x_3111_, 0, v_size_x27_3131_);
                            v___x_3147_ = v___x_3111_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3150_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3150_,
                                0,
                                v_size_x27_3131_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3150_,
                                1,
                                v_buckets_x27_3133_,
                            );
                            v___x_3147_ = v_reuseFailAlloc_3150_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_3128_);
                    leanh::lean_dec_ref(v_inst_3104_);
                    v___x_3151_ = leanh::lean_box(0);
                    v_buckets_x27_3152_ =
                        lean_array_uset(v_buckets_3109_, v___x_3127_, v___x_3151_);
                    v___x_3153_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_inst_3103_,
                        v_a_3106_,
                        v_b_3107_,
                        v_bkt_3128_,
                    );
                    v___x_3154_ = lean_array_uset(v_buckets_x27_3152_, v___x_3127_, v___x_3153_);
                    if v_isShared_3112_ == 0 {
                        leanh::lean_ctor_set(v___x_3111_, 1, v___x_3154_);
                        v___x_3156_ = v___x_3111_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3159_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_size_3108_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___x_3154_);
                        v___x_3156_ = v_reuseFailAlloc_3159_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3143_ = leanh::lean_box((v___x_3129_) as usize);
                v___x_3144_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3144_, 0, v___x_3143_);
                leanh::lean_ctor_set(v___x_3144_, 1, v___x_3142_);
                return v___x_3144_;
            }
            3 => {
                v___x_3148_ = leanh::lean_box((v___x_3129_) as usize);
                v___x_3149_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3149_, 0, v___x_3148_);
                leanh::lean_ctor_set(v___x_3149_, 1, v___x_3147_);
                return v___x_3149_;
            }
            4 => {
                v___x_3157_ = leanh::lean_box((v___x_3129_) as usize);
                v___x_3158_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3158_, 0, v___x_3157_);
                leanh::lean_ctor_set(v___x_3158_, 1, v___x_3156_);
                return v___x_3158_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertIfNew___redArg(
    mut v_inst_3161_: *mut leanh::LeanObject,
    mut v_inst_3162_: *mut leanh::LeanObject,
    mut v_m_3163_: *mut leanh::LeanObject,
    mut v_a_3164_: *mut leanh::LeanObject,
    mut v_b_3165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: u64 = 0;
    let mut v___x_3171_: u64 = 0;
    let mut v___x_3172_: u64 = 0;
    let mut v___x_3173_: u64 = 0;
    let mut v_fold_3174_: u64 = 0;
    let mut v___x_3175_: u64 = 0;
    let mut v___x_3176_: u64 = 0;
    let mut v___x_3177_: u64 = 0;
    let mut v___x_3178_: usize = 0;
    let mut v___x_3179_: usize = 0;
    let mut v___x_3180_: usize = 0;
    let mut v___x_3181_: usize = 0;
    let mut v___x_3182_: usize = 0;
    let mut v_bkt_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3187_: u8 = 0;
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: u8 = 0;
    let mut v_val_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3209_: u8 = 0;
    let mut v_unused_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3166_ = leanh::lean_ctor_get(v_m_3163_, 0);
                v_buckets_3167_ = leanh::lean_ctor_get(v_m_3163_, 1);
                v___x_3168_ = lean_array_get_size(v_buckets_3167_);
                leanh::lean_inc_ref(v_inst_3162_);
                leanh::lean_inc_n(v_a_3164_, 2);
                v___x_3169_ = leanh::lean_apply_1(v_inst_3162_, v_a_3164_);
                v___x_3170_ = 32u64;
                v___x_3171_ = leanh::lean_unbox_uint64(v___x_3169_);
                v___x_3172_ = lean_uint64_shift_right(v___x_3171_, v___x_3170_);
                v___x_3173_ = leanh::lean_unbox_uint64(v___x_3169_);
                leanh::lean_dec_ref(v___x_3169_);
                v_fold_3174_ = lean_uint64_xor(v___x_3173_, v___x_3172_);
                v___x_3175_ = 16u64;
                v___x_3176_ = lean_uint64_shift_right(v_fold_3174_, v___x_3175_);
                v___x_3177_ = lean_uint64_xor(v_fold_3174_, v___x_3176_);
                v___x_3178_ = lean_uint64_to_usize(v___x_3177_);
                v___x_3179_ = lean_usize_of_nat(v___x_3168_);
                v___x_3180_ = 1usize;
                v___x_3181_ = lean_usize_sub(v___x_3179_, v___x_3180_);
                v___x_3182_ = lean_usize_land(v___x_3178_, v___x_3181_);
                v_bkt_3183_ = lean_array_uget_borrowed(v_buckets_3167_, v___x_3182_);
                leanh::lean_inc(v_bkt_3183_);
                v___x_3184_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_3161_,
                    v_a_3164_,
                    v_bkt_3183_,
                );
                if v___x_3184_ == 0 {
                    leanh::lean_inc_ref(v_buckets_3167_);
                    leanh::lean_inc(v_size_3166_);
                    v_isSharedCheck_3209_ = (!leanh::lean_is_exclusive(v_m_3163_)) as u8;
                    if v_isSharedCheck_3209_ == 0 {
                        v_unused_3210_ = leanh::lean_ctor_get(v_m_3163_, 1);
                        leanh::lean_dec(v_unused_3210_);
                        v_unused_3211_ = leanh::lean_ctor_get(v_m_3163_, 0);
                        leanh::lean_dec(v_unused_3211_);
                        v___x_3186_ = v_m_3163_;
                        v_isShared_3187_ = v_isSharedCheck_3209_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_3163_);
                        v___x_3186_ = leanh::lean_box(0);
                        v_isShared_3187_ = v_isSharedCheck_3209_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_3165_);
                    leanh::lean_dec(v_a_3164_);
                    leanh::lean_dec_ref(v_inst_3162_);
                    v___x_3212_ = leanh::lean_box((v___x_3184_) as usize);
                    v___x_3213_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3213_, 0, v___x_3212_);
                    leanh::lean_ctor_set(v___x_3213_, 1, v_m_3163_);
                    return v___x_3213_;
                }
            }
            1 => {
                v___x_3188_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3189_ = lean_nat_add(v_size_3166_, v___x_3188_);
                leanh::lean_dec(v_size_3166_);
                leanh::lean_inc(v_bkt_3183_);
                v___x_3190_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3190_, 0, v_a_3164_);
                leanh::lean_ctor_set(v___x_3190_, 1, v_b_3165_);
                leanh::lean_ctor_set(v___x_3190_, 2, v_bkt_3183_);
                v_buckets_x27_3191_ = lean_array_uset(v_buckets_3167_, v___x_3182_, v___x_3190_);
                v___x_3192_ = leanh::lean_unsigned_to_nat(4);
                v___x_3193_ = lean_nat_mul(v_size_x27_3189_, v___x_3192_);
                v___x_3194_ = leanh::lean_unsigned_to_nat(3);
                v___x_3195_ = lean_nat_div(v___x_3193_, v___x_3194_);
                leanh::lean_dec(v___x_3193_);
                v___x_3196_ = lean_array_get_size(v_buckets_x27_3191_);
                v___x_3197_ = lean_nat_dec_le(v___x_3195_, v___x_3196_);
                leanh::lean_dec(v___x_3195_);
                if v___x_3197_ == 0 {
                    v_val_3198_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3162_,
                        v_buckets_x27_3191_,
                    );
                    if v_isShared_3187_ == 0 {
                        leanh::lean_ctor_set(v___x_3186_, 1, v_val_3198_);
                        leanh::lean_ctor_set(v___x_3186_, 0, v_size_x27_3189_);
                        v___x_3200_ = v___x_3186_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3203_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_size_x27_3189_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_val_3198_);
                        v___x_3200_ = v_reuseFailAlloc_3203_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_3162_);
                    if v_isShared_3187_ == 0 {
                        leanh::lean_ctor_set(v___x_3186_, 1, v_buckets_x27_3191_);
                        leanh::lean_ctor_set(v___x_3186_, 0, v_size_x27_3189_);
                        v___x_3205_ = v___x_3186_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3208_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_size_x27_3189_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_buckets_x27_3191_);
                        v___x_3205_ = v_reuseFailAlloc_3208_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3201_ = leanh::lean_box((v___x_3184_) as usize);
                v___x_3202_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3202_, 0, v___x_3201_);
                leanh::lean_ctor_set(v___x_3202_, 1, v___x_3200_);
                return v___x_3202_;
            }
            3 => {
                v___x_3206_ = leanh::lean_box((v___x_3184_) as usize);
                v___x_3207_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3207_, 0, v___x_3206_);
                leanh::lean_ctor_set(v___x_3207_, 1, v___x_3205_);
                return v___x_3207_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertIfNew(
    mut v_00_u03b1_3214_: *mut leanh::LeanObject,
    mut v_00_u03b2_3215_: *mut leanh::LeanObject,
    mut v_inst_3216_: *mut leanh::LeanObject,
    mut v_inst_3217_: *mut leanh::LeanObject,
    mut v_m_3218_: *mut leanh::LeanObject,
    mut v_a_3219_: *mut leanh::LeanObject,
    mut v_b_3220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: u64 = 0;
    let mut v___x_3226_: u64 = 0;
    let mut v___x_3227_: u64 = 0;
    let mut v___x_3228_: u64 = 0;
    let mut v_fold_3229_: u64 = 0;
    let mut v___x_3230_: u64 = 0;
    let mut v___x_3231_: u64 = 0;
    let mut v___x_3232_: u64 = 0;
    let mut v___x_3233_: usize = 0;
    let mut v___x_3234_: usize = 0;
    let mut v___x_3235_: usize = 0;
    let mut v___x_3236_: usize = 0;
    let mut v___x_3237_: usize = 0;
    let mut v_bkt_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: u8 = 0;
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3242_: u8 = 0;
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u8 = 0;
    let mut v_val_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3264_: u8 = 0;
    let mut v_unused_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3221_ = leanh::lean_ctor_get(v_m_3218_, 0);
                v_buckets_3222_ = leanh::lean_ctor_get(v_m_3218_, 1);
                v___x_3223_ = lean_array_get_size(v_buckets_3222_);
                leanh::lean_inc_ref(v_inst_3217_);
                leanh::lean_inc_n(v_a_3219_, 2);
                v___x_3224_ = leanh::lean_apply_1(v_inst_3217_, v_a_3219_);
                v___x_3225_ = 32u64;
                v___x_3226_ = leanh::lean_unbox_uint64(v___x_3224_);
                v___x_3227_ = lean_uint64_shift_right(v___x_3226_, v___x_3225_);
                v___x_3228_ = leanh::lean_unbox_uint64(v___x_3224_);
                leanh::lean_dec_ref(v___x_3224_);
                v_fold_3229_ = lean_uint64_xor(v___x_3228_, v___x_3227_);
                v___x_3230_ = 16u64;
                v___x_3231_ = lean_uint64_shift_right(v_fold_3229_, v___x_3230_);
                v___x_3232_ = lean_uint64_xor(v_fold_3229_, v___x_3231_);
                v___x_3233_ = lean_uint64_to_usize(v___x_3232_);
                v___x_3234_ = lean_usize_of_nat(v___x_3223_);
                v___x_3235_ = 1usize;
                v___x_3236_ = lean_usize_sub(v___x_3234_, v___x_3235_);
                v___x_3237_ = lean_usize_land(v___x_3233_, v___x_3236_);
                v_bkt_3238_ = lean_array_uget_borrowed(v_buckets_3222_, v___x_3237_);
                leanh::lean_inc(v_bkt_3238_);
                v___x_3239_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_3216_,
                    v_a_3219_,
                    v_bkt_3238_,
                );
                if v___x_3239_ == 0 {
                    leanh::lean_inc_ref(v_buckets_3222_);
                    leanh::lean_inc(v_size_3221_);
                    v_isSharedCheck_3264_ = (!leanh::lean_is_exclusive(v_m_3218_)) as u8;
                    if v_isSharedCheck_3264_ == 0 {
                        v_unused_3265_ = leanh::lean_ctor_get(v_m_3218_, 1);
                        leanh::lean_dec(v_unused_3265_);
                        v_unused_3266_ = leanh::lean_ctor_get(v_m_3218_, 0);
                        leanh::lean_dec(v_unused_3266_);
                        v___x_3241_ = v_m_3218_;
                        v_isShared_3242_ = v_isSharedCheck_3264_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_3218_);
                        v___x_3241_ = leanh::lean_box(0);
                        v_isShared_3242_ = v_isSharedCheck_3264_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_3220_);
                    leanh::lean_dec(v_a_3219_);
                    leanh::lean_dec_ref(v_inst_3217_);
                    v___x_3267_ = leanh::lean_box((v___x_3239_) as usize);
                    v___x_3268_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3268_, 0, v___x_3267_);
                    leanh::lean_ctor_set(v___x_3268_, 1, v_m_3218_);
                    return v___x_3268_;
                }
            }
            1 => {
                v___x_3243_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3244_ = lean_nat_add(v_size_3221_, v___x_3243_);
                leanh::lean_dec(v_size_3221_);
                leanh::lean_inc(v_bkt_3238_);
                v___x_3245_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3245_, 0, v_a_3219_);
                leanh::lean_ctor_set(v___x_3245_, 1, v_b_3220_);
                leanh::lean_ctor_set(v___x_3245_, 2, v_bkt_3238_);
                v_buckets_x27_3246_ = lean_array_uset(v_buckets_3222_, v___x_3237_, v___x_3245_);
                v___x_3247_ = leanh::lean_unsigned_to_nat(4);
                v___x_3248_ = lean_nat_mul(v_size_x27_3244_, v___x_3247_);
                v___x_3249_ = leanh::lean_unsigned_to_nat(3);
                v___x_3250_ = lean_nat_div(v___x_3248_, v___x_3249_);
                leanh::lean_dec(v___x_3248_);
                v___x_3251_ = lean_array_get_size(v_buckets_x27_3246_);
                v___x_3252_ = lean_nat_dec_le(v___x_3250_, v___x_3251_);
                leanh::lean_dec(v___x_3250_);
                if v___x_3252_ == 0 {
                    v_val_3253_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3217_,
                        v_buckets_x27_3246_,
                    );
                    if v_isShared_3242_ == 0 {
                        leanh::lean_ctor_set(v___x_3241_, 1, v_val_3253_);
                        leanh::lean_ctor_set(v___x_3241_, 0, v_size_x27_3244_);
                        v___x_3255_ = v___x_3241_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3258_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_size_x27_3244_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_val_3253_);
                        v___x_3255_ = v_reuseFailAlloc_3258_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_3217_);
                    if v_isShared_3242_ == 0 {
                        leanh::lean_ctor_set(v___x_3241_, 1, v_buckets_x27_3246_);
                        leanh::lean_ctor_set(v___x_3241_, 0, v_size_x27_3244_);
                        v___x_3260_ = v___x_3241_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3263_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_size_x27_3244_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_buckets_x27_3246_);
                        v___x_3260_ = v_reuseFailAlloc_3263_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3256_ = leanh::lean_box((v___x_3239_) as usize);
                v___x_3257_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3257_, 0, v___x_3256_);
                leanh::lean_ctor_set(v___x_3257_, 1, v___x_3255_);
                return v___x_3257_;
            }
            3 => {
                v___x_3261_ = leanh::lean_box((v___x_3239_) as usize);
                v___x_3262_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3262_, 0, v___x_3261_);
                leanh::lean_ctor_set(v___x_3262_, 1, v___x_3260_);
                return v___x_3262_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
    mut v_inst_3269_: *mut leanh::LeanObject,
    mut v_inst_3270_: *mut leanh::LeanObject,
    mut v_m_3271_: *mut leanh::LeanObject,
    mut v_a_3272_: *mut leanh::LeanObject,
    mut v_b_3273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: u64 = 0;
    let mut v___x_3279_: u64 = 0;
    let mut v___x_3280_: u64 = 0;
    let mut v___x_3281_: u64 = 0;
    let mut v_fold_3282_: u64 = 0;
    let mut v___x_3283_: u64 = 0;
    let mut v___x_3284_: u64 = 0;
    let mut v___x_3285_: u64 = 0;
    let mut v___x_3286_: usize = 0;
    let mut v___x_3287_: usize = 0;
    let mut v___x_3288_: usize = 0;
    let mut v___x_3289_: usize = 0;
    let mut v___x_3290_: usize = 0;
    let mut v_bkt_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: u8 = 0;
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3295_: u8 = 0;
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: u8 = 0;
    let mut v_val_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v_unused_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3274_ = leanh::lean_ctor_get(v_m_3271_, 0);
                v_buckets_3275_ = leanh::lean_ctor_get(v_m_3271_, 1);
                v___x_3276_ = lean_array_get_size(v_buckets_3275_);
                leanh::lean_inc_ref(v_inst_3270_);
                leanh::lean_inc_n(v_a_3272_, 2);
                v___x_3277_ = leanh::lean_apply_1(v_inst_3270_, v_a_3272_);
                v___x_3278_ = 32u64;
                v___x_3279_ = leanh::lean_unbox_uint64(v___x_3277_);
                v___x_3280_ = lean_uint64_shift_right(v___x_3279_, v___x_3278_);
                v___x_3281_ = leanh::lean_unbox_uint64(v___x_3277_);
                leanh::lean_dec_ref(v___x_3277_);
                v_fold_3282_ = lean_uint64_xor(v___x_3281_, v___x_3280_);
                v___x_3283_ = 16u64;
                v___x_3284_ = lean_uint64_shift_right(v_fold_3282_, v___x_3283_);
                v___x_3285_ = lean_uint64_xor(v_fold_3282_, v___x_3284_);
                v___x_3286_ = lean_uint64_to_usize(v___x_3285_);
                v___x_3287_ = lean_usize_of_nat(v___x_3276_);
                v___x_3288_ = 1usize;
                v___x_3289_ = lean_usize_sub(v___x_3287_, v___x_3288_);
                v___x_3290_ = lean_usize_land(v___x_3286_, v___x_3289_);
                v_bkt_3291_ = lean_array_uget_borrowed(v_buckets_3275_, v___x_3290_);
                leanh::lean_inc(v_bkt_3291_);
                v___x_3292_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_3269_,
                    v_a_3272_,
                    v_bkt_3291_,
                );
                if v___x_3292_ == 0 {
                    leanh::lean_inc_ref(v_buckets_3275_);
                    leanh::lean_inc(v_size_3274_);
                    v_isSharedCheck_3313_ = (!leanh::lean_is_exclusive(v_m_3271_)) as u8;
                    if v_isSharedCheck_3313_ == 0 {
                        v_unused_3314_ = leanh::lean_ctor_get(v_m_3271_, 1);
                        leanh::lean_dec(v_unused_3314_);
                        v_unused_3315_ = leanh::lean_ctor_get(v_m_3271_, 0);
                        leanh::lean_dec(v_unused_3315_);
                        v___x_3294_ = v_m_3271_;
                        v_isShared_3295_ = v_isSharedCheck_3313_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_3271_);
                        v___x_3294_ = leanh::lean_box(0);
                        v_isShared_3295_ = v_isSharedCheck_3313_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_3273_);
                    leanh::lean_dec(v_a_3272_);
                    leanh::lean_dec_ref(v_inst_3270_);
                    return v_m_3271_;
                }
            }
            1 => {
                v___x_3296_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3297_ = lean_nat_add(v_size_3274_, v___x_3296_);
                leanh::lean_dec(v_size_3274_);
                leanh::lean_inc(v_bkt_3291_);
                v___x_3298_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3298_, 0, v_a_3272_);
                leanh::lean_ctor_set(v___x_3298_, 1, v_b_3273_);
                leanh::lean_ctor_set(v___x_3298_, 2, v_bkt_3291_);
                v_buckets_x27_3299_ = lean_array_uset(v_buckets_3275_, v___x_3290_, v___x_3298_);
                v___x_3300_ = leanh::lean_unsigned_to_nat(4);
                v___x_3301_ = lean_nat_mul(v_size_x27_3297_, v___x_3300_);
                v___x_3302_ = leanh::lean_unsigned_to_nat(3);
                v___x_3303_ = lean_nat_div(v___x_3301_, v___x_3302_);
                leanh::lean_dec(v___x_3301_);
                v___x_3304_ = lean_array_get_size(v_buckets_x27_3299_);
                v___x_3305_ = lean_nat_dec_le(v___x_3303_, v___x_3304_);
                leanh::lean_dec(v___x_3303_);
                if v___x_3305_ == 0 {
                    v_val_3306_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3270_,
                        v_buckets_x27_3299_,
                    );
                    if v_isShared_3295_ == 0 {
                        leanh::lean_ctor_set(v___x_3294_, 1, v_val_3306_);
                        leanh::lean_ctor_set(v___x_3294_, 0, v_size_x27_3297_);
                        v___x_3308_ = v___x_3294_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3309_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_size_x27_3297_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3309_, 1, v_val_3306_);
                        v___x_3308_ = v_reuseFailAlloc_3309_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_3270_);
                    if v_isShared_3295_ == 0 {
                        leanh::lean_ctor_set(v___x_3294_, 1, v_buckets_x27_3299_);
                        leanh::lean_ctor_set(v___x_3294_, 0, v_size_x27_3297_);
                        v___x_3311_ = v___x_3294_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3312_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_size_x27_3297_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3312_, 1, v_buckets_x27_3299_);
                        v___x_3311_ = v_reuseFailAlloc_3312_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3308_;
            }
            3 => {
                return v___x_3311_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew(
    mut v_00_u03b1_3316_: *mut leanh::LeanObject,
    mut v_00_u03b2_3317_: *mut leanh::LeanObject,
    mut v_inst_3318_: *mut leanh::LeanObject,
    mut v_inst_3319_: *mut leanh::LeanObject,
    mut v_m_3320_: *mut leanh::LeanObject,
    mut v_a_3321_: *mut leanh::LeanObject,
    mut v_b_3322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3323_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_3318_,
        v_inst_3319_,
        v_m_3320_,
        v_a_3321_,
        v_b_3322_,
    );
    return v___x_3323_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getThenInsertIfNew_x3f___redArg(
    mut v_inst_3324_: *mut leanh::LeanObject,
    mut v_inst_3325_: *mut leanh::LeanObject,
    mut v_m_3326_: *mut leanh::LeanObject,
    mut v_a_3327_: *mut leanh::LeanObject,
    mut v_b_3328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: u64 = 0;
    let mut v___x_3334_: u64 = 0;
    let mut v___x_3335_: u64 = 0;
    let mut v___x_3336_: u64 = 0;
    let mut v_fold_3337_: u64 = 0;
    let mut v___x_3338_: u64 = 0;
    let mut v___x_3339_: u64 = 0;
    let mut v___x_3340_: u64 = 0;
    let mut v___x_3341_: usize = 0;
    let mut v___x_3342_: usize = 0;
    let mut v___x_3343_: usize = 0;
    let mut v___x_3344_: usize = 0;
    let mut v___x_3345_: usize = 0;
    let mut v_bkt_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3350_: u8 = 0;
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: u8 = 0;
    let mut v_val_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3370_: u8 = 0;
    let mut v_unused_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3329_ = leanh::lean_ctor_get(v_m_3326_, 0);
                v_buckets_3330_ = leanh::lean_ctor_get(v_m_3326_, 1);
                v___x_3331_ = lean_array_get_size(v_buckets_3330_);
                leanh::lean_inc_ref(v_inst_3325_);
                leanh::lean_inc_n(v_a_3327_, 2);
                v___x_3332_ = leanh::lean_apply_1(v_inst_3325_, v_a_3327_);
                v___x_3333_ = 32u64;
                v___x_3334_ = leanh::lean_unbox_uint64(v___x_3332_);
                v___x_3335_ = lean_uint64_shift_right(v___x_3334_, v___x_3333_);
                v___x_3336_ = leanh::lean_unbox_uint64(v___x_3332_);
                leanh::lean_dec_ref(v___x_3332_);
                v_fold_3337_ = lean_uint64_xor(v___x_3336_, v___x_3335_);
                v___x_3338_ = 16u64;
                v___x_3339_ = lean_uint64_shift_right(v_fold_3337_, v___x_3338_);
                v___x_3340_ = lean_uint64_xor(v_fold_3337_, v___x_3339_);
                v___x_3341_ = lean_uint64_to_usize(v___x_3340_);
                v___x_3342_ = lean_usize_of_nat(v___x_3331_);
                v___x_3343_ = 1usize;
                v___x_3344_ = lean_usize_sub(v___x_3342_, v___x_3343_);
                v___x_3345_ = lean_usize_land(v___x_3341_, v___x_3344_);
                v_bkt_3346_ = lean_array_uget_borrowed(v_buckets_3330_, v___x_3345_);
                leanh::lean_inc(v_bkt_3346_);
                v___x_3347_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
                    v_inst_3324_,
                    v_a_3327_,
                    v_bkt_3346_,
                );
                if leanh::lean_obj_tag(v___x_3347_) == 0 {
                    leanh::lean_inc_ref(v_buckets_3330_);
                    leanh::lean_inc(v_size_3329_);
                    v_isSharedCheck_3370_ = (!leanh::lean_is_exclusive(v_m_3326_)) as u8;
                    if v_isSharedCheck_3370_ == 0 {
                        v_unused_3371_ = leanh::lean_ctor_get(v_m_3326_, 1);
                        leanh::lean_dec(v_unused_3371_);
                        v_unused_3372_ = leanh::lean_ctor_get(v_m_3326_, 0);
                        leanh::lean_dec(v_unused_3372_);
                        v___x_3349_ = v_m_3326_;
                        v_isShared_3350_ = v_isSharedCheck_3370_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_3326_);
                        v___x_3349_ = leanh::lean_box(0);
                        v_isShared_3350_ = v_isSharedCheck_3370_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_3328_);
                    leanh::lean_dec(v_a_3327_);
                    leanh::lean_dec_ref(v_inst_3325_);
                    v___x_3373_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3373_, 0, v___x_3347_);
                    leanh::lean_ctor_set(v___x_3373_, 1, v_m_3326_);
                    return v___x_3373_;
                }
            }
            1 => {
                v___x_3351_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3352_ = lean_nat_add(v_size_3329_, v___x_3351_);
                leanh::lean_dec(v_size_3329_);
                leanh::lean_inc(v_bkt_3346_);
                v___x_3353_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3353_, 0, v_a_3327_);
                leanh::lean_ctor_set(v___x_3353_, 1, v_b_3328_);
                leanh::lean_ctor_set(v___x_3353_, 2, v_bkt_3346_);
                v_buckets_x27_3354_ = lean_array_uset(v_buckets_3330_, v___x_3345_, v___x_3353_);
                v___x_3355_ = leanh::lean_unsigned_to_nat(4);
                v___x_3356_ = lean_nat_mul(v_size_x27_3352_, v___x_3355_);
                v___x_3357_ = leanh::lean_unsigned_to_nat(3);
                v___x_3358_ = lean_nat_div(v___x_3356_, v___x_3357_);
                leanh::lean_dec(v___x_3356_);
                v___x_3359_ = lean_array_get_size(v_buckets_x27_3354_);
                v___x_3360_ = lean_nat_dec_le(v___x_3358_, v___x_3359_);
                leanh::lean_dec(v___x_3358_);
                if v___x_3360_ == 0 {
                    v_val_3361_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3325_,
                        v_buckets_x27_3354_,
                    );
                    if v_isShared_3350_ == 0 {
                        leanh::lean_ctor_set(v___x_3349_, 1, v_val_3361_);
                        leanh::lean_ctor_set(v___x_3349_, 0, v_size_x27_3352_);
                        v___x_3363_ = v___x_3349_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3365_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_size_x27_3352_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3365_, 1, v_val_3361_);
                        v___x_3363_ = v_reuseFailAlloc_3365_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_3325_);
                    if v_isShared_3350_ == 0 {
                        leanh::lean_ctor_set(v___x_3349_, 1, v_buckets_x27_3354_);
                        leanh::lean_ctor_set(v___x_3349_, 0, v_size_x27_3352_);
                        v___x_3367_ = v___x_3349_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3369_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_size_x27_3352_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_buckets_x27_3354_);
                        v___x_3367_ = v_reuseFailAlloc_3369_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3364_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3364_, 0, v___x_3347_);
                leanh::lean_ctor_set(v___x_3364_, 1, v___x_3363_);
                return v___x_3364_;
            }
            3 => {
                v___x_3368_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3368_, 0, v___x_3347_);
                leanh::lean_ctor_set(v___x_3368_, 1, v___x_3367_);
                return v___x_3368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getThenInsertIfNew_x3f(
    mut v_00_u03b1_3374_: *mut leanh::LeanObject,
    mut v_00_u03b2_3375_: *mut leanh::LeanObject,
    mut v_inst_3376_: *mut leanh::LeanObject,
    mut v_inst_3377_: *mut leanh::LeanObject,
    mut v_inst_3378_: *mut leanh::LeanObject,
    mut v_m_3379_: *mut leanh::LeanObject,
    mut v_a_3380_: *mut leanh::LeanObject,
    mut v_b_3381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: u64 = 0;
    let mut v___x_3387_: u64 = 0;
    let mut v___x_3388_: u64 = 0;
    let mut v___x_3389_: u64 = 0;
    let mut v_fold_3390_: u64 = 0;
    let mut v___x_3391_: u64 = 0;
    let mut v___x_3392_: u64 = 0;
    let mut v___x_3393_: u64 = 0;
    let mut v___x_3394_: usize = 0;
    let mut v___x_3395_: usize = 0;
    let mut v___x_3396_: usize = 0;
    let mut v___x_3397_: usize = 0;
    let mut v___x_3398_: usize = 0;
    let mut v_bkt_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3403_: u8 = 0;
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: u8 = 0;
    let mut v_val_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3423_: u8 = 0;
    let mut v_unused_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3382_ = leanh::lean_ctor_get(v_m_3379_, 0);
                v_buckets_3383_ = leanh::lean_ctor_get(v_m_3379_, 1);
                v___x_3384_ = lean_array_get_size(v_buckets_3383_);
                leanh::lean_inc_ref(v_inst_3377_);
                leanh::lean_inc_n(v_a_3380_, 2);
                v___x_3385_ = leanh::lean_apply_1(v_inst_3377_, v_a_3380_);
                v___x_3386_ = 32u64;
                v___x_3387_ = leanh::lean_unbox_uint64(v___x_3385_);
                v___x_3388_ = lean_uint64_shift_right(v___x_3387_, v___x_3386_);
                v___x_3389_ = leanh::lean_unbox_uint64(v___x_3385_);
                leanh::lean_dec_ref(v___x_3385_);
                v_fold_3390_ = lean_uint64_xor(v___x_3389_, v___x_3388_);
                v___x_3391_ = 16u64;
                v___x_3392_ = lean_uint64_shift_right(v_fold_3390_, v___x_3391_);
                v___x_3393_ = lean_uint64_xor(v_fold_3390_, v___x_3392_);
                v___x_3394_ = lean_uint64_to_usize(v___x_3393_);
                v___x_3395_ = lean_usize_of_nat(v___x_3384_);
                v___x_3396_ = 1usize;
                v___x_3397_ = lean_usize_sub(v___x_3395_, v___x_3396_);
                v___x_3398_ = lean_usize_land(v___x_3394_, v___x_3397_);
                v_bkt_3399_ = lean_array_uget_borrowed(v_buckets_3383_, v___x_3398_);
                leanh::lean_inc(v_bkt_3399_);
                v___x_3400_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
                    v_inst_3376_,
                    v_a_3380_,
                    v_bkt_3399_,
                );
                if leanh::lean_obj_tag(v___x_3400_) == 0 {
                    leanh::lean_inc_ref(v_buckets_3383_);
                    leanh::lean_inc(v_size_3382_);
                    v_isSharedCheck_3423_ = (!leanh::lean_is_exclusive(v_m_3379_)) as u8;
                    if v_isSharedCheck_3423_ == 0 {
                        v_unused_3424_ = leanh::lean_ctor_get(v_m_3379_, 1);
                        leanh::lean_dec(v_unused_3424_);
                        v_unused_3425_ = leanh::lean_ctor_get(v_m_3379_, 0);
                        leanh::lean_dec(v_unused_3425_);
                        v___x_3402_ = v_m_3379_;
                        v_isShared_3403_ = v_isSharedCheck_3423_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_3379_);
                        v___x_3402_ = leanh::lean_box(0);
                        v_isShared_3403_ = v_isSharedCheck_3423_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_3381_);
                    leanh::lean_dec(v_a_3380_);
                    leanh::lean_dec_ref(v_inst_3377_);
                    v___x_3426_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3426_, 0, v___x_3400_);
                    leanh::lean_ctor_set(v___x_3426_, 1, v_m_3379_);
                    return v___x_3426_;
                }
            }
            1 => {
                v___x_3404_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3405_ = lean_nat_add(v_size_3382_, v___x_3404_);
                leanh::lean_dec(v_size_3382_);
                leanh::lean_inc(v_bkt_3399_);
                v___x_3406_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3406_, 0, v_a_3380_);
                leanh::lean_ctor_set(v___x_3406_, 1, v_b_3381_);
                leanh::lean_ctor_set(v___x_3406_, 2, v_bkt_3399_);
                v_buckets_x27_3407_ = lean_array_uset(v_buckets_3383_, v___x_3398_, v___x_3406_);
                v___x_3408_ = leanh::lean_unsigned_to_nat(4);
                v___x_3409_ = lean_nat_mul(v_size_x27_3405_, v___x_3408_);
                v___x_3410_ = leanh::lean_unsigned_to_nat(3);
                v___x_3411_ = lean_nat_div(v___x_3409_, v___x_3410_);
                leanh::lean_dec(v___x_3409_);
                v___x_3412_ = lean_array_get_size(v_buckets_x27_3407_);
                v___x_3413_ = lean_nat_dec_le(v___x_3411_, v___x_3412_);
                leanh::lean_dec(v___x_3411_);
                if v___x_3413_ == 0 {
                    v_val_3414_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_3377_,
                        v_buckets_x27_3407_,
                    );
                    if v_isShared_3403_ == 0 {
                        leanh::lean_ctor_set(v___x_3402_, 1, v_val_3414_);
                        leanh::lean_ctor_set(v___x_3402_, 0, v_size_x27_3405_);
                        v___x_3416_ = v___x_3402_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3418_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_size_x27_3405_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3418_, 1, v_val_3414_);
                        v___x_3416_ = v_reuseFailAlloc_3418_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_3377_);
                    if v_isShared_3403_ == 0 {
                        leanh::lean_ctor_set(v___x_3402_, 1, v_buckets_x27_3407_);
                        leanh::lean_ctor_set(v___x_3402_, 0, v_size_x27_3405_);
                        v___x_3420_ = v___x_3402_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3422_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_size_x27_3405_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_buckets_x27_3407_);
                        v___x_3420_ = v_reuseFailAlloc_3422_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3417_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3417_, 0, v___x_3400_);
                leanh::lean_ctor_set(v___x_3417_, 1, v___x_3416_);
                return v___x_3417_;
            }
            3 => {
                v___x_3421_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3421_, 0, v___x_3400_);
                leanh::lean_ctor_set(v___x_3421_, 1, v___x_3420_);
                return v___x_3421_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
    mut v_inst_3427_: *mut leanh::LeanObject,
    mut v_inst_3428_: *mut leanh::LeanObject,
    mut v_m_3429_: *mut leanh::LeanObject,
    mut v_a_3430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: u64 = 0;
    let mut v___x_3435_: u64 = 0;
    let mut v___x_3436_: u64 = 0;
    let mut v___x_3437_: u64 = 0;
    let mut v_fold_3438_: u64 = 0;
    let mut v___x_3439_: u64 = 0;
    let mut v___x_3440_: u64 = 0;
    let mut v___x_3441_: u64 = 0;
    let mut v___x_3442_: usize = 0;
    let mut v___x_3443_: usize = 0;
    let mut v___x_3444_: usize = 0;
    let mut v___x_3445_: usize = 0;
    let mut v___x_3446_: usize = 0;
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3431_ = leanh::lean_ctor_get(v_m_3429_, 1);
    v___x_3432_ = lean_array_get_size(v_buckets_3431_);
    leanh::lean_inc(v_a_3430_);
    v___x_3433_ = leanh::lean_apply_1(v_inst_3428_, v_a_3430_);
    v___x_3434_ = 32u64;
    v___x_3435_ = leanh::lean_unbox_uint64(v___x_3433_);
    v___x_3436_ = lean_uint64_shift_right(v___x_3435_, v___x_3434_);
    v___x_3437_ = leanh::lean_unbox_uint64(v___x_3433_);
    leanh::lean_dec_ref(v___x_3433_);
    v_fold_3438_ = lean_uint64_xor(v___x_3437_, v___x_3436_);
    v___x_3439_ = 16u64;
    v___x_3440_ = lean_uint64_shift_right(v_fold_3438_, v___x_3439_);
    v___x_3441_ = lean_uint64_xor(v_fold_3438_, v___x_3440_);
    v___x_3442_ = lean_uint64_to_usize(v___x_3441_);
    v___x_3443_ = lean_usize_of_nat(v___x_3432_);
    v___x_3444_ = 1usize;
    v___x_3445_ = lean_usize_sub(v___x_3443_, v___x_3444_);
    v___x_3446_ = lean_usize_land(v___x_3442_, v___x_3445_);
    v___x_3447_ = lean_array_uget_borrowed(v_buckets_3431_, v___x_3446_);
    leanh::lean_inc(v___x_3447_);
    v___x_3448_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
        v_inst_3427_,
        v_a_3430_,
        v___x_3447_,
    );
    return v___x_3448_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg___boxed(
    mut v_inst_3449_: *mut leanh::LeanObject,
    mut v_inst_3450_: *mut leanh::LeanObject,
    mut v_m_3451_: *mut leanh::LeanObject,
    mut v_a_3452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3453_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        v_inst_3449_,
        v_inst_3450_,
        v_m_3451_,
        v_a_3452_,
    );
    leanh::lean_dec_ref(v_m_3451_);
    return v_res_3453_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f(
    mut v_00_u03b1_3454_: *mut leanh::LeanObject,
    mut v_00_u03b2_3455_: *mut leanh::LeanObject,
    mut v_inst_3456_: *mut leanh::LeanObject,
    mut v_inst_3457_: *mut leanh::LeanObject,
    mut v_inst_3458_: *mut leanh::LeanObject,
    mut v_m_3459_: *mut leanh::LeanObject,
    mut v_a_3460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3461_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        v_inst_3456_,
        v_inst_3458_,
        v_m_3459_,
        v_a_3460_,
    );
    return v___x_3461_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x3f___boxed(
    mut v_00_u03b1_3462_: *mut leanh::LeanObject,
    mut v_00_u03b2_3463_: *mut leanh::LeanObject,
    mut v_inst_3464_: *mut leanh::LeanObject,
    mut v_inst_3465_: *mut leanh::LeanObject,
    mut v_inst_3466_: *mut leanh::LeanObject,
    mut v_m_3467_: *mut leanh::LeanObject,
    mut v_a_3468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3469_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f(
        v_00_u03b1_3462_,
        v_00_u03b2_3463_,
        v_inst_3464_,
        v_inst_3465_,
        v_inst_3466_,
        v_m_3467_,
        v_a_3468_,
    );
    leanh::lean_dec_ref(v_m_3467_);
    return v_res_3469_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
    mut v_inst_3470_: *mut leanh::LeanObject,
    mut v_inst_3471_: *mut leanh::LeanObject,
    mut v_m_3472_: *mut leanh::LeanObject,
    mut v_a_3473_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: u64 = 0;
    let mut v___x_3478_: u64 = 0;
    let mut v___x_3479_: u64 = 0;
    let mut v___x_3480_: u64 = 0;
    let mut v_fold_3481_: u64 = 0;
    let mut v___x_3482_: u64 = 0;
    let mut v___x_3483_: u64 = 0;
    let mut v___x_3484_: u64 = 0;
    let mut v___x_3485_: usize = 0;
    let mut v___x_3486_: usize = 0;
    let mut v___x_3487_: usize = 0;
    let mut v___x_3488_: usize = 0;
    let mut v___x_3489_: usize = 0;
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: u8 = 0;
    v_buckets_3474_ = leanh::lean_ctor_get(v_m_3472_, 1);
    v___x_3475_ = lean_array_get_size(v_buckets_3474_);
    leanh::lean_inc(v_a_3473_);
    v___x_3476_ = leanh::lean_apply_1(v_inst_3471_, v_a_3473_);
    v___x_3477_ = 32u64;
    v___x_3478_ = leanh::lean_unbox_uint64(v___x_3476_);
    v___x_3479_ = lean_uint64_shift_right(v___x_3478_, v___x_3477_);
    v___x_3480_ = leanh::lean_unbox_uint64(v___x_3476_);
    leanh::lean_dec_ref(v___x_3476_);
    v_fold_3481_ = lean_uint64_xor(v___x_3480_, v___x_3479_);
    v___x_3482_ = 16u64;
    v___x_3483_ = lean_uint64_shift_right(v_fold_3481_, v___x_3482_);
    v___x_3484_ = lean_uint64_xor(v_fold_3481_, v___x_3483_);
    v___x_3485_ = lean_uint64_to_usize(v___x_3484_);
    v___x_3486_ = lean_usize_of_nat(v___x_3475_);
    v___x_3487_ = 1usize;
    v___x_3488_ = lean_usize_sub(v___x_3486_, v___x_3487_);
    v___x_3489_ = lean_usize_land(v___x_3485_, v___x_3488_);
    v___x_3490_ = lean_array_uget_borrowed(v_buckets_3474_, v___x_3489_);
    leanh::lean_inc(v___x_3490_);
    v___x_3491_ =
        l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_3470_, v_a_3473_, v___x_3490_);
    return v___x_3491_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___redArg___boxed(
    mut v_inst_3492_: *mut leanh::LeanObject,
    mut v_inst_3493_: *mut leanh::LeanObject,
    mut v_m_3494_: *mut leanh::LeanObject,
    mut v_a_3495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3496_: u8 = 0;
    let mut v_r_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3496_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_3492_,
        v_inst_3493_,
        v_m_3494_,
        v_a_3495_,
    );
    leanh::lean_dec_ref(v_m_3494_);
    v_r_3497_ = leanh::lean_box((v_res_3496_) as usize);
    return v_r_3497_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains(
    mut v_00_u03b1_3498_: *mut leanh::LeanObject,
    mut v_00_u03b2_3499_: *mut leanh::LeanObject,
    mut v_inst_3500_: *mut leanh::LeanObject,
    mut v_inst_3501_: *mut leanh::LeanObject,
    mut v_m_3502_: *mut leanh::LeanObject,
    mut v_a_3503_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3504_: u8 = 0;
    v___x_3504_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_3500_,
        v_inst_3501_,
        v_m_3502_,
        v_a_3503_,
    );
    return v___x_3504_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___boxed(
    mut v_00_u03b1_3505_: *mut leanh::LeanObject,
    mut v_00_u03b2_3506_: *mut leanh::LeanObject,
    mut v_inst_3507_: *mut leanh::LeanObject,
    mut v_inst_3508_: *mut leanh::LeanObject,
    mut v_m_3509_: *mut leanh::LeanObject,
    mut v_a_3510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3511_: u8 = 0;
    let mut v_r_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3511_ = l_Std_DHashMap_Internal_Raw_u2080_contains(
        v_00_u03b1_3505_,
        v_00_u03b2_3506_,
        v_inst_3507_,
        v_inst_3508_,
        v_m_3509_,
        v_a_3510_,
    );
    leanh::lean_dec_ref(v_m_3509_);
    v_r_3512_ = leanh::lean_box((v_res_3511_) as usize);
    return v_r_3512_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get___redArg(
    mut v_inst_3513_: *mut leanh::LeanObject,
    mut v_inst_3514_: *mut leanh::LeanObject,
    mut v_m_3515_: *mut leanh::LeanObject,
    mut v_a_3516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: u64 = 0;
    let mut v___x_3521_: u64 = 0;
    let mut v___x_3522_: u64 = 0;
    let mut v___x_3523_: u64 = 0;
    let mut v_fold_3524_: u64 = 0;
    let mut v___x_3525_: u64 = 0;
    let mut v___x_3526_: u64 = 0;
    let mut v___x_3527_: u64 = 0;
    let mut v___x_3528_: usize = 0;
    let mut v___x_3529_: usize = 0;
    let mut v___x_3530_: usize = 0;
    let mut v___x_3531_: usize = 0;
    let mut v___x_3532_: usize = 0;
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3517_ = leanh::lean_ctor_get(v_m_3515_, 1);
    v___x_3518_ = lean_array_get_size(v_buckets_3517_);
    leanh::lean_inc(v_a_3516_);
    v___x_3519_ = leanh::lean_apply_1(v_inst_3514_, v_a_3516_);
    v___x_3520_ = 32u64;
    v___x_3521_ = leanh::lean_unbox_uint64(v___x_3519_);
    v___x_3522_ = lean_uint64_shift_right(v___x_3521_, v___x_3520_);
    v___x_3523_ = leanh::lean_unbox_uint64(v___x_3519_);
    leanh::lean_dec_ref(v___x_3519_);
    v_fold_3524_ = lean_uint64_xor(v___x_3523_, v___x_3522_);
    v___x_3525_ = 16u64;
    v___x_3526_ = lean_uint64_shift_right(v_fold_3524_, v___x_3525_);
    v___x_3527_ = lean_uint64_xor(v_fold_3524_, v___x_3526_);
    v___x_3528_ = lean_uint64_to_usize(v___x_3527_);
    v___x_3529_ = lean_usize_of_nat(v___x_3518_);
    v___x_3530_ = 1usize;
    v___x_3531_ = lean_usize_sub(v___x_3529_, v___x_3530_);
    v___x_3532_ = lean_usize_land(v___x_3528_, v___x_3531_);
    v___x_3533_ = lean_array_uget_borrowed(v_buckets_3517_, v___x_3532_);
    leanh::lean_inc(v___x_3533_);
    v___x_3534_ =
        l_Std_DHashMap_Internal_AssocList_getCast___redArg(v_inst_3513_, v_a_3516_, v___x_3533_);
    return v___x_3534_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get___redArg___boxed(
    mut v_inst_3535_: *mut leanh::LeanObject,
    mut v_inst_3536_: *mut leanh::LeanObject,
    mut v_m_3537_: *mut leanh::LeanObject,
    mut v_a_3538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3539_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(
        v_inst_3535_,
        v_inst_3536_,
        v_m_3537_,
        v_a_3538_,
    );
    leanh::lean_dec_ref(v_m_3537_);
    return v_res_3539_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get(
    mut v_00_u03b1_3540_: *mut leanh::LeanObject,
    mut v_00_u03b2_3541_: *mut leanh::LeanObject,
    mut v_inst_3542_: *mut leanh::LeanObject,
    mut v_inst_3543_: *mut leanh::LeanObject,
    mut v_inst_3544_: *mut leanh::LeanObject,
    mut v_m_3545_: *mut leanh::LeanObject,
    mut v_a_3546_: *mut leanh::LeanObject,
    mut v_hma_3547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3548_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(
        v_inst_3542_,
        v_inst_3544_,
        v_m_3545_,
        v_a_3546_,
    );
    return v___x_3548_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get___boxed(
    mut v_00_u03b1_3549_: *mut leanh::LeanObject,
    mut v_00_u03b2_3550_: *mut leanh::LeanObject,
    mut v_inst_3551_: *mut leanh::LeanObject,
    mut v_inst_3552_: *mut leanh::LeanObject,
    mut v_inst_3553_: *mut leanh::LeanObject,
    mut v_m_3554_: *mut leanh::LeanObject,
    mut v_a_3555_: *mut leanh::LeanObject,
    mut v_hma_3556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3557_ = l_Std_DHashMap_Internal_Raw_u2080_get(
        v_00_u03b1_3549_,
        v_00_u03b2_3550_,
        v_inst_3551_,
        v_inst_3552_,
        v_inst_3553_,
        v_m_3554_,
        v_a_3555_,
        v_hma_3556_,
    );
    leanh::lean_dec_ref(v_m_3554_);
    return v_res_3557_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(
    mut v_inst_3558_: *mut leanh::LeanObject,
    mut v_inst_3559_: *mut leanh::LeanObject,
    mut v_m_3560_: *mut leanh::LeanObject,
    mut v_a_3561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: u64 = 0;
    let mut v___x_3566_: u64 = 0;
    let mut v___x_3567_: u64 = 0;
    let mut v___x_3568_: u64 = 0;
    let mut v_fold_3569_: u64 = 0;
    let mut v___x_3570_: u64 = 0;
    let mut v___x_3571_: u64 = 0;
    let mut v___x_3572_: u64 = 0;
    let mut v___x_3573_: usize = 0;
    let mut v___x_3574_: usize = 0;
    let mut v___x_3575_: usize = 0;
    let mut v___x_3576_: usize = 0;
    let mut v___x_3577_: usize = 0;
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3562_ = leanh::lean_ctor_get(v_m_3560_, 1);
    v___x_3563_ = lean_array_get_size(v_buckets_3562_);
    leanh::lean_inc(v_a_3561_);
    v___x_3564_ = leanh::lean_apply_1(v_inst_3559_, v_a_3561_);
    v___x_3565_ = 32u64;
    v___x_3566_ = leanh::lean_unbox_uint64(v___x_3564_);
    v___x_3567_ = lean_uint64_shift_right(v___x_3566_, v___x_3565_);
    v___x_3568_ = leanh::lean_unbox_uint64(v___x_3564_);
    leanh::lean_dec_ref(v___x_3564_);
    v_fold_3569_ = lean_uint64_xor(v___x_3568_, v___x_3567_);
    v___x_3570_ = 16u64;
    v___x_3571_ = lean_uint64_shift_right(v_fold_3569_, v___x_3570_);
    v___x_3572_ = lean_uint64_xor(v_fold_3569_, v___x_3571_);
    v___x_3573_ = lean_uint64_to_usize(v___x_3572_);
    v___x_3574_ = lean_usize_of_nat(v___x_3563_);
    v___x_3575_ = 1usize;
    v___x_3576_ = lean_usize_sub(v___x_3574_, v___x_3575_);
    v___x_3577_ = lean_usize_land(v___x_3573_, v___x_3576_);
    v___x_3578_ = lean_array_uget_borrowed(v_buckets_3562_, v___x_3577_);
    leanh::lean_inc(v___x_3578_);
    v___x_3579_ =
        l_Std_DHashMap_Internal_AssocList_getEntry___redArg(v_inst_3558_, v_a_3561_, v___x_3578_);
    return v___x_3579_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg___boxed(
    mut v_inst_3580_: *mut leanh::LeanObject,
    mut v_inst_3581_: *mut leanh::LeanObject,
    mut v_m_3582_: *mut leanh::LeanObject,
    mut v_a_3583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3584_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(
        v_inst_3580_,
        v_inst_3581_,
        v_m_3582_,
        v_a_3583_,
    );
    leanh::lean_dec_ref(v_m_3582_);
    return v_res_3584_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry(
    mut v_00_u03b1_3585_: *mut leanh::LeanObject,
    mut v_00_u03b2_3586_: *mut leanh::LeanObject,
    mut v_inst_3587_: *mut leanh::LeanObject,
    mut v_inst_3588_: *mut leanh::LeanObject,
    mut v_m_3589_: *mut leanh::LeanObject,
    mut v_a_3590_: *mut leanh::LeanObject,
    mut v_hma_3591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3592_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(
        v_inst_3587_,
        v_inst_3588_,
        v_m_3589_,
        v_a_3590_,
    );
    return v___x_3592_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry___boxed(
    mut v_00_u03b1_3593_: *mut leanh::LeanObject,
    mut v_00_u03b2_3594_: *mut leanh::LeanObject,
    mut v_inst_3595_: *mut leanh::LeanObject,
    mut v_inst_3596_: *mut leanh::LeanObject,
    mut v_m_3597_: *mut leanh::LeanObject,
    mut v_a_3598_: *mut leanh::LeanObject,
    mut v_hma_3599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3600_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry(
        v_00_u03b1_3593_,
        v_00_u03b2_3594_,
        v_inst_3595_,
        v_inst_3596_,
        v_m_3597_,
        v_a_3598_,
        v_hma_3599_,
    );
    leanh::lean_dec_ref(v_m_3597_);
    return v_res_3600_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(
    mut v_inst_3601_: *mut leanh::LeanObject,
    mut v_inst_3602_: *mut leanh::LeanObject,
    mut v_m_3603_: *mut leanh::LeanObject,
    mut v_a_3604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: u64 = 0;
    let mut v___x_3609_: u64 = 0;
    let mut v___x_3610_: u64 = 0;
    let mut v___x_3611_: u64 = 0;
    let mut v_fold_3612_: u64 = 0;
    let mut v___x_3613_: u64 = 0;
    let mut v___x_3614_: u64 = 0;
    let mut v___x_3615_: u64 = 0;
    let mut v___x_3616_: usize = 0;
    let mut v___x_3617_: usize = 0;
    let mut v___x_3618_: usize = 0;
    let mut v___x_3619_: usize = 0;
    let mut v___x_3620_: usize = 0;
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3605_ = leanh::lean_ctor_get(v_m_3603_, 1);
    v___x_3606_ = lean_array_get_size(v_buckets_3605_);
    leanh::lean_inc(v_a_3604_);
    v___x_3607_ = leanh::lean_apply_1(v_inst_3602_, v_a_3604_);
    v___x_3608_ = 32u64;
    v___x_3609_ = leanh::lean_unbox_uint64(v___x_3607_);
    v___x_3610_ = lean_uint64_shift_right(v___x_3609_, v___x_3608_);
    v___x_3611_ = leanh::lean_unbox_uint64(v___x_3607_);
    leanh::lean_dec_ref(v___x_3607_);
    v_fold_3612_ = lean_uint64_xor(v___x_3611_, v___x_3610_);
    v___x_3613_ = 16u64;
    v___x_3614_ = lean_uint64_shift_right(v_fold_3612_, v___x_3613_);
    v___x_3615_ = lean_uint64_xor(v_fold_3612_, v___x_3614_);
    v___x_3616_ = lean_uint64_to_usize(v___x_3615_);
    v___x_3617_ = lean_usize_of_nat(v___x_3606_);
    v___x_3618_ = 1usize;
    v___x_3619_ = lean_usize_sub(v___x_3617_, v___x_3618_);
    v___x_3620_ = lean_usize_land(v___x_3616_, v___x_3619_);
    v___x_3621_ = lean_array_uget_borrowed(v_buckets_3605_, v___x_3620_);
    leanh::lean_inc(v___x_3621_);
    v___x_3622_ = l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(
        v_inst_3601_,
        v_a_3604_,
        v___x_3621_,
    );
    return v___x_3622_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg___boxed(
    mut v_inst_3623_: *mut leanh::LeanObject,
    mut v_inst_3624_: *mut leanh::LeanObject,
    mut v_m_3625_: *mut leanh::LeanObject,
    mut v_a_3626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3627_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(
        v_inst_3623_,
        v_inst_3624_,
        v_m_3625_,
        v_a_3626_,
    );
    leanh::lean_dec_ref(v_m_3625_);
    return v_res_3627_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f(
    mut v_00_u03b1_3628_: *mut leanh::LeanObject,
    mut v_00_u03b2_3629_: *mut leanh::LeanObject,
    mut v_inst_3630_: *mut leanh::LeanObject,
    mut v_inst_3631_: *mut leanh::LeanObject,
    mut v_m_3632_: *mut leanh::LeanObject,
    mut v_a_3633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3634_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(
        v_inst_3630_,
        v_inst_3631_,
        v_m_3632_,
        v_a_3633_,
    );
    return v___x_3634_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___boxed(
    mut v_00_u03b1_3635_: *mut leanh::LeanObject,
    mut v_00_u03b2_3636_: *mut leanh::LeanObject,
    mut v_inst_3637_: *mut leanh::LeanObject,
    mut v_inst_3638_: *mut leanh::LeanObject,
    mut v_m_3639_: *mut leanh::LeanObject,
    mut v_a_3640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3641_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f(
        v_00_u03b1_3635_,
        v_00_u03b2_3636_,
        v_inst_3637_,
        v_inst_3638_,
        v_m_3639_,
        v_a_3640_,
    );
    leanh::lean_dec_ref(v_m_3639_);
    return v_res_3641_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(
    mut v_inst_3642_: *mut leanh::LeanObject,
    mut v_inst_3643_: *mut leanh::LeanObject,
    mut v_m_3644_: *mut leanh::LeanObject,
    mut v_a_3645_: *mut leanh::LeanObject,
    mut v_fallback_3646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: u64 = 0;
    let mut v___x_3651_: u64 = 0;
    let mut v___x_3652_: u64 = 0;
    let mut v___x_3653_: u64 = 0;
    let mut v_fold_3654_: u64 = 0;
    let mut v___x_3655_: u64 = 0;
    let mut v___x_3656_: u64 = 0;
    let mut v___x_3657_: u64 = 0;
    let mut v___x_3658_: usize = 0;
    let mut v___x_3659_: usize = 0;
    let mut v___x_3660_: usize = 0;
    let mut v___x_3661_: usize = 0;
    let mut v___x_3662_: usize = 0;
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3647_ = leanh::lean_ctor_get(v_m_3644_, 1);
    v___x_3648_ = lean_array_get_size(v_buckets_3647_);
    leanh::lean_inc(v_a_3645_);
    v___x_3649_ = leanh::lean_apply_1(v_inst_3643_, v_a_3645_);
    v___x_3650_ = 32u64;
    v___x_3651_ = leanh::lean_unbox_uint64(v___x_3649_);
    v___x_3652_ = lean_uint64_shift_right(v___x_3651_, v___x_3650_);
    v___x_3653_ = leanh::lean_unbox_uint64(v___x_3649_);
    leanh::lean_dec_ref(v___x_3649_);
    v_fold_3654_ = lean_uint64_xor(v___x_3653_, v___x_3652_);
    v___x_3655_ = 16u64;
    v___x_3656_ = lean_uint64_shift_right(v_fold_3654_, v___x_3655_);
    v___x_3657_ = lean_uint64_xor(v_fold_3654_, v___x_3656_);
    v___x_3658_ = lean_uint64_to_usize(v___x_3657_);
    v___x_3659_ = lean_usize_of_nat(v___x_3648_);
    v___x_3660_ = 1usize;
    v___x_3661_ = lean_usize_sub(v___x_3659_, v___x_3660_);
    v___x_3662_ = lean_usize_land(v___x_3658_, v___x_3661_);
    v___x_3663_ = lean_array_uget_borrowed(v_buckets_3647_, v___x_3662_);
    leanh::lean_inc(v___x_3663_);
    v___x_3664_ = l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(
        v_inst_3642_,
        v_a_3645_,
        v_fallback_3646_,
        v___x_3663_,
    );
    return v___x_3664_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg___boxed(
    mut v_inst_3665_: *mut leanh::LeanObject,
    mut v_inst_3666_: *mut leanh::LeanObject,
    mut v_m_3667_: *mut leanh::LeanObject,
    mut v_a_3668_: *mut leanh::LeanObject,
    mut v_fallback_3669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3670_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(
        v_inst_3665_,
        v_inst_3666_,
        v_m_3667_,
        v_a_3668_,
        v_fallback_3669_,
    );
    leanh::lean_dec_ref(v_fallback_3669_);
    leanh::lean_dec_ref(v_m_3667_);
    return v_res_3670_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntryD(
    mut v_00_u03b1_3671_: *mut leanh::LeanObject,
    mut v_00_u03b2_3672_: *mut leanh::LeanObject,
    mut v_inst_3673_: *mut leanh::LeanObject,
    mut v_inst_3674_: *mut leanh::LeanObject,
    mut v_m_3675_: *mut leanh::LeanObject,
    mut v_a_3676_: *mut leanh::LeanObject,
    mut v_fallback_3677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3678_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(
        v_inst_3673_,
        v_inst_3674_,
        v_m_3675_,
        v_a_3676_,
        v_fallback_3677_,
    );
    return v___x_3678_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntryD___boxed(
    mut v_00_u03b1_3679_: *mut leanh::LeanObject,
    mut v_00_u03b2_3680_: *mut leanh::LeanObject,
    mut v_inst_3681_: *mut leanh::LeanObject,
    mut v_inst_3682_: *mut leanh::LeanObject,
    mut v_m_3683_: *mut leanh::LeanObject,
    mut v_a_3684_: *mut leanh::LeanObject,
    mut v_fallback_3685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3686_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD(
        v_00_u03b1_3679_,
        v_00_u03b2_3680_,
        v_inst_3681_,
        v_inst_3682_,
        v_m_3683_,
        v_a_3684_,
        v_fallback_3685_,
    );
    leanh::lean_dec_ref(v_fallback_3685_);
    leanh::lean_dec_ref(v_m_3683_);
    return v_res_3686_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(
    mut v_inst_3687_: *mut leanh::LeanObject,
    mut v_inst_3688_: *mut leanh::LeanObject,
    mut v_m_3689_: *mut leanh::LeanObject,
    mut v_a_3690_: *mut leanh::LeanObject,
    mut v_inst_3691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: u64 = 0;
    let mut v___x_3696_: u64 = 0;
    let mut v___x_3697_: u64 = 0;
    let mut v___x_3698_: u64 = 0;
    let mut v_fold_3699_: u64 = 0;
    let mut v___x_3700_: u64 = 0;
    let mut v___x_3701_: u64 = 0;
    let mut v___x_3702_: u64 = 0;
    let mut v___x_3703_: usize = 0;
    let mut v___x_3704_: usize = 0;
    let mut v___x_3705_: usize = 0;
    let mut v___x_3706_: usize = 0;
    let mut v___x_3707_: usize = 0;
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3692_ = leanh::lean_ctor_get(v_m_3689_, 1);
    v___x_3693_ = lean_array_get_size(v_buckets_3692_);
    leanh::lean_inc(v_a_3690_);
    v___x_3694_ = leanh::lean_apply_1(v_inst_3688_, v_a_3690_);
    v___x_3695_ = 32u64;
    v___x_3696_ = leanh::lean_unbox_uint64(v___x_3694_);
    v___x_3697_ = lean_uint64_shift_right(v___x_3696_, v___x_3695_);
    v___x_3698_ = leanh::lean_unbox_uint64(v___x_3694_);
    leanh::lean_dec_ref(v___x_3694_);
    v_fold_3699_ = lean_uint64_xor(v___x_3698_, v___x_3697_);
    v___x_3700_ = 16u64;
    v___x_3701_ = lean_uint64_shift_right(v_fold_3699_, v___x_3700_);
    v___x_3702_ = lean_uint64_xor(v_fold_3699_, v___x_3701_);
    v___x_3703_ = lean_uint64_to_usize(v___x_3702_);
    v___x_3704_ = lean_usize_of_nat(v___x_3693_);
    v___x_3705_ = 1usize;
    v___x_3706_ = lean_usize_sub(v___x_3704_, v___x_3705_);
    v___x_3707_ = lean_usize_land(v___x_3703_, v___x_3706_);
    v___x_3708_ = lean_array_uget_borrowed(v_buckets_3692_, v___x_3707_);
    leanh::lean_inc(v___x_3708_);
    v___x_3709_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(
        v_inst_3687_,
        v_a_3690_,
        v_inst_3691_,
        v___x_3708_,
    );
    return v___x_3709_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg___boxed(
    mut v_inst_3710_: *mut leanh::LeanObject,
    mut v_inst_3711_: *mut leanh::LeanObject,
    mut v_m_3712_: *mut leanh::LeanObject,
    mut v_a_3713_: *mut leanh::LeanObject,
    mut v_inst_3714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3715_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(
        v_inst_3710_,
        v_inst_3711_,
        v_m_3712_,
        v_a_3713_,
        v_inst_3714_,
    );
    leanh::lean_dec_ref(v_inst_3714_);
    leanh::lean_dec_ref(v_m_3712_);
    return v_res_3715_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21(
    mut v_00_u03b1_3716_: *mut leanh::LeanObject,
    mut v_00_u03b2_3717_: *mut leanh::LeanObject,
    mut v_inst_3718_: *mut leanh::LeanObject,
    mut v_inst_3719_: *mut leanh::LeanObject,
    mut v_m_3720_: *mut leanh::LeanObject,
    mut v_a_3721_: *mut leanh::LeanObject,
    mut v_inst_3722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3723_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(
        v_inst_3718_,
        v_inst_3719_,
        v_m_3720_,
        v_a_3721_,
        v_inst_3722_,
    );
    return v___x_3723_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___boxed(
    mut v_00_u03b1_3724_: *mut leanh::LeanObject,
    mut v_00_u03b2_3725_: *mut leanh::LeanObject,
    mut v_inst_3726_: *mut leanh::LeanObject,
    mut v_inst_3727_: *mut leanh::LeanObject,
    mut v_m_3728_: *mut leanh::LeanObject,
    mut v_a_3729_: *mut leanh::LeanObject,
    mut v_inst_3730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3731_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21(
        v_00_u03b1_3724_,
        v_00_u03b2_3725_,
        v_inst_3726_,
        v_inst_3727_,
        v_m_3728_,
        v_a_3729_,
        v_inst_3730_,
    );
    leanh::lean_dec_ref(v_inst_3730_);
    leanh::lean_dec_ref(v_m_3728_);
    return v_res_3731_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(
    mut v_inst_3732_: *mut leanh::LeanObject,
    mut v_inst_3733_: *mut leanh::LeanObject,
    mut v_m_3734_: *mut leanh::LeanObject,
    mut v_a_3735_: *mut leanh::LeanObject,
    mut v_fallback_3736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: u64 = 0;
    let mut v___x_3741_: u64 = 0;
    let mut v___x_3742_: u64 = 0;
    let mut v___x_3743_: u64 = 0;
    let mut v_fold_3744_: u64 = 0;
    let mut v___x_3745_: u64 = 0;
    let mut v___x_3746_: u64 = 0;
    let mut v___x_3747_: u64 = 0;
    let mut v___x_3748_: usize = 0;
    let mut v___x_3749_: usize = 0;
    let mut v___x_3750_: usize = 0;
    let mut v___x_3751_: usize = 0;
    let mut v___x_3752_: usize = 0;
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3737_ = leanh::lean_ctor_get(v_m_3734_, 1);
    v___x_3738_ = lean_array_get_size(v_buckets_3737_);
    leanh::lean_inc(v_a_3735_);
    v___x_3739_ = leanh::lean_apply_1(v_inst_3733_, v_a_3735_);
    v___x_3740_ = 32u64;
    v___x_3741_ = leanh::lean_unbox_uint64(v___x_3739_);
    v___x_3742_ = lean_uint64_shift_right(v___x_3741_, v___x_3740_);
    v___x_3743_ = leanh::lean_unbox_uint64(v___x_3739_);
    leanh::lean_dec_ref(v___x_3739_);
    v_fold_3744_ = lean_uint64_xor(v___x_3743_, v___x_3742_);
    v___x_3745_ = 16u64;
    v___x_3746_ = lean_uint64_shift_right(v_fold_3744_, v___x_3745_);
    v___x_3747_ = lean_uint64_xor(v_fold_3744_, v___x_3746_);
    v___x_3748_ = lean_uint64_to_usize(v___x_3747_);
    v___x_3749_ = lean_usize_of_nat(v___x_3738_);
    v___x_3750_ = 1usize;
    v___x_3751_ = lean_usize_sub(v___x_3749_, v___x_3750_);
    v___x_3752_ = lean_usize_land(v___x_3748_, v___x_3751_);
    v___x_3753_ = lean_array_uget_borrowed(v_buckets_3737_, v___x_3752_);
    leanh::lean_inc(v___x_3753_);
    v___x_3754_ = l_Std_DHashMap_Internal_AssocList_getCastD___redArg(
        v_inst_3732_,
        v_a_3735_,
        v_fallback_3736_,
        v___x_3753_,
    );
    return v___x_3754_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getD___redArg___boxed(
    mut v_inst_3755_: *mut leanh::LeanObject,
    mut v_inst_3756_: *mut leanh::LeanObject,
    mut v_m_3757_: *mut leanh::LeanObject,
    mut v_a_3758_: *mut leanh::LeanObject,
    mut v_fallback_3759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3760_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(
        v_inst_3755_,
        v_inst_3756_,
        v_m_3757_,
        v_a_3758_,
        v_fallback_3759_,
    );
    leanh::lean_dec(v_fallback_3759_);
    leanh::lean_dec_ref(v_m_3757_);
    return v_res_3760_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getD(
    mut v_00_u03b1_3761_: *mut leanh::LeanObject,
    mut v_00_u03b2_3762_: *mut leanh::LeanObject,
    mut v_inst_3763_: *mut leanh::LeanObject,
    mut v_inst_3764_: *mut leanh::LeanObject,
    mut v_inst_3765_: *mut leanh::LeanObject,
    mut v_m_3766_: *mut leanh::LeanObject,
    mut v_a_3767_: *mut leanh::LeanObject,
    mut v_fallback_3768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3769_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(
        v_inst_3763_,
        v_inst_3765_,
        v_m_3766_,
        v_a_3767_,
        v_fallback_3768_,
    );
    return v___x_3769_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getD___boxed(
    mut v_00_u03b1_3770_: *mut leanh::LeanObject,
    mut v_00_u03b2_3771_: *mut leanh::LeanObject,
    mut v_inst_3772_: *mut leanh::LeanObject,
    mut v_inst_3773_: *mut leanh::LeanObject,
    mut v_inst_3774_: *mut leanh::LeanObject,
    mut v_m_3775_: *mut leanh::LeanObject,
    mut v_a_3776_: *mut leanh::LeanObject,
    mut v_fallback_3777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3778_ = l_Std_DHashMap_Internal_Raw_u2080_getD(
        v_00_u03b1_3770_,
        v_00_u03b2_3771_,
        v_inst_3772_,
        v_inst_3773_,
        v_inst_3774_,
        v_m_3775_,
        v_a_3776_,
        v_fallback_3777_,
    );
    leanh::lean_dec(v_fallback_3777_);
    leanh::lean_dec_ref(v_m_3775_);
    return v_res_3778_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(
    mut v_inst_3779_: *mut leanh::LeanObject,
    mut v_inst_3780_: *mut leanh::LeanObject,
    mut v_m_3781_: *mut leanh::LeanObject,
    mut v_a_3782_: *mut leanh::LeanObject,
    mut v_inst_3783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: u64 = 0;
    let mut v___x_3788_: u64 = 0;
    let mut v___x_3789_: u64 = 0;
    let mut v___x_3790_: u64 = 0;
    let mut v_fold_3791_: u64 = 0;
    let mut v___x_3792_: u64 = 0;
    let mut v___x_3793_: u64 = 0;
    let mut v___x_3794_: u64 = 0;
    let mut v___x_3795_: usize = 0;
    let mut v___x_3796_: usize = 0;
    let mut v___x_3797_: usize = 0;
    let mut v___x_3798_: usize = 0;
    let mut v___x_3799_: usize = 0;
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3784_ = leanh::lean_ctor_get(v_m_3781_, 1);
    v___x_3785_ = lean_array_get_size(v_buckets_3784_);
    leanh::lean_inc(v_a_3782_);
    v___x_3786_ = leanh::lean_apply_1(v_inst_3780_, v_a_3782_);
    v___x_3787_ = 32u64;
    v___x_3788_ = leanh::lean_unbox_uint64(v___x_3786_);
    v___x_3789_ = lean_uint64_shift_right(v___x_3788_, v___x_3787_);
    v___x_3790_ = leanh::lean_unbox_uint64(v___x_3786_);
    leanh::lean_dec_ref(v___x_3786_);
    v_fold_3791_ = lean_uint64_xor(v___x_3790_, v___x_3789_);
    v___x_3792_ = 16u64;
    v___x_3793_ = lean_uint64_shift_right(v_fold_3791_, v___x_3792_);
    v___x_3794_ = lean_uint64_xor(v_fold_3791_, v___x_3793_);
    v___x_3795_ = lean_uint64_to_usize(v___x_3794_);
    v___x_3796_ = lean_usize_of_nat(v___x_3785_);
    v___x_3797_ = 1usize;
    v___x_3798_ = lean_usize_sub(v___x_3796_, v___x_3797_);
    v___x_3799_ = lean_usize_land(v___x_3795_, v___x_3798_);
    v___x_3800_ = lean_array_uget_borrowed(v_buckets_3784_, v___x_3799_);
    leanh::lean_inc(v___x_3800_);
    v___x_3801_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg(
        v_inst_3779_,
        v_a_3782_,
        v_inst_3783_,
        v___x_3800_,
    );
    return v___x_3801_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___boxed(
    mut v_inst_3802_: *mut leanh::LeanObject,
    mut v_inst_3803_: *mut leanh::LeanObject,
    mut v_m_3804_: *mut leanh::LeanObject,
    mut v_a_3805_: *mut leanh::LeanObject,
    mut v_inst_3806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3807_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(
        v_inst_3802_,
        v_inst_3803_,
        v_m_3804_,
        v_a_3805_,
        v_inst_3806_,
    );
    leanh::lean_dec(v_inst_3806_);
    leanh::lean_dec_ref(v_m_3804_);
    return v_res_3807_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x21(
    mut v_00_u03b1_3808_: *mut leanh::LeanObject,
    mut v_00_u03b2_3809_: *mut leanh::LeanObject,
    mut v_inst_3810_: *mut leanh::LeanObject,
    mut v_inst_3811_: *mut leanh::LeanObject,
    mut v_inst_3812_: *mut leanh::LeanObject,
    mut v_m_3813_: *mut leanh::LeanObject,
    mut v_a_3814_: *mut leanh::LeanObject,
    mut v_inst_3815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3816_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(
        v_inst_3810_,
        v_inst_3812_,
        v_m_3813_,
        v_a_3814_,
        v_inst_3815_,
    );
    return v___x_3816_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_get_x21___boxed(
    mut v_00_u03b1_3817_: *mut leanh::LeanObject,
    mut v_00_u03b2_3818_: *mut leanh::LeanObject,
    mut v_inst_3819_: *mut leanh::LeanObject,
    mut v_inst_3820_: *mut leanh::LeanObject,
    mut v_inst_3821_: *mut leanh::LeanObject,
    mut v_m_3822_: *mut leanh::LeanObject,
    mut v_a_3823_: *mut leanh::LeanObject,
    mut v_inst_3824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3825_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21(
        v_00_u03b1_3817_,
        v_00_u03b2_3818_,
        v_inst_3819_,
        v_inst_3820_,
        v_inst_3821_,
        v_m_3822_,
        v_a_3823_,
        v_inst_3824_,
    );
    leanh::lean_dec(v_inst_3824_);
    leanh::lean_dec_ref(v_m_3822_);
    return v_res_3825_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
    mut v_inst_3826_: *mut leanh::LeanObject,
    mut v_inst_3827_: *mut leanh::LeanObject,
    mut v_m_3828_: *mut leanh::LeanObject,
    mut v_a_3829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: u64 = 0;
    let mut v___x_3835_: u64 = 0;
    let mut v___x_3836_: u64 = 0;
    let mut v___x_3837_: u64 = 0;
    let mut v_fold_3838_: u64 = 0;
    let mut v___x_3839_: u64 = 0;
    let mut v___x_3840_: u64 = 0;
    let mut v___x_3841_: u64 = 0;
    let mut v___x_3842_: usize = 0;
    let mut v___x_3843_: usize = 0;
    let mut v___x_3844_: usize = 0;
    let mut v___x_3845_: usize = 0;
    let mut v___x_3846_: usize = 0;
    let mut v_bkt_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3851_: u8 = 0;
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut v_unused_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3830_ = leanh::lean_ctor_get(v_m_3828_, 0);
                v_buckets_3831_ = leanh::lean_ctor_get(v_m_3828_, 1);
                v___x_3832_ = lean_array_get_size(v_buckets_3831_);
                leanh::lean_inc_n(v_a_3829_, 2);
                v___x_3833_ = leanh::lean_apply_1(v_inst_3827_, v_a_3829_);
                v___x_3834_ = 32u64;
                v___x_3835_ = leanh::lean_unbox_uint64(v___x_3833_);
                v___x_3836_ = lean_uint64_shift_right(v___x_3835_, v___x_3834_);
                v___x_3837_ = leanh::lean_unbox_uint64(v___x_3833_);
                leanh::lean_dec_ref(v___x_3833_);
                v_fold_3838_ = lean_uint64_xor(v___x_3837_, v___x_3836_);
                v___x_3839_ = 16u64;
                v___x_3840_ = lean_uint64_shift_right(v_fold_3838_, v___x_3839_);
                v___x_3841_ = lean_uint64_xor(v_fold_3838_, v___x_3840_);
                v___x_3842_ = lean_uint64_to_usize(v___x_3841_);
                v___x_3843_ = lean_usize_of_nat(v___x_3832_);
                v___x_3844_ = 1usize;
                v___x_3845_ = lean_usize_sub(v___x_3843_, v___x_3844_);
                v___x_3846_ = lean_usize_land(v___x_3842_, v___x_3845_);
                v_bkt_3847_ = lean_array_uget_borrowed(v_buckets_3831_, v___x_3846_);
                leanh::lean_inc(v_bkt_3847_);
                leanh::lean_inc_ref(v_inst_3826_);
                v___x_3848_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_inst_3826_,
                    v_a_3829_,
                    v_bkt_3847_,
                );
                if v___x_3848_ == 0 {
                    leanh::lean_dec(v_a_3829_);
                    leanh::lean_dec_ref(v_inst_3826_);
                    return v_m_3828_;
                } else {
                    leanh::lean_inc(v_bkt_3847_);
                    leanh::lean_inc_ref(v_buckets_3831_);
                    leanh::lean_inc(v_size_3830_);
                    v_isSharedCheck_3861_ = (!leanh::lean_is_exclusive(v_m_3828_)) as u8;
                    if v_isSharedCheck_3861_ == 0 {
                        v_unused_3862_ = leanh::lean_ctor_get(v_m_3828_, 1);
                        leanh::lean_dec(v_unused_3862_);
                        v_unused_3863_ = leanh::lean_ctor_get(v_m_3828_, 0);
                        leanh::lean_dec(v_unused_3863_);
                        v___x_3850_ = v_m_3828_;
                        v_isShared_3851_ = v_isSharedCheck_3861_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_3828_);
                        v___x_3850_ = leanh::lean_box(0);
                        v_isShared_3851_ = v_isSharedCheck_3861_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3852_ = leanh::lean_box(0);
                v_buckets_x27_3853_ = lean_array_uset(v_buckets_3831_, v___x_3846_, v___x_3852_);
                v___x_3854_ = leanh::lean_unsigned_to_nat(1);
                v___x_3855_ = lean_nat_sub(v_size_3830_, v___x_3854_);
                leanh::lean_dec(v_size_3830_);
                v___x_3856_ = l_Std_DHashMap_Internal_AssocList_erase___redArg(
                    v_inst_3826_,
                    v_a_3829_,
                    v_bkt_3847_,
                );
                v___x_3857_ = lean_array_uset(v_buckets_x27_3853_, v___x_3846_, v___x_3856_);
                if v_isShared_3851_ == 0 {
                    leanh::lean_ctor_set(v___x_3850_, 1, v___x_3857_);
                    leanh::lean_ctor_set(v___x_3850_, 0, v___x_3855_);
                    v___x_3859_ = v___x_3850_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3860_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3855_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 1, v___x_3857_);
                    v___x_3859_ = v_reuseFailAlloc_3860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase(
    mut v_00_u03b1_3864_: *mut leanh::LeanObject,
    mut v_00_u03b2_3865_: *mut leanh::LeanObject,
    mut v_inst_3866_: *mut leanh::LeanObject,
    mut v_inst_3867_: *mut leanh::LeanObject,
    mut v_m_3868_: *mut leanh::LeanObject,
    mut v_a_3869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3870_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_inst_3866_,
        v_inst_3867_,
        v_m_3868_,
        v_a_3869_,
    );
    return v___x_3870_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg___lam__0(
    mut v_f_3871_: *mut leanh::LeanObject,
    mut v_x_3872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3873_ = leanh::lean_box(0);
    v___x_3874_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v_f_3871_, v___x_3873_, v_x_3872_);
    return v___x_3874_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(
    mut v_f_3875_: *mut leanh::LeanObject,
    mut v_m_3876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3880_: u8 = 0;
    let mut v___f_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3883_: usize = 0;
    let mut v___x_3884_: usize = 0;
    let mut v_newBuckets_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: u8 = 0;
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: u8 = 0;
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: usize = 0;
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: usize = 0;
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3907_: u8 = 0;
    let mut v_unused_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3877_ = leanh::lean_ctor_get(v_m_3876_, 1);
                v_isSharedCheck_3907_ = (!leanh::lean_is_exclusive(v_m_3876_)) as u8;
                if v_isSharedCheck_3907_ == 0 {
                    v_unused_3908_ = leanh::lean_ctor_get(v_m_3876_, 0);
                    leanh::lean_dec(v_unused_3908_);
                    v___x_3879_ = v_m_3876_;
                    v_isShared_3880_ = v_isSharedCheck_3907_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3877_);
                    leanh::lean_dec(v_m_3876_);
                    v___x_3879_ = leanh::lean_box(0);
                    v_isShared_3880_ = v_isSharedCheck_3907_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_3881_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg___lam__0
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3881_, 0, v_f_3875_);
                v___x_3882_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__9;
                v_sz_3883_ = lean_array_size(v_buckets_3877_);
                v___x_3884_ = 0usize;
                v_newBuckets_3885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3882_,
                    v___f_3881_,
                    v_sz_3883_,
                    v___x_3884_,
                    v_buckets_3877_,
                );
                v___x_3886_ = leanh::lean_unsigned_to_nat(0);
                v___x_3887_ = lean_array_get_size(v_newBuckets_3885_);
                v___x_3888_ = lean_nat_dec_lt(v___x_3886_, v___x_3887_);
                if v___x_3888_ == 0 {
                    if v_isShared_3880_ == 0 {
                        leanh::lean_ctor_set(v___x_3879_, 1, v_newBuckets_3885_);
                        leanh::lean_ctor_set(v___x_3879_, 0, v___x_3886_);
                        v___x_3890_ = v___x_3879_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3891_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3886_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_newBuckets_3885_);
                        v___x_3890_ = v_reuseFailAlloc_3891_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___f_3892_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__10;
                    v___x_3893_ = lean_nat_dec_le(v___x_3887_, v___x_3887_);
                    if v___x_3893_ == 0 {
                        if v___x_3888_ == 0 {
                            if v_isShared_3880_ == 0 {
                                leanh::lean_ctor_set(v___x_3879_, 1, v_newBuckets_3885_);
                                leanh::lean_ctor_set(v___x_3879_, 0, v___x_3886_);
                                v___x_3895_ = v___x_3879_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3896_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3886_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3896_,
                                    1,
                                    v_newBuckets_3885_,
                                );
                                v___x_3895_ = v_reuseFailAlloc_3896_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___x_3897_ = lean_usize_of_nat(v___x_3887_);
                            leanh::lean_inc(v_newBuckets_3885_);
                            v___x_3898_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_3882_,
                                    v___f_3892_,
                                    v_newBuckets_3885_,
                                    v___x_3884_,
                                    v___x_3897_,
                                    v___x_3886_,
                                );
                            if v_isShared_3880_ == 0 {
                                leanh::lean_ctor_set(v___x_3879_, 1, v_newBuckets_3885_);
                                leanh::lean_ctor_set(v___x_3879_, 0, v___x_3898_);
                                v___x_3900_ = v___x_3879_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3901_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3898_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3901_,
                                    1,
                                    v_newBuckets_3885_,
                                );
                                v___x_3900_ = v_reuseFailAlloc_3901_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v___x_3902_ = lean_usize_of_nat(v___x_3887_);
                        leanh::lean_inc(v_newBuckets_3885_);
                        v___x_3903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_3882_,
                            v___f_3892_,
                            v_newBuckets_3885_,
                            v___x_3884_,
                            v___x_3902_,
                            v___x_3886_,
                        );
                        if v_isShared_3880_ == 0 {
                            leanh::lean_ctor_set(v___x_3879_, 1, v_newBuckets_3885_);
                            leanh::lean_ctor_set(v___x_3879_, 0, v___x_3903_);
                            v___x_3905_ = v___x_3879_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3906_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3903_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3906_,
                                1,
                                v_newBuckets_3885_,
                            );
                            v___x_3905_ = v_reuseFailAlloc_3906_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3890_;
            }
            3 => {
                return v___x_3895_;
            }
            4 => {
                return v___x_3900_;
            }
            5 => {
                return v___x_3905_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filterMap(
    mut v_00_u03b1_3909_: *mut leanh::LeanObject,
    mut v_00_u03b2_3910_: *mut leanh::LeanObject,
    mut v_00_u03b3_3911_: *mut leanh::LeanObject,
    mut v_f_3912_: *mut leanh::LeanObject,
    mut v_m_3913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3914_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_3912_, v_m_3913_);
    return v___x_3914_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_map___redArg___lam__0(
    mut v_f_3915_: *mut leanh::LeanObject,
    mut v_x_3916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3917_ = leanh::lean_box(0);
    v___x_3918_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v_f_3915_, v___x_3917_, v_x_3916_);
    return v___x_3918_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_map___redArg(
    mut v_f_3919_: *mut leanh::LeanObject,
    mut v_m_3920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3925_: u8 = 0;
    let mut v___f_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3928_: usize = 0;
    let mut v___x_3929_: usize = 0;
    let mut v_newBuckets_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3921_ = leanh::lean_ctor_get(v_m_3920_, 0);
                v_buckets_3922_ = leanh::lean_ctor_get(v_m_3920_, 1);
                v_isSharedCheck_3934_ = (!leanh::lean_is_exclusive(v_m_3920_)) as u8;
                if v_isSharedCheck_3934_ == 0 {
                    v___x_3924_ = v_m_3920_;
                    v_isShared_3925_ = v_isSharedCheck_3934_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3922_);
                    leanh::lean_inc(v_size_3921_);
                    leanh::lean_dec(v_m_3920_);
                    v___x_3924_ = leanh::lean_box(0);
                    v_isShared_3925_ = v_isSharedCheck_3934_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_3926_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_map___redArg___lam__0
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3926_, 0, v_f_3919_);
                v___x_3927_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__9;
                v_sz_3928_ = lean_array_size(v_buckets_3922_);
                v___x_3929_ = 0usize;
                v_newBuckets_3930_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3927_,
                    v___f_3926_,
                    v_sz_3928_,
                    v___x_3929_,
                    v_buckets_3922_,
                );
                if v_isShared_3925_ == 0 {
                    leanh::lean_ctor_set(v___x_3924_, 1, v_newBuckets_3930_);
                    v___x_3932_ = v___x_3924_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3933_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_size_3921_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3933_, 1, v_newBuckets_3930_);
                    v___x_3932_ = v_reuseFailAlloc_3933_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_map(
    mut v_00_u03b1_3935_: *mut leanh::LeanObject,
    mut v_00_u03b2_3936_: *mut leanh::LeanObject,
    mut v_00_u03b3_3937_: *mut leanh::LeanObject,
    mut v_f_3938_: *mut leanh::LeanObject,
    mut v_m_3939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3940_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_3938_, v_m_3939_);
    return v___x_3940_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filter___redArg___lam__0(
    mut v_f_3941_: *mut leanh::LeanObject,
    mut v_x_3942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3943_ = leanh::lean_box(0);
    v___x_3944_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go(leanh::lean_box(0), leanh::lean_box(0), v_f_3941_, v___x_3943_, v_x_3942_);
    return v___x_3944_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(
    mut v_f_3945_: *mut leanh::LeanObject,
    mut v_m_3946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3950_: u8 = 0;
    let mut v___f_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3953_: usize = 0;
    let mut v___x_3954_: usize = 0;
    let mut v_newBuckets_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: u8 = 0;
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: u8 = 0;
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: usize = 0;
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: usize = 0;
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3977_: u8 = 0;
    let mut v_unused_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3947_ = leanh::lean_ctor_get(v_m_3946_, 1);
                v_isSharedCheck_3977_ = (!leanh::lean_is_exclusive(v_m_3946_)) as u8;
                if v_isSharedCheck_3977_ == 0 {
                    v_unused_3978_ = leanh::lean_ctor_get(v_m_3946_, 0);
                    leanh::lean_dec(v_unused_3978_);
                    v___x_3949_ = v_m_3946_;
                    v_isShared_3950_ = v_isSharedCheck_3977_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3947_);
                    leanh::lean_dec(v_m_3946_);
                    v___x_3949_ = leanh::lean_box(0);
                    v_isShared_3950_ = v_isSharedCheck_3977_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_3951_ = leanh::lean_alloc_closure(
                    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg___lam__0
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3951_, 0, v_f_3945_);
                v___x_3952_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__9;
                v_sz_3953_ = lean_array_size(v_buckets_3947_);
                v___x_3954_ = 0usize;
                v_newBuckets_3955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3952_,
                    v___f_3951_,
                    v_sz_3953_,
                    v___x_3954_,
                    v_buckets_3947_,
                );
                v___x_3956_ = leanh::lean_unsigned_to_nat(0);
                v___x_3957_ = lean_array_get_size(v_newBuckets_3955_);
                v___x_3958_ = lean_nat_dec_lt(v___x_3956_, v___x_3957_);
                if v___x_3958_ == 0 {
                    if v_isShared_3950_ == 0 {
                        leanh::lean_ctor_set(v___x_3949_, 1, v_newBuckets_3955_);
                        leanh::lean_ctor_set(v___x_3949_, 0, v___x_3956_);
                        v___x_3960_ = v___x_3949_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3961_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3956_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_newBuckets_3955_);
                        v___x_3960_ = v_reuseFailAlloc_3961_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___f_3962_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__10;
                    v___x_3963_ = lean_nat_dec_le(v___x_3957_, v___x_3957_);
                    if v___x_3963_ == 0 {
                        if v___x_3958_ == 0 {
                            if v_isShared_3950_ == 0 {
                                leanh::lean_ctor_set(v___x_3949_, 1, v_newBuckets_3955_);
                                leanh::lean_ctor_set(v___x_3949_, 0, v___x_3956_);
                                v___x_3965_ = v___x_3949_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3966_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3956_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3966_,
                                    1,
                                    v_newBuckets_3955_,
                                );
                                v___x_3965_ = v_reuseFailAlloc_3966_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___x_3967_ = lean_usize_of_nat(v___x_3957_);
                            leanh::lean_inc(v_newBuckets_3955_);
                            v___x_3968_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_3952_,
                                    v___f_3962_,
                                    v_newBuckets_3955_,
                                    v___x_3954_,
                                    v___x_3967_,
                                    v___x_3956_,
                                );
                            if v_isShared_3950_ == 0 {
                                leanh::lean_ctor_set(v___x_3949_, 1, v_newBuckets_3955_);
                                leanh::lean_ctor_set(v___x_3949_, 0, v___x_3968_);
                                v___x_3970_ = v___x_3949_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3971_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3968_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3971_,
                                    1,
                                    v_newBuckets_3955_,
                                );
                                v___x_3970_ = v_reuseFailAlloc_3971_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v___x_3972_ = lean_usize_of_nat(v___x_3957_);
                        leanh::lean_inc(v_newBuckets_3955_);
                        v___x_3973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_3952_,
                            v___f_3962_,
                            v_newBuckets_3955_,
                            v___x_3954_,
                            v___x_3972_,
                            v___x_3956_,
                        );
                        if v_isShared_3950_ == 0 {
                            leanh::lean_ctor_set(v___x_3949_, 1, v_newBuckets_3955_);
                            leanh::lean_ctor_set(v___x_3949_, 0, v___x_3973_);
                            v___x_3975_ = v___x_3949_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3976_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3973_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3976_,
                                1,
                                v_newBuckets_3955_,
                            );
                            v___x_3975_ = v_reuseFailAlloc_3976_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3960_;
            }
            3 => {
                return v___x_3965_;
            }
            4 => {
                return v___x_3970_;
            }
            5 => {
                return v___x_3975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filter(
    mut v_00_u03b1_3979_: *mut leanh::LeanObject,
    mut v_00_u03b2_3980_: *mut leanh::LeanObject,
    mut v_f_3981_: *mut leanh::LeanObject,
    mut v_m_3982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3983_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_3981_, v_m_3982_);
    return v___x_3983_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg___lam__0(
    mut v_inst_3984_: *mut leanh::LeanObject,
    mut v_inst_3985_: *mut leanh::LeanObject,
    mut v_x_3986_: *mut leanh::LeanObject,
    mut v_____s_3987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_3988_ = leanh::lean_ctor_get(v_x_3986_, 0);
    leanh::lean_inc(v_fst_3988_);
    v_snd_3989_ = leanh::lean_ctor_get(v_x_3986_, 1);
    leanh::lean_inc(v_snd_3989_);
    leanh::lean_dec_ref(v_x_3986_);
    v_r_3990_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_inst_3984_,
        v_inst_3985_,
        v_____s_3987_,
        v_fst_3988_,
        v_snd_3989_,
    );
    v___x_3991_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3991_, 0, v_r_3990_);
    return v___x_3991_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
    mut v_inst_3992_: *mut leanh::LeanObject,
    mut v_inst_3993_: *mut leanh::LeanObject,
    mut v_inst_3994_: *mut leanh::LeanObject,
    mut v_m_3995_: *mut leanh::LeanObject,
    mut v_l_3996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3997_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_3997_, 0, v_inst_3993_);
    leanh::lean_closure_set(v___f_3997_, 1, v_inst_3994_);
    v___x_3998_ = leanh::lean_apply_4(
        v_inst_3992_,
        leanh::lean_box(0),
        v_l_3996_,
        v_m_3995_,
        v___f_3997_,
    );
    return v___x_3998_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertMany(
    mut v_00_u03b1_3999_: *mut leanh::LeanObject,
    mut v_00_u03b2_4000_: *mut leanh::LeanObject,
    mut v_00_u03c1_4001_: *mut leanh::LeanObject,
    mut v_inst_4002_: *mut leanh::LeanObject,
    mut v_inst_4003_: *mut leanh::LeanObject,
    mut v_inst_4004_: *mut leanh::LeanObject,
    mut v_m_4005_: *mut leanh::LeanObject,
    mut v_l_4006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4007_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
        v_inst_4002_,
        v_inst_4003_,
        v_inst_4004_,
        v_m_4005_,
        v_l_4006_,
    );
    return v___x_4007_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg___lam__0(
    mut v_inst_4008_: *mut leanh::LeanObject,
    mut v_inst_4009_: *mut leanh::LeanObject,
    mut v_x_4010_: *mut leanh::LeanObject,
    mut v_____s_4011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_4012_ = leanh::lean_ctor_get(v_x_4010_, 0);
    leanh::lean_inc(v_fst_4012_);
    leanh::lean_dec_ref(v_x_4010_);
    v_r_4013_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_inst_4008_,
        v_inst_4009_,
        v_____s_4011_,
        v_fst_4012_,
    );
    v___x_4014_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4014_, 0, v_r_4013_);
    return v___x_4014_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
    mut v_inst_4015_: *mut leanh::LeanObject,
    mut v_inst_4016_: *mut leanh::LeanObject,
    mut v_inst_4017_: *mut leanh::LeanObject,
    mut v_m_4018_: *mut leanh::LeanObject,
    mut v_l_4019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4020_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_4020_, 0, v_inst_4016_);
    leanh::lean_closure_set(v___f_4020_, 1, v_inst_4017_);
    v___x_4021_ = leanh::lean_apply_4(
        v_inst_4015_,
        leanh::lean_box(0),
        v_l_4019_,
        v_m_4018_,
        v___f_4020_,
    );
    return v___x_4021_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries(
    mut v_00_u03b1_4022_: *mut leanh::LeanObject,
    mut v_00_u03b2_4023_: *mut leanh::LeanObject,
    mut v_00_u03c1_4024_: *mut leanh::LeanObject,
    mut v_inst_4025_: *mut leanh::LeanObject,
    mut v_inst_4026_: *mut leanh::LeanObject,
    mut v_inst_4027_: *mut leanh::LeanObject,
    mut v_m_4028_: *mut leanh::LeanObject,
    mut v_l_4029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4030_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
        v_inst_4025_,
        v_inst_4026_,
        v_inst_4027_,
        v_m_4028_,
        v_l_4029_,
    );
    return v___x_4030_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg___lam__0(
    mut v_inst_4031_: *mut leanh::LeanObject,
    mut v_inst_4032_: *mut leanh::LeanObject,
    mut v_x_4033_: *mut leanh::LeanObject,
    mut v_____s_4034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_4035_ = leanh::lean_ctor_get(v_x_4033_, 0);
    leanh::lean_inc(v_fst_4035_);
    v_snd_4036_ = leanh::lean_ctor_get(v_x_4033_, 1);
    leanh::lean_inc(v_snd_4036_);
    leanh::lean_dec_ref(v_x_4033_);
    v_r_4037_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_4031_,
        v_inst_4032_,
        v_____s_4034_,
        v_fst_4035_,
        v_snd_4036_,
    );
    v___x_4038_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4038_, 0, v_r_4037_);
    return v___x_4038_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg(
    mut v_inst_4039_: *mut leanh::LeanObject,
    mut v_inst_4040_: *mut leanh::LeanObject,
    mut v_inst_4041_: *mut leanh::LeanObject,
    mut v_m_4042_: *mut leanh::LeanObject,
    mut v_l_4043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4044_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_4044_, 0, v_inst_4040_);
    leanh::lean_closure_set(v___f_4044_, 1, v_inst_4041_);
    v___x_4045_ = leanh::lean_apply_4(
        v_inst_4039_,
        leanh::lean_box(0),
        v_l_4043_,
        v_m_4042_,
        v___f_4044_,
    );
    return v___x_4045_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew(
    mut v_00_u03b1_4046_: *mut leanh::LeanObject,
    mut v_00_u03b2_4047_: *mut leanh::LeanObject,
    mut v_00_u03c1_4048_: *mut leanh::LeanObject,
    mut v_inst_4049_: *mut leanh::LeanObject,
    mut v_inst_4050_: *mut leanh::LeanObject,
    mut v_inst_4051_: *mut leanh::LeanObject,
    mut v_m_4052_: *mut leanh::LeanObject,
    mut v_l_4053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4054_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_4054_, 0, v_inst_4050_);
    leanh::lean_closure_set(v___f_4054_, 1, v_inst_4051_);
    v___x_4055_ = leanh::lean_apply_4(
        v_inst_4049_,
        leanh::lean_box(0),
        v_l_4053_,
        v_m_4052_,
        v___f_4054_,
    );
    return v___x_4055_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg(
    mut v_inst_4056_: *mut leanh::LeanObject,
    mut v_inst_4057_: *mut leanh::LeanObject,
    mut v_m_4058_: *mut leanh::LeanObject,
    mut v_sofar_4059_: *mut leanh::LeanObject,
    mut v_k_4060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_4057_);
    leanh::lean_inc_ref(v_inst_4056_);
    v___x_4061_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(
        v_inst_4056_,
        v_inst_4057_,
        v_m_4058_,
        v_k_4060_,
    );
    if leanh::lean_obj_tag(v___x_4061_) == 0 {
        leanh::lean_dec_ref(v_inst_4057_);
        leanh::lean_dec_ref(v_inst_4056_);
        return v_sofar_4059_;
    } else {
        let mut v_val_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4062_ = leanh::lean_ctor_get(v___x_4061_, 0);
        leanh::lean_inc(v_val_4062_);
        leanh::lean_dec_ref_known(v___x_4061_, 1);
        v_fst_4063_ = leanh::lean_ctor_get(v_val_4062_, 0);
        leanh::lean_inc(v_fst_4063_);
        v_snd_4064_ = leanh::lean_ctor_get(v_val_4062_, 1);
        leanh::lean_inc(v_snd_4064_);
        leanh::lean_dec(v_val_4062_);
        v___x_4065_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
            v_inst_4056_,
            v_inst_4057_,
            v_sofar_4059_,
            v_fst_4063_,
            v_snd_4064_,
        );
        return v___x_4065_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg___boxed(
    mut v_inst_4066_: *mut leanh::LeanObject,
    mut v_inst_4067_: *mut leanh::LeanObject,
    mut v_m_4068_: *mut leanh::LeanObject,
    mut v_sofar_4069_: *mut leanh::LeanObject,
    mut v_k_4070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4071_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg(
        v_inst_4066_,
        v_inst_4067_,
        v_m_4068_,
        v_sofar_4069_,
        v_k_4070_,
    );
    leanh::lean_dec_ref(v_m_4068_);
    return v_res_4071_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn(
    mut v_00_u03b1_4072_: *mut leanh::LeanObject,
    mut v_00_u03b2_4073_: *mut leanh::LeanObject,
    mut v_inst_4074_: *mut leanh::LeanObject,
    mut v_inst_4075_: *mut leanh::LeanObject,
    mut v_m_4076_: *mut leanh::LeanObject,
    mut v_sofar_4077_: *mut leanh::LeanObject,
    mut v_k_4078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_4075_);
    leanh::lean_inc_ref(v_inst_4074_);
    v___x_4079_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(
        v_inst_4074_,
        v_inst_4075_,
        v_m_4076_,
        v_k_4078_,
    );
    if leanh::lean_obj_tag(v___x_4079_) == 0 {
        leanh::lean_dec_ref(v_inst_4075_);
        leanh::lean_dec_ref(v_inst_4074_);
        return v_sofar_4077_;
    } else {
        let mut v_val_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4080_ = leanh::lean_ctor_get(v___x_4079_, 0);
        leanh::lean_inc(v_val_4080_);
        leanh::lean_dec_ref_known(v___x_4079_, 1);
        v_fst_4081_ = leanh::lean_ctor_get(v_val_4080_, 0);
        leanh::lean_inc(v_fst_4081_);
        v_snd_4082_ = leanh::lean_ctor_get(v_val_4080_, 1);
        leanh::lean_inc(v_snd_4082_);
        leanh::lean_dec(v_val_4080_);
        v___x_4083_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
            v_inst_4074_,
            v_inst_4075_,
            v_sofar_4077_,
            v_fst_4081_,
            v_snd_4082_,
        );
        return v___x_4083_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___boxed(
    mut v_00_u03b1_4084_: *mut leanh::LeanObject,
    mut v_00_u03b2_4085_: *mut leanh::LeanObject,
    mut v_inst_4086_: *mut leanh::LeanObject,
    mut v_inst_4087_: *mut leanh::LeanObject,
    mut v_m_4088_: *mut leanh::LeanObject,
    mut v_sofar_4089_: *mut leanh::LeanObject,
    mut v_k_4090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4091_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn(
        v_00_u03b1_4084_,
        v_00_u03b2_4085_,
        v_inst_4086_,
        v_inst_4087_,
        v_m_4088_,
        v_sofar_4089_,
        v_k_4090_,
    );
    leanh::lean_dec_ref(v_m_4088_);
    return v_res_4091_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0(
    mut v_inst_4092_: *mut leanh::LeanObject,
    mut v_inst_4093_: *mut leanh::LeanObject,
    mut v_m_u2081_4094_: *mut leanh::LeanObject,
    mut v_x1_4095_: *mut leanh::LeanObject,
    mut v_x2_4096_: *mut leanh::LeanObject,
    mut v_x3_4097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_4093_);
    leanh::lean_inc_ref(v_inst_4092_);
    v___x_4098_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(
        v_inst_4092_,
        v_inst_4093_,
        v_m_u2081_4094_,
        v_x2_4096_,
    );
    if leanh::lean_obj_tag(v___x_4098_) == 0 {
        leanh::lean_dec_ref(v_inst_4093_);
        leanh::lean_dec_ref(v_inst_4092_);
        return v_x1_4095_;
    } else {
        let mut v_val_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4099_ = leanh::lean_ctor_get(v___x_4098_, 0);
        leanh::lean_inc(v_val_4099_);
        leanh::lean_dec_ref_known(v___x_4098_, 1);
        v_fst_4100_ = leanh::lean_ctor_get(v_val_4099_, 0);
        leanh::lean_inc(v_fst_4100_);
        v_snd_4101_ = leanh::lean_ctor_get(v_val_4099_, 1);
        leanh::lean_inc(v_snd_4101_);
        leanh::lean_dec(v_val_4099_);
        v___x_4102_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
            v_inst_4092_,
            v_inst_4093_,
            v_x1_4095_,
            v_fst_4100_,
            v_snd_4101_,
        );
        return v___x_4102_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0___boxed(
    mut v_inst_4103_: *mut leanh::LeanObject,
    mut v_inst_4104_: *mut leanh::LeanObject,
    mut v_m_u2081_4105_: *mut leanh::LeanObject,
    mut v_x1_4106_: *mut leanh::LeanObject,
    mut v_x2_4107_: *mut leanh::LeanObject,
    mut v_x3_4108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4109_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0(
        v_inst_4103_,
        v_inst_4104_,
        v_m_u2081_4105_,
        v_x1_4106_,
        v_x2_4107_,
        v_x3_4108_,
    );
    leanh::lean_dec(v_x3_4108_);
    leanh::lean_dec_ref(v_m_u2081_4105_);
    return v_res_4109_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__1(
    mut v___x_4110_: *mut leanh::LeanObject,
    mut v___f_4111_: *mut leanh::LeanObject,
    mut v_acc_4112_: *mut leanh::LeanObject,
    mut v_l_4113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4114_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_4110_,
        v___f_4111_,
        v_acc_4112_,
        v_l_4113_,
    );
    return v___x_4114_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4115_ = leanh::lean_box(0);
    v___x_4116_ = leanh::lean_unsigned_to_nat(16);
    v___x_4117_ = lean_mk_array(v___x_4116_, v___x_4115_);
    return v___x_4117_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4118_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0_once
        ),
        _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0,
    );
    v___x_4119_ = leanh::lean_unsigned_to_nat(0);
    v___x_4120_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4120_, 0, v___x_4119_);
    leanh::lean_ctor_set(v___x_4120_, 1, v___x_4118_);
    return v___x_4120_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg(
    mut v_inst_4121_: *mut leanh::LeanObject,
    mut v_inst_4122_: *mut leanh::LeanObject,
    mut v_m_u2081_4123_: *mut leanh::LeanObject,
    mut v_m_u2082_4124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: u8 = 0;
    v___x_4125_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__9;
    v_buckets_4126_ = leanh::lean_ctor_get(v_m_u2082_4124_, 1);
    leanh::lean_inc_ref(v_buckets_4126_);
    leanh::lean_dec_ref(v_m_u2082_4124_);
    v___x_4127_ = leanh::lean_unsigned_to_nat(0);
    v___x_4128_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1_once
        ),
        _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1,
    );
    v___x_4129_ = lean_array_get_size(v_buckets_4126_);
    v___x_4130_ = lean_nat_dec_lt(v___x_4127_, v___x_4129_);
    if v___x_4130_ == 0 {
        leanh::lean_dec_ref(v_buckets_4126_);
        leanh::lean_dec_ref(v_m_u2081_4123_);
        leanh::lean_dec_ref(v_inst_4122_);
        leanh::lean_dec_ref(v_inst_4121_);
        return v___x_4128_;
    } else {
        let mut v___f_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4133_: u8 = 0;
        v___f_4131_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            3,
        );
        leanh::lean_closure_set(v___f_4131_, 0, v_inst_4121_);
        leanh::lean_closure_set(v___f_4131_, 1, v_inst_4122_);
        leanh::lean_closure_set(v___f_4131_, 2, v_m_u2081_4123_);
        v___f_4132_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__1
                as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_4132_, 0, v___x_4125_);
        leanh::lean_closure_set(v___f_4132_, 1, v___f_4131_);
        v___x_4133_ = lean_nat_dec_le(v___x_4129_, v___x_4129_);
        if v___x_4133_ == 0 {
            if v___x_4130_ == 0 {
                leanh::lean_dec_ref(v___f_4132_);
                leanh::lean_dec_ref(v_buckets_4126_);
                return v___x_4128_;
            } else {
                let mut v___x_4134_: usize = 0;
                let mut v___x_4135_: usize = 0;
                let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4134_ = 0usize;
                v___x_4135_ = lean_usize_of_nat(v___x_4129_);
                v___x_4136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4125_,
                    v___f_4132_,
                    v_buckets_4126_,
                    v___x_4134_,
                    v___x_4135_,
                    v___x_4128_,
                );
                return v___x_4136_;
            }
        } else {
            let mut v___x_4137_: usize = 0;
            let mut v___x_4138_: usize = 0;
            let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4137_ = 0usize;
            v___x_4138_ = lean_usize_of_nat(v___x_4129_);
            v___x_4139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4125_,
                v___f_4132_,
                v_buckets_4126_,
                v___x_4137_,
                v___x_4138_,
                v___x_4128_,
            );
            return v___x_4139_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_interSmaller(
    mut v_00_u03b1_4140_: *mut leanh::LeanObject,
    mut v_00_u03b2_4141_: *mut leanh::LeanObject,
    mut v_inst_4142_: *mut leanh::LeanObject,
    mut v_inst_4143_: *mut leanh::LeanObject,
    mut v_m_u2081_4144_: *mut leanh::LeanObject,
    mut v_m_u2082_4145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4146_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg(
        v_inst_4142_,
        v_inst_4143_,
        v_m_u2081_4144_,
        v_m_u2082_4145_,
    );
    return v___x_4146_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__0(
    mut v_inst_4147_: *mut leanh::LeanObject,
    mut v_inst_4148_: *mut leanh::LeanObject,
    mut v_a_4149_: *mut leanh::LeanObject,
    mut v_b_4150_: *mut leanh::LeanObject,
    mut v_acc_4151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_4152_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_4147_,
        v_inst_4148_,
        v_acc_4151_,
        v_a_4149_,
        v_b_4150_,
    );
    v___x_4153_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4153_, 0, v_r_4152_);
    return v___x_4153_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__1(
    mut v___x_4154_: *mut leanh::LeanObject,
    mut v___f_4155_: *mut leanh::LeanObject,
    mut v_a_4156_: *mut leanh::LeanObject,
    mut v_x_4157_: *mut leanh::LeanObject,
    mut v___y_4158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_4154_, v___f_4155_, v_a_4156_, v___y_4158_);
    return v___x_4159_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_union___redArg(
    mut v_inst_4162_: *mut leanh::LeanObject,
    mut v_inst_4163_: *mut leanh::LeanObject,
    mut v_m_u2081_4164_: *mut leanh::LeanObject,
    mut v_m_u2082_4165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: u8 = 0;
    v_size_4166_ = leanh::lean_ctor_get(v_m_u2081_4164_, 0);
    v_buckets_4167_ = leanh::lean_ctor_get(v_m_u2081_4164_, 1);
    v_size_4168_ = leanh::lean_ctor_get(v_m_u2082_4165_, 0);
    v___x_4169_ = lean_nat_dec_le(v_size_4166_, v_size_4168_);
    if v___x_4169_ == 0 {
        let mut v___f_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4170_ = l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0;
        v___x_4171_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_4170_,
            v_inst_4162_,
            v_inst_4163_,
            v_m_u2081_4164_,
            v_m_u2082_4165_,
        );
        return v___x_4171_;
    } else {
        let mut v___f_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4175_: usize = 0;
        let mut v___x_4176_: usize = 0;
        let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_buckets_4167_);
        leanh::lean_dec_ref(v_m_u2081_4164_);
        v___f_4172_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_4172_, 0, v_inst_4162_);
        leanh::lean_closure_set(v___f_4172_, 1, v_inst_4163_);
        v___x_4173_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__9;
        v___f_4174_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_4174_, 0, v___x_4173_);
        leanh::lean_closure_set(v___f_4174_, 1, v___f_4172_);
        v_sz_4175_ = lean_array_size(v_buckets_4167_);
        v___x_4176_ = 0usize;
        v___x_4177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4173_,
            v_buckets_4167_,
            v___f_4174_,
            v_sz_4175_,
            v___x_4176_,
            v_m_u2082_4165_,
        );
        return v___x_4177_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_union(
    mut v_00_u03b1_4178_: *mut leanh::LeanObject,
    mut v_00_u03b2_4179_: *mut leanh::LeanObject,
    mut v_inst_4180_: *mut leanh::LeanObject,
    mut v_inst_4181_: *mut leanh::LeanObject,
    mut v_m_u2081_4182_: *mut leanh::LeanObject,
    mut v_m_u2082_4183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: u8 = 0;
    v_size_4184_ = leanh::lean_ctor_get(v_m_u2081_4182_, 0);
    v_buckets_4185_ = leanh::lean_ctor_get(v_m_u2081_4182_, 1);
    v_size_4186_ = leanh::lean_ctor_get(v_m_u2082_4183_, 0);
    v___x_4187_ = lean_nat_dec_le(v_size_4184_, v_size_4186_);
    if v___x_4187_ == 0 {
        let mut v___f_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4188_ = l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0;
        v___x_4189_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_4188_,
            v_inst_4180_,
            v_inst_4181_,
            v_m_u2081_4182_,
            v_m_u2082_4183_,
        );
        return v___x_4189_;
    } else {
        let mut v___f_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4193_: usize = 0;
        let mut v___x_4194_: usize = 0;
        let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_buckets_4185_);
        leanh::lean_dec_ref(v_m_u2081_4182_);
        v___f_4190_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_4190_, 0, v_inst_4180_);
        leanh::lean_closure_set(v___f_4190_, 1, v_inst_4181_);
        v___x_4191_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__9;
        v___f_4192_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_4192_, 0, v___x_4191_);
        leanh::lean_closure_set(v___f_4192_, 1, v___f_4190_);
        v_sz_4193_ = lean_array_size(v_buckets_4185_);
        v___x_4194_ = 0usize;
        v___x_4195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4191_,
            v_buckets_4185_,
            v___f_4192_,
            v_sz_4193_,
            v___x_4194_,
            v_m_u2082_4183_,
        );
        return v___x_4195_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0(
    mut v_inst_4196_: *mut leanh::LeanObject,
    mut v_inst_4197_: *mut leanh::LeanObject,
    mut v_m_u2082_4198_: *mut leanh::LeanObject,
    mut v_k_4199_: *mut leanh::LeanObject,
    mut v_x_4200_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4201_: u8 = 0;
    v___x_4201_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_4196_,
        v_inst_4197_,
        v_m_u2082_4198_,
        v_k_4199_,
    );
    return v___x_4201_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0___boxed(
    mut v_inst_4202_: *mut leanh::LeanObject,
    mut v_inst_4203_: *mut leanh::LeanObject,
    mut v_m_u2082_4204_: *mut leanh::LeanObject,
    mut v_k_4205_: *mut leanh::LeanObject,
    mut v_x_4206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4207_: u8 = 0;
    let mut v_r_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4207_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0(
        v_inst_4202_,
        v_inst_4203_,
        v_m_u2082_4204_,
        v_k_4205_,
        v_x_4206_,
    );
    leanh::lean_dec(v_x_4206_);
    leanh::lean_dec_ref(v_m_u2082_4204_);
    v_r_4208_ = leanh::lean_box((v_res_4207_) as usize);
    return v_r_4208_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
    mut v_inst_4209_: *mut leanh::LeanObject,
    mut v_inst_4210_: *mut leanh::LeanObject,
    mut v_m_u2081_4211_: *mut leanh::LeanObject,
    mut v_m_u2082_4212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: u8 = 0;
    v_size_4213_ = leanh::lean_ctor_get(v_m_u2081_4211_, 0);
    v_size_4214_ = leanh::lean_ctor_get(v_m_u2082_4212_, 0);
    v___x_4215_ = lean_nat_dec_le(v_size_4213_, v_size_4214_);
    if v___x_4215_ == 0 {
        let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4216_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg(
            v_inst_4209_,
            v_inst_4210_,
            v_m_u2081_4211_,
            v_m_u2082_4212_,
        );
        return v___x_4216_;
    } else {
        let mut v___f_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4217_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            5,
            3,
        );
        leanh::lean_closure_set(v___f_4217_, 0, v_inst_4209_);
        leanh::lean_closure_set(v___f_4217_, 1, v_inst_4210_);
        leanh::lean_closure_set(v___f_4217_, 2, v_m_u2082_4212_);
        v___x_4218_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_4217_, v_m_u2081_4211_);
        return v___x_4218_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_inter(
    mut v_00_u03b1_4219_: *mut leanh::LeanObject,
    mut v_00_u03b2_4220_: *mut leanh::LeanObject,
    mut v_inst_4221_: *mut leanh::LeanObject,
    mut v_inst_4222_: *mut leanh::LeanObject,
    mut v_m_u2081_4223_: *mut leanh::LeanObject,
    mut v_m_u2082_4224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4225_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_inst_4221_,
        v_inst_4222_,
        v_m_u2081_4223_,
        v_m_u2082_4224_,
    );
    return v___x_4225_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0(
    mut v_inst_4226_: *mut leanh::LeanObject,
    mut v_inst_4227_: *mut leanh::LeanObject,
    mut v_inst_4228_: *mut leanh::LeanObject,
    mut v_m_u2082_4229_: *mut leanh::LeanObject,
    mut v___x_4230_: u8,
    mut v___x_4231_: *mut leanh::LeanObject,
    mut v___x_4232_: *mut leanh::LeanObject,
    mut v_a_4233_: *mut leanh::LeanObject,
    mut v_b_4234_: *mut leanh::LeanObject,
    mut v_acc_4235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: u8 = 0;
    leanh::lean_inc(v_a_4233_);
    v___x_4236_ = leanh::lean_apply_1(v_inst_4226_, v_a_4233_);
    v___x_4237_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        v_inst_4227_,
        v_inst_4228_,
        v_m_u2082_4229_,
        v_a_4233_,
    );
    v___x_4238_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4238_, 0, v_b_4234_);
    v___x_4239_ = l_Option_instBEq_beq___redArg(v___x_4236_, v___x_4237_, v___x_4238_);
    if v___x_4239_ == 0 {
        let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_4232_);
        v___x_4240_ = leanh::lean_box((v___x_4230_) as usize);
        v___x_4241_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4241_, 0, v___x_4240_);
        v___x_4242_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4242_, 0, v___x_4241_);
        leanh::lean_ctor_set(v___x_4242_, 1, v___x_4231_);
        v___x_4243_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4243_, 0, v___x_4242_);
        return v___x_4243_;
    } else {
        let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4244_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4244_, 0, v___x_4232_);
        return v___x_4244_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0___boxed(
    mut v_inst_4245_: *mut leanh::LeanObject,
    mut v_inst_4246_: *mut leanh::LeanObject,
    mut v_inst_4247_: *mut leanh::LeanObject,
    mut v_m_u2082_4248_: *mut leanh::LeanObject,
    mut v___x_4249_: *mut leanh::LeanObject,
    mut v___x_4250_: *mut leanh::LeanObject,
    mut v___x_4251_: *mut leanh::LeanObject,
    mut v_a_4252_: *mut leanh::LeanObject,
    mut v_b_4253_: *mut leanh::LeanObject,
    mut v_acc_4254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_202__boxed_4255_: u8 = 0;
    let mut v_res_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_202__boxed_4255_ = (leanh::lean_unbox(v___x_4249_) as u8);
    v_res_4256_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0(
        v_inst_4245_,
        v_inst_4246_,
        v_inst_4247_,
        v_m_u2082_4248_,
        v___x_202__boxed_4255_,
        v___x_4250_,
        v___x_4251_,
        v_a_4252_,
        v_b_4253_,
        v_acc_4254_,
    );
    leanh::lean_dec_ref(v_acc_4254_);
    leanh::lean_dec_ref(v_m_u2082_4248_);
    return v_res_4256_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__1(
    mut v___x_4257_: *mut leanh::LeanObject,
    mut v___f_4258_: *mut leanh::LeanObject,
    mut v_a_4259_: *mut leanh::LeanObject,
    mut v_x_4260_: *mut leanh::LeanObject,
    mut v___y_4261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4262_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_4257_, v___f_4258_, v_a_4259_, v___y_4261_);
    return v___x_4262_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
    mut v_inst_4266_: *mut leanh::LeanObject,
    mut v_inst_4267_: *mut leanh::LeanObject,
    mut v_inst_4268_: *mut leanh::LeanObject,
    mut v_m_u2081_4269_: *mut leanh::LeanObject,
    mut v_m_u2082_4270_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: u8 = 0;
    v_size_4271_ = leanh::lean_ctor_get(v_m_u2081_4269_, 0);
    leanh::lean_inc(v_size_4271_);
    v_buckets_4272_ = leanh::lean_ctor_get(v_m_u2081_4269_, 1);
    leanh::lean_inc_ref(v_buckets_4272_);
    leanh::lean_dec_ref(v_m_u2081_4269_);
    v_size_4273_ = leanh::lean_ctor_get(v_m_u2082_4270_, 0);
    v___x_4274_ = lean_nat_dec_eq(v_size_4271_, v_size_4273_);
    leanh::lean_dec(v_size_4271_);
    if v___x_4274_ == 0 {
        leanh::lean_dec_ref(v_buckets_4272_);
        leanh::lean_dec_ref(v_m_u2082_4270_);
        leanh::lean_dec_ref(v_inst_4268_);
        leanh::lean_dec_ref(v_inst_4267_);
        leanh::lean_dec_ref(v_inst_4266_);
        return v___x_4274_;
    } else {
        let mut v___x_4275_: u8 = 0;
        let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4282_: usize = 0;
        let mut v___x_4283_: usize = 0;
        let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4275_ = 0;
        v___x_4276_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__9;
        v___x_4277_ = leanh::lean_box(0);
        v___x_4278_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0;
        v___x_4279_ = leanh::lean_box((v___x_4275_) as usize);
        v___f_4280_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            10,
            7,
        );
        leanh::lean_closure_set(v___f_4280_, 0, v_inst_4268_);
        leanh::lean_closure_set(v___f_4280_, 1, v_inst_4266_);
        leanh::lean_closure_set(v___f_4280_, 2, v_inst_4267_);
        leanh::lean_closure_set(v___f_4280_, 3, v_m_u2082_4270_);
        leanh::lean_closure_set(v___f_4280_, 4, v___x_4279_);
        leanh::lean_closure_set(v___f_4280_, 5, v___x_4277_);
        leanh::lean_closure_set(v___f_4280_, 6, v___x_4278_);
        v___f_4281_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_4281_, 0, v___x_4276_);
        leanh::lean_closure_set(v___f_4281_, 1, v___f_4280_);
        v_sz_4282_ = lean_array_size(v_buckets_4272_);
        v___x_4283_ = 0usize;
        v___x_4284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4276_,
            v_buckets_4272_,
            v___f_4281_,
            v_sz_4282_,
            v___x_4283_,
            v___x_4278_,
        );
        v_fst_4285_ = leanh::lean_ctor_get(v___x_4284_, 0);
        leanh::lean_inc(v_fst_4285_);
        leanh::lean_dec(v___x_4284_);
        if leanh::lean_obj_tag(v_fst_4285_) == 0 {
            return v___x_4274_;
        } else {
            let mut v_val_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4287_: u8 = 0;
            v_val_4286_ = leanh::lean_ctor_get(v_fst_4285_, 0);
            leanh::lean_inc(v_val_4286_);
            leanh::lean_dec_ref_known(v_fst_4285_, 1);
            v___x_4287_ = (leanh::lean_unbox(v_val_4286_) as u8);
            leanh::lean_dec(v_val_4286_);
            return v___x_4287_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___boxed(
    mut v_inst_4288_: *mut leanh::LeanObject,
    mut v_inst_4289_: *mut leanh::LeanObject,
    mut v_inst_4290_: *mut leanh::LeanObject,
    mut v_m_u2081_4291_: *mut leanh::LeanObject,
    mut v_m_u2082_4292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4293_: u8 = 0;
    let mut v_r_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4293_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
        v_inst_4288_,
        v_inst_4289_,
        v_inst_4290_,
        v_m_u2081_4291_,
        v_m_u2082_4292_,
    );
    v_r_4294_ = leanh::lean_box((v_res_4293_) as usize);
    return v_r_4294_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_beq(
    mut v_00_u03b1_4295_: *mut leanh::LeanObject,
    mut v_00_u03b2_4296_: *mut leanh::LeanObject,
    mut v_inst_4297_: *mut leanh::LeanObject,
    mut v_inst_4298_: *mut leanh::LeanObject,
    mut v_inst_4299_: *mut leanh::LeanObject,
    mut v_inst_4300_: *mut leanh::LeanObject,
    mut v_m_u2081_4301_: *mut leanh::LeanObject,
    mut v_m_u2082_4302_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4303_: u8 = 0;
    v___x_4303_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(
        v_inst_4297_,
        v_inst_4299_,
        v_inst_4300_,
        v_m_u2081_4301_,
        v_m_u2082_4302_,
    );
    return v___x_4303_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_beq___boxed(
    mut v_00_u03b1_4304_: *mut leanh::LeanObject,
    mut v_00_u03b2_4305_: *mut leanh::LeanObject,
    mut v_inst_4306_: *mut leanh::LeanObject,
    mut v_inst_4307_: *mut leanh::LeanObject,
    mut v_inst_4308_: *mut leanh::LeanObject,
    mut v_inst_4309_: *mut leanh::LeanObject,
    mut v_m_u2081_4310_: *mut leanh::LeanObject,
    mut v_m_u2082_4311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4312_: u8 = 0;
    let mut v_r_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4312_ = l_Std_DHashMap_Internal_Raw_u2080_beq(
        v_00_u03b1_4304_,
        v_00_u03b2_4305_,
        v_inst_4306_,
        v_inst_4307_,
        v_inst_4308_,
        v_inst_4309_,
        v_m_u2081_4310_,
        v_m_u2082_4311_,
    );
    v_r_4313_ = leanh::lean_box((v_res_4312_) as usize);
    return v_r_4313_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0(
    mut v_inst_4314_: *mut leanh::LeanObject,
    mut v_inst_4315_: *mut leanh::LeanObject,
    mut v_m_u2082_4316_: *mut leanh::LeanObject,
    mut v___x_4317_: u8,
    mut v_k_4318_: *mut leanh::LeanObject,
    mut v_x_4319_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4320_: u8 = 0;
    v___x_4320_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_4314_,
        v_inst_4315_,
        v_m_u2082_4316_,
        v_k_4318_,
    );
    if v___x_4320_ == 0 {
        return v___x_4317_;
    } else {
        let mut v___x_4321_: u8 = 0;
        v___x_4321_ = 0;
        return v___x_4321_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0___boxed(
    mut v_inst_4322_: *mut leanh::LeanObject,
    mut v_inst_4323_: *mut leanh::LeanObject,
    mut v_m_u2082_4324_: *mut leanh::LeanObject,
    mut v___x_4325_: *mut leanh::LeanObject,
    mut v_k_4326_: *mut leanh::LeanObject,
    mut v_x_4327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_70__boxed_4328_: u8 = 0;
    let mut v_res_4329_: u8 = 0;
    let mut v_r_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_70__boxed_4328_ = (leanh::lean_unbox(v___x_4325_) as u8);
    v_res_4329_ = l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0(
        v_inst_4322_,
        v_inst_4323_,
        v_m_u2082_4324_,
        v___x_70__boxed_4328_,
        v_k_4326_,
        v_x_4327_,
    );
    leanh::lean_dec(v_x_4327_);
    leanh::lean_dec_ref(v_m_u2082_4324_);
    v_r_4330_ = leanh::lean_box((v_res_4329_) as usize);
    return v_r_4330_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_diff___redArg(
    mut v_inst_4331_: *mut leanh::LeanObject,
    mut v_inst_4332_: *mut leanh::LeanObject,
    mut v_m_u2081_4333_: *mut leanh::LeanObject,
    mut v_m_u2082_4334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: u8 = 0;
    v_size_4335_ = leanh::lean_ctor_get(v_m_u2081_4333_, 0);
    v_size_4336_ = leanh::lean_ctor_get(v_m_u2082_4334_, 0);
    v___x_4337_ = lean_nat_dec_le(v_size_4335_, v_size_4336_);
    if v___x_4337_ == 0 {
        let mut v___f_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4338_ = l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0;
        v___x_4339_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_4338_,
            v_inst_4331_,
            v_inst_4332_,
            v_m_u2081_4333_,
            v_m_u2082_4334_,
        );
        return v___x_4339_;
    } else {
        let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4340_ = leanh::lean_box((v___x_4337_) as usize);
        v___f_4341_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            4,
        );
        leanh::lean_closure_set(v___f_4341_, 0, v_inst_4331_);
        leanh::lean_closure_set(v___f_4341_, 1, v_inst_4332_);
        leanh::lean_closure_set(v___f_4341_, 2, v_m_u2082_4334_);
        leanh::lean_closure_set(v___f_4341_, 3, v___x_4340_);
        v___x_4342_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_4341_, v_m_u2081_4333_);
        return v___x_4342_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_diff(
    mut v_00_u03b1_4343_: *mut leanh::LeanObject,
    mut v_00_u03b2_4344_: *mut leanh::LeanObject,
    mut v_inst_4345_: *mut leanh::LeanObject,
    mut v_inst_4346_: *mut leanh::LeanObject,
    mut v_m_u2081_4347_: *mut leanh::LeanObject,
    mut v_m_u2082_4348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: u8 = 0;
    v_size_4349_ = leanh::lean_ctor_get(v_m_u2081_4347_, 0);
    v_size_4350_ = leanh::lean_ctor_get(v_m_u2082_4348_, 0);
    v___x_4351_ = lean_nat_dec_le(v_size_4349_, v_size_4350_);
    if v___x_4351_ == 0 {
        let mut v___f_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4352_ = l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0;
        v___x_4353_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_4352_,
            v_inst_4345_,
            v_inst_4346_,
            v_m_u2081_4347_,
            v_m_u2082_4348_,
        );
        return v___x_4353_;
    } else {
        let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4354_ = leanh::lean_box((v___x_4351_) as usize);
        v___f_4355_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            4,
        );
        leanh::lean_closure_set(v___f_4355_, 0, v_inst_4345_);
        leanh::lean_closure_set(v___f_4355_, 1, v_inst_4346_);
        leanh::lean_closure_set(v___f_4355_, 2, v_m_u2082_4348_);
        leanh::lean_closure_set(v___f_4355_, 3, v___x_4354_);
        v___x_4356_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_4355_, v_m_u2081_4347_);
        return v___x_4356_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
    mut v_inst_4357_: *mut leanh::LeanObject,
    mut v_inst_4358_: *mut leanh::LeanObject,
    mut v_m_4359_: *mut leanh::LeanObject,
    mut v_a_4360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: u64 = 0;
    let mut v___x_4365_: u64 = 0;
    let mut v___x_4366_: u64 = 0;
    let mut v___x_4367_: u64 = 0;
    let mut v_fold_4368_: u64 = 0;
    let mut v___x_4369_: u64 = 0;
    let mut v___x_4370_: u64 = 0;
    let mut v___x_4371_: u64 = 0;
    let mut v___x_4372_: usize = 0;
    let mut v___x_4373_: usize = 0;
    let mut v___x_4374_: usize = 0;
    let mut v___x_4375_: usize = 0;
    let mut v___x_4376_: usize = 0;
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4361_ = leanh::lean_ctor_get(v_m_4359_, 1);
    v___x_4362_ = lean_array_get_size(v_buckets_4361_);
    leanh::lean_inc(v_a_4360_);
    v___x_4363_ = leanh::lean_apply_1(v_inst_4358_, v_a_4360_);
    v___x_4364_ = 32u64;
    v___x_4365_ = leanh::lean_unbox_uint64(v___x_4363_);
    v___x_4366_ = lean_uint64_shift_right(v___x_4365_, v___x_4364_);
    v___x_4367_ = leanh::lean_unbox_uint64(v___x_4363_);
    leanh::lean_dec_ref(v___x_4363_);
    v_fold_4368_ = lean_uint64_xor(v___x_4367_, v___x_4366_);
    v___x_4369_ = 16u64;
    v___x_4370_ = lean_uint64_shift_right(v_fold_4368_, v___x_4369_);
    v___x_4371_ = lean_uint64_xor(v_fold_4368_, v___x_4370_);
    v___x_4372_ = lean_uint64_to_usize(v___x_4371_);
    v___x_4373_ = lean_usize_of_nat(v___x_4362_);
    v___x_4374_ = 1usize;
    v___x_4375_ = lean_usize_sub(v___x_4373_, v___x_4374_);
    v___x_4376_ = lean_usize_land(v___x_4372_, v___x_4375_);
    v___x_4377_ = lean_array_uget_borrowed(v_buckets_4361_, v___x_4376_);
    leanh::lean_inc(v___x_4377_);
    v___x_4378_ =
        l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_4357_, v_a_4360_, v___x_4377_);
    return v___x_4378_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg___boxed(
    mut v_inst_4379_: *mut leanh::LeanObject,
    mut v_inst_4380_: *mut leanh::LeanObject,
    mut v_m_4381_: *mut leanh::LeanObject,
    mut v_a_4382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4383_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_inst_4379_,
        v_inst_4380_,
        v_m_4381_,
        v_a_4382_,
    );
    leanh::lean_dec_ref(v_m_4381_);
    return v_res_4383_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f(
    mut v_00_u03b1_4384_: *mut leanh::LeanObject,
    mut v_00_u03b2_4385_: *mut leanh::LeanObject,
    mut v_inst_4386_: *mut leanh::LeanObject,
    mut v_inst_4387_: *mut leanh::LeanObject,
    mut v_m_4388_: *mut leanh::LeanObject,
    mut v_a_4389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4390_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_inst_4386_,
        v_inst_4387_,
        v_m_4388_,
        v_a_4389_,
    );
    return v___x_4390_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___boxed(
    mut v_00_u03b1_4391_: *mut leanh::LeanObject,
    mut v_00_u03b2_4392_: *mut leanh::LeanObject,
    mut v_inst_4393_: *mut leanh::LeanObject,
    mut v_inst_4394_: *mut leanh::LeanObject,
    mut v_m_4395_: *mut leanh::LeanObject,
    mut v_a_4396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4397_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f(
        v_00_u03b1_4391_,
        v_00_u03b2_4392_,
        v_inst_4393_,
        v_inst_4394_,
        v_m_4395_,
        v_a_4396_,
    );
    leanh::lean_dec_ref(v_m_4395_);
    return v_res_4397_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0(
    mut v_inst_4398_: *mut leanh::LeanObject,
    mut v_inst_4399_: *mut leanh::LeanObject,
    mut v_m_u2082_4400_: *mut leanh::LeanObject,
    mut v_inst_4401_: *mut leanh::LeanObject,
    mut v___x_4402_: u8,
    mut v___x_4403_: *mut leanh::LeanObject,
    mut v___x_4404_: *mut leanh::LeanObject,
    mut v_a_4405_: *mut leanh::LeanObject,
    mut v_b_4406_: *mut leanh::LeanObject,
    mut v_acc_4407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: u8 = 0;
    v___x_4408_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_inst_4398_,
        v_inst_4399_,
        v_m_u2082_4400_,
        v_a_4405_,
    );
    v___x_4409_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4409_, 0, v_b_4406_);
    v___x_4410_ = l_Option_instBEq_beq___redArg(v_inst_4401_, v___x_4408_, v___x_4409_);
    if v___x_4410_ == 0 {
        let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_4404_);
        v___x_4411_ = leanh::lean_box((v___x_4402_) as usize);
        v___x_4412_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4412_, 0, v___x_4411_);
        v___x_4413_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4413_, 0, v___x_4412_);
        leanh::lean_ctor_set(v___x_4413_, 1, v___x_4403_);
        v___x_4414_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4414_, 0, v___x_4413_);
        return v___x_4414_;
    } else {
        let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4415_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4415_, 0, v___x_4404_);
        return v___x_4415_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0___boxed(
    mut v_inst_4416_: *mut leanh::LeanObject,
    mut v_inst_4417_: *mut leanh::LeanObject,
    mut v_m_u2082_4418_: *mut leanh::LeanObject,
    mut v_inst_4419_: *mut leanh::LeanObject,
    mut v___x_4420_: *mut leanh::LeanObject,
    mut v___x_4421_: *mut leanh::LeanObject,
    mut v___x_4422_: *mut leanh::LeanObject,
    mut v_a_4423_: *mut leanh::LeanObject,
    mut v_b_4424_: *mut leanh::LeanObject,
    mut v_acc_4425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_195__boxed_4426_: u8 = 0;
    let mut v_res_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_195__boxed_4426_ = (leanh::lean_unbox(v___x_4420_) as u8);
    v_res_4427_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0(
        v_inst_4416_,
        v_inst_4417_,
        v_m_u2082_4418_,
        v_inst_4419_,
        v___x_195__boxed_4426_,
        v___x_4421_,
        v___x_4422_,
        v_a_4423_,
        v_b_4424_,
        v_acc_4425_,
    );
    leanh::lean_dec_ref(v_acc_4425_);
    leanh::lean_dec_ref(v_m_u2082_4418_);
    return v_res_4427_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
    mut v_inst_4428_: *mut leanh::LeanObject,
    mut v_inst_4429_: *mut leanh::LeanObject,
    mut v_inst_4430_: *mut leanh::LeanObject,
    mut v_m_u2081_4431_: *mut leanh::LeanObject,
    mut v_m_u2082_4432_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: u8 = 0;
    v_size_4433_ = leanh::lean_ctor_get(v_m_u2081_4431_, 0);
    leanh::lean_inc(v_size_4433_);
    v_buckets_4434_ = leanh::lean_ctor_get(v_m_u2081_4431_, 1);
    leanh::lean_inc_ref(v_buckets_4434_);
    leanh::lean_dec_ref(v_m_u2081_4431_);
    v_size_4435_ = leanh::lean_ctor_get(v_m_u2082_4432_, 0);
    v___x_4436_ = lean_nat_dec_eq(v_size_4433_, v_size_4435_);
    leanh::lean_dec(v_size_4433_);
    if v___x_4436_ == 0 {
        leanh::lean_dec_ref(v_buckets_4434_);
        leanh::lean_dec_ref(v_m_u2082_4432_);
        leanh::lean_dec_ref(v_inst_4430_);
        leanh::lean_dec_ref(v_inst_4429_);
        leanh::lean_dec_ref(v_inst_4428_);
        return v___x_4436_;
    } else {
        let mut v___x_4437_: u8 = 0;
        let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4444_: usize = 0;
        let mut v___x_4445_: usize = 0;
        let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4437_ = 0;
        v___x_4438_ = l_Std_DHashMap_Internal_computeSize___redArg___closed__9;
        v___x_4439_ = leanh::lean_box(0);
        v___x_4440_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0;
        v___x_4441_ = leanh::lean_box((v___x_4437_) as usize);
        v___f_4442_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            10,
            7,
        );
        leanh::lean_closure_set(v___f_4442_, 0, v_inst_4428_);
        leanh::lean_closure_set(v___f_4442_, 1, v_inst_4429_);
        leanh::lean_closure_set(v___f_4442_, 2, v_m_u2082_4432_);
        leanh::lean_closure_set(v___f_4442_, 3, v_inst_4430_);
        leanh::lean_closure_set(v___f_4442_, 4, v___x_4441_);
        leanh::lean_closure_set(v___f_4442_, 5, v___x_4439_);
        leanh::lean_closure_set(v___f_4442_, 6, v___x_4440_);
        v___f_4443_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_4443_, 0, v___x_4438_);
        leanh::lean_closure_set(v___f_4443_, 1, v___f_4442_);
        v_sz_4444_ = lean_array_size(v_buckets_4434_);
        v___x_4445_ = 0usize;
        v___x_4446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4438_,
            v_buckets_4434_,
            v___f_4443_,
            v_sz_4444_,
            v___x_4445_,
            v___x_4440_,
        );
        v_fst_4447_ = leanh::lean_ctor_get(v___x_4446_, 0);
        leanh::lean_inc(v_fst_4447_);
        leanh::lean_dec(v___x_4446_);
        if leanh::lean_obj_tag(v_fst_4447_) == 0 {
            return v___x_4436_;
        } else {
            let mut v_val_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4449_: u8 = 0;
            v_val_4448_ = leanh::lean_ctor_get(v_fst_4447_, 0);
            leanh::lean_inc(v_val_4448_);
            leanh::lean_dec_ref_known(v_fst_4447_, 1);
            v___x_4449_ = (leanh::lean_unbox(v_val_4448_) as u8);
            leanh::lean_dec(v_val_4448_);
            return v___x_4449_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___boxed(
    mut v_inst_4450_: *mut leanh::LeanObject,
    mut v_inst_4451_: *mut leanh::LeanObject,
    mut v_inst_4452_: *mut leanh::LeanObject,
    mut v_m_u2081_4453_: *mut leanh::LeanObject,
    mut v_m_u2082_4454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4455_: u8 = 0;
    let mut v_r_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4455_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
        v_inst_4450_,
        v_inst_4451_,
        v_inst_4452_,
        v_m_u2081_4453_,
        v_m_u2082_4454_,
    );
    v_r_4456_ = leanh::lean_box((v_res_4455_) as usize);
    return v_r_4456_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_beq(
    mut v_00_u03b1_4457_: *mut leanh::LeanObject,
    mut v_00_u03b2_4458_: *mut leanh::LeanObject,
    mut v_inst_4459_: *mut leanh::LeanObject,
    mut v_inst_4460_: *mut leanh::LeanObject,
    mut v_inst_4461_: *mut leanh::LeanObject,
    mut v_m_u2081_4462_: *mut leanh::LeanObject,
    mut v_m_u2082_4463_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4464_: u8 = 0;
    v___x_4464_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
        v_inst_4459_,
        v_inst_4460_,
        v_inst_4461_,
        v_m_u2081_4462_,
        v_m_u2082_4463_,
    );
    return v___x_4464_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_beq___boxed(
    mut v_00_u03b1_4465_: *mut leanh::LeanObject,
    mut v_00_u03b2_4466_: *mut leanh::LeanObject,
    mut v_inst_4467_: *mut leanh::LeanObject,
    mut v_inst_4468_: *mut leanh::LeanObject,
    mut v_inst_4469_: *mut leanh::LeanObject,
    mut v_m_u2081_4470_: *mut leanh::LeanObject,
    mut v_m_u2082_4471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4472_: u8 = 0;
    let mut v_r_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4472_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq(
        v_00_u03b1_4465_,
        v_00_u03b2_4466_,
        v_inst_4467_,
        v_inst_4468_,
        v_inst_4469_,
        v_m_u2081_4470_,
        v_m_u2082_4471_,
    );
    v_r_4473_ = leanh::lean_box((v_res_4472_) as usize);
    return v_r_4473_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
    mut v_inst_4474_: *mut leanh::LeanObject,
    mut v_inst_4475_: *mut leanh::LeanObject,
    mut v_m_4476_: *mut leanh::LeanObject,
    mut v_a_4477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: u64 = 0;
    let mut v___x_4482_: u64 = 0;
    let mut v___x_4483_: u64 = 0;
    let mut v___x_4484_: u64 = 0;
    let mut v_fold_4485_: u64 = 0;
    let mut v___x_4486_: u64 = 0;
    let mut v___x_4487_: u64 = 0;
    let mut v___x_4488_: u64 = 0;
    let mut v___x_4489_: usize = 0;
    let mut v___x_4490_: usize = 0;
    let mut v___x_4491_: usize = 0;
    let mut v___x_4492_: usize = 0;
    let mut v___x_4493_: usize = 0;
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4478_ = leanh::lean_ctor_get(v_m_4476_, 1);
    v___x_4479_ = lean_array_get_size(v_buckets_4478_);
    leanh::lean_inc(v_a_4477_);
    v___x_4480_ = leanh::lean_apply_1(v_inst_4475_, v_a_4477_);
    v___x_4481_ = 32u64;
    v___x_4482_ = leanh::lean_unbox_uint64(v___x_4480_);
    v___x_4483_ = lean_uint64_shift_right(v___x_4482_, v___x_4481_);
    v___x_4484_ = leanh::lean_unbox_uint64(v___x_4480_);
    leanh::lean_dec_ref(v___x_4480_);
    v_fold_4485_ = lean_uint64_xor(v___x_4484_, v___x_4483_);
    v___x_4486_ = 16u64;
    v___x_4487_ = lean_uint64_shift_right(v_fold_4485_, v___x_4486_);
    v___x_4488_ = lean_uint64_xor(v_fold_4485_, v___x_4487_);
    v___x_4489_ = lean_uint64_to_usize(v___x_4488_);
    v___x_4490_ = lean_usize_of_nat(v___x_4479_);
    v___x_4491_ = 1usize;
    v___x_4492_ = lean_usize_sub(v___x_4490_, v___x_4491_);
    v___x_4493_ = lean_usize_land(v___x_4489_, v___x_4492_);
    v___x_4494_ = lean_array_uget_borrowed(v_buckets_4478_, v___x_4493_);
    leanh::lean_inc(v___x_4494_);
    v___x_4495_ =
        l_Std_DHashMap_Internal_AssocList_get___redArg(v_inst_4474_, v_a_4477_, v___x_4494_);
    return v___x_4495_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg___boxed(
    mut v_inst_4496_: *mut leanh::LeanObject,
    mut v_inst_4497_: *mut leanh::LeanObject,
    mut v_m_4498_: *mut leanh::LeanObject,
    mut v_a_4499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4500_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_4496_,
        v_inst_4497_,
        v_m_4498_,
        v_a_4499_,
    );
    leanh::lean_dec_ref(v_m_4498_);
    return v_res_4500_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get(
    mut v_00_u03b1_4501_: *mut leanh::LeanObject,
    mut v_00_u03b2_4502_: *mut leanh::LeanObject,
    mut v_inst_4503_: *mut leanh::LeanObject,
    mut v_inst_4504_: *mut leanh::LeanObject,
    mut v_m_4505_: *mut leanh::LeanObject,
    mut v_a_4506_: *mut leanh::LeanObject,
    mut v_hma_4507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_4503_,
        v_inst_4504_,
        v_m_4505_,
        v_a_4506_,
    );
    return v___x_4508_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get___boxed(
    mut v_00_u03b1_4509_: *mut leanh::LeanObject,
    mut v_00_u03b2_4510_: *mut leanh::LeanObject,
    mut v_inst_4511_: *mut leanh::LeanObject,
    mut v_inst_4512_: *mut leanh::LeanObject,
    mut v_m_4513_: *mut leanh::LeanObject,
    mut v_a_4514_: *mut leanh::LeanObject,
    mut v_hma_4515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4516_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get(
        v_00_u03b1_4509_,
        v_00_u03b2_4510_,
        v_inst_4511_,
        v_inst_4512_,
        v_m_4513_,
        v_a_4514_,
        v_hma_4515_,
    );
    leanh::lean_dec_ref(v_m_4513_);
    return v_res_4516_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
    mut v_inst_4517_: *mut leanh::LeanObject,
    mut v_inst_4518_: *mut leanh::LeanObject,
    mut v_m_4519_: *mut leanh::LeanObject,
    mut v_a_4520_: *mut leanh::LeanObject,
    mut v_fallback_4521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: u64 = 0;
    let mut v___x_4526_: u64 = 0;
    let mut v___x_4527_: u64 = 0;
    let mut v___x_4528_: u64 = 0;
    let mut v_fold_4529_: u64 = 0;
    let mut v___x_4530_: u64 = 0;
    let mut v___x_4531_: u64 = 0;
    let mut v___x_4532_: u64 = 0;
    let mut v___x_4533_: usize = 0;
    let mut v___x_4534_: usize = 0;
    let mut v___x_4535_: usize = 0;
    let mut v___x_4536_: usize = 0;
    let mut v___x_4537_: usize = 0;
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4522_ = leanh::lean_ctor_get(v_m_4519_, 1);
    v___x_4523_ = lean_array_get_size(v_buckets_4522_);
    leanh::lean_inc(v_a_4520_);
    v___x_4524_ = leanh::lean_apply_1(v_inst_4518_, v_a_4520_);
    v___x_4525_ = 32u64;
    v___x_4526_ = leanh::lean_unbox_uint64(v___x_4524_);
    v___x_4527_ = lean_uint64_shift_right(v___x_4526_, v___x_4525_);
    v___x_4528_ = leanh::lean_unbox_uint64(v___x_4524_);
    leanh::lean_dec_ref(v___x_4524_);
    v_fold_4529_ = lean_uint64_xor(v___x_4528_, v___x_4527_);
    v___x_4530_ = 16u64;
    v___x_4531_ = lean_uint64_shift_right(v_fold_4529_, v___x_4530_);
    v___x_4532_ = lean_uint64_xor(v_fold_4529_, v___x_4531_);
    v___x_4533_ = lean_uint64_to_usize(v___x_4532_);
    v___x_4534_ = lean_usize_of_nat(v___x_4523_);
    v___x_4535_ = 1usize;
    v___x_4536_ = lean_usize_sub(v___x_4534_, v___x_4535_);
    v___x_4537_ = lean_usize_land(v___x_4533_, v___x_4536_);
    v___x_4538_ = lean_array_uget_borrowed(v_buckets_4522_, v___x_4537_);
    leanh::lean_inc(v___x_4538_);
    v___x_4539_ = l_Std_DHashMap_Internal_AssocList_getD___redArg(
        v_inst_4517_,
        v_a_4520_,
        v_fallback_4521_,
        v___x_4538_,
    );
    return v___x_4539_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg___boxed(
    mut v_inst_4540_: *mut leanh::LeanObject,
    mut v_inst_4541_: *mut leanh::LeanObject,
    mut v_m_4542_: *mut leanh::LeanObject,
    mut v_a_4543_: *mut leanh::LeanObject,
    mut v_fallback_4544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4545_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        v_inst_4540_,
        v_inst_4541_,
        v_m_4542_,
        v_a_4543_,
        v_fallback_4544_,
    );
    leanh::lean_dec(v_fallback_4544_);
    leanh::lean_dec_ref(v_m_4542_);
    return v_res_4545_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD(
    mut v_00_u03b1_4546_: *mut leanh::LeanObject,
    mut v_00_u03b2_4547_: *mut leanh::LeanObject,
    mut v_inst_4548_: *mut leanh::LeanObject,
    mut v_inst_4549_: *mut leanh::LeanObject,
    mut v_m_4550_: *mut leanh::LeanObject,
    mut v_a_4551_: *mut leanh::LeanObject,
    mut v_fallback_4552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4553_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        v_inst_4548_,
        v_inst_4549_,
        v_m_4550_,
        v_a_4551_,
        v_fallback_4552_,
    );
    return v___x_4553_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___boxed(
    mut v_00_u03b1_4554_: *mut leanh::LeanObject,
    mut v_00_u03b2_4555_: *mut leanh::LeanObject,
    mut v_inst_4556_: *mut leanh::LeanObject,
    mut v_inst_4557_: *mut leanh::LeanObject,
    mut v_m_4558_: *mut leanh::LeanObject,
    mut v_a_4559_: *mut leanh::LeanObject,
    mut v_fallback_4560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4561_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD(
        v_00_u03b1_4554_,
        v_00_u03b2_4555_,
        v_inst_4556_,
        v_inst_4557_,
        v_m_4558_,
        v_a_4559_,
        v_fallback_4560_,
    );
    leanh::lean_dec(v_fallback_4560_);
    leanh::lean_dec_ref(v_m_4558_);
    return v_res_4561_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
    mut v_inst_4562_: *mut leanh::LeanObject,
    mut v_inst_4563_: *mut leanh::LeanObject,
    mut v_inst_4564_: *mut leanh::LeanObject,
    mut v_m_4565_: *mut leanh::LeanObject,
    mut v_a_4566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: u64 = 0;
    let mut v___x_4571_: u64 = 0;
    let mut v___x_4572_: u64 = 0;
    let mut v___x_4573_: u64 = 0;
    let mut v_fold_4574_: u64 = 0;
    let mut v___x_4575_: u64 = 0;
    let mut v___x_4576_: u64 = 0;
    let mut v___x_4577_: u64 = 0;
    let mut v___x_4578_: usize = 0;
    let mut v___x_4579_: usize = 0;
    let mut v___x_4580_: usize = 0;
    let mut v___x_4581_: usize = 0;
    let mut v___x_4582_: usize = 0;
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4567_ = leanh::lean_ctor_get(v_m_4565_, 1);
    v___x_4568_ = lean_array_get_size(v_buckets_4567_);
    leanh::lean_inc(v_a_4566_);
    v___x_4569_ = leanh::lean_apply_1(v_inst_4563_, v_a_4566_);
    v___x_4570_ = 32u64;
    v___x_4571_ = leanh::lean_unbox_uint64(v___x_4569_);
    v___x_4572_ = lean_uint64_shift_right(v___x_4571_, v___x_4570_);
    v___x_4573_ = leanh::lean_unbox_uint64(v___x_4569_);
    leanh::lean_dec_ref(v___x_4569_);
    v_fold_4574_ = lean_uint64_xor(v___x_4573_, v___x_4572_);
    v___x_4575_ = 16u64;
    v___x_4576_ = lean_uint64_shift_right(v_fold_4574_, v___x_4575_);
    v___x_4577_ = lean_uint64_xor(v_fold_4574_, v___x_4576_);
    v___x_4578_ = lean_uint64_to_usize(v___x_4577_);
    v___x_4579_ = lean_usize_of_nat(v___x_4568_);
    v___x_4580_ = 1usize;
    v___x_4581_ = lean_usize_sub(v___x_4579_, v___x_4580_);
    v___x_4582_ = lean_usize_land(v___x_4578_, v___x_4581_);
    v___x_4583_ = lean_array_uget_borrowed(v_buckets_4567_, v___x_4582_);
    leanh::lean_inc(v___x_4583_);
    v___x_4584_ = l_Std_DHashMap_Internal_AssocList_get_x21___redArg(
        v_inst_4562_,
        v_inst_4564_,
        v_a_4566_,
        v___x_4583_,
    );
    return v___x_4584_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___boxed(
    mut v_inst_4585_: *mut leanh::LeanObject,
    mut v_inst_4586_: *mut leanh::LeanObject,
    mut v_inst_4587_: *mut leanh::LeanObject,
    mut v_m_4588_: *mut leanh::LeanObject,
    mut v_a_4589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
        v_inst_4585_,
        v_inst_4586_,
        v_inst_4587_,
        v_m_4588_,
        v_a_4589_,
    );
    leanh::lean_dec_ref(v_m_4588_);
    leanh::lean_dec(v_inst_4587_);
    return v_res_4590_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21(
    mut v_00_u03b1_4591_: *mut leanh::LeanObject,
    mut v_00_u03b2_4592_: *mut leanh::LeanObject,
    mut v_inst_4593_: *mut leanh::LeanObject,
    mut v_inst_4594_: *mut leanh::LeanObject,
    mut v_inst_4595_: *mut leanh::LeanObject,
    mut v_m_4596_: *mut leanh::LeanObject,
    mut v_a_4597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4598_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(
        v_inst_4593_,
        v_inst_4594_,
        v_inst_4595_,
        v_m_4596_,
        v_a_4597_,
    );
    return v___x_4598_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___boxed(
    mut v_00_u03b1_4599_: *mut leanh::LeanObject,
    mut v_00_u03b2_4600_: *mut leanh::LeanObject,
    mut v_inst_4601_: *mut leanh::LeanObject,
    mut v_inst_4602_: *mut leanh::LeanObject,
    mut v_inst_4603_: *mut leanh::LeanObject,
    mut v_m_4604_: *mut leanh::LeanObject,
    mut v_a_4605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21(
        v_00_u03b1_4599_,
        v_00_u03b2_4600_,
        v_inst_4601_,
        v_inst_4602_,
        v_inst_4603_,
        v_m_4604_,
        v_a_4605_,
    );
    leanh::lean_dec_ref(v_m_4604_);
    leanh::lean_dec(v_inst_4603_);
    return v_res_4606_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getThenInsertIfNew_x3f___redArg(
    mut v_inst_4607_: *mut leanh::LeanObject,
    mut v_inst_4608_: *mut leanh::LeanObject,
    mut v_m_4609_: *mut leanh::LeanObject,
    mut v_a_4610_: *mut leanh::LeanObject,
    mut v_b_4611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: u64 = 0;
    let mut v___x_4617_: u64 = 0;
    let mut v___x_4618_: u64 = 0;
    let mut v___x_4619_: u64 = 0;
    let mut v_fold_4620_: u64 = 0;
    let mut v___x_4621_: u64 = 0;
    let mut v___x_4622_: u64 = 0;
    let mut v___x_4623_: u64 = 0;
    let mut v___x_4624_: usize = 0;
    let mut v___x_4625_: usize = 0;
    let mut v___x_4626_: usize = 0;
    let mut v___x_4627_: usize = 0;
    let mut v___x_4628_: usize = 0;
    let mut v_bkt_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4633_: u8 = 0;
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: u8 = 0;
    let mut v_val_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4653_: u8 = 0;
    let mut v_unused_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4612_ = leanh::lean_ctor_get(v_m_4609_, 0);
                v_buckets_4613_ = leanh::lean_ctor_get(v_m_4609_, 1);
                v___x_4614_ = lean_array_get_size(v_buckets_4613_);
                leanh::lean_inc_ref(v_inst_4608_);
                leanh::lean_inc_n(v_a_4610_, 2);
                v___x_4615_ = leanh::lean_apply_1(v_inst_4608_, v_a_4610_);
                v___x_4616_ = 32u64;
                v___x_4617_ = leanh::lean_unbox_uint64(v___x_4615_);
                v___x_4618_ = lean_uint64_shift_right(v___x_4617_, v___x_4616_);
                v___x_4619_ = leanh::lean_unbox_uint64(v___x_4615_);
                leanh::lean_dec_ref(v___x_4615_);
                v_fold_4620_ = lean_uint64_xor(v___x_4619_, v___x_4618_);
                v___x_4621_ = 16u64;
                v___x_4622_ = lean_uint64_shift_right(v_fold_4620_, v___x_4621_);
                v___x_4623_ = lean_uint64_xor(v_fold_4620_, v___x_4622_);
                v___x_4624_ = lean_uint64_to_usize(v___x_4623_);
                v___x_4625_ = lean_usize_of_nat(v___x_4614_);
                v___x_4626_ = 1usize;
                v___x_4627_ = lean_usize_sub(v___x_4625_, v___x_4626_);
                v___x_4628_ = lean_usize_land(v___x_4624_, v___x_4627_);
                v_bkt_4629_ = lean_array_uget_borrowed(v_buckets_4613_, v___x_4628_);
                leanh::lean_inc(v_bkt_4629_);
                v___x_4630_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                    v_inst_4607_,
                    v_a_4610_,
                    v_bkt_4629_,
                );
                if leanh::lean_obj_tag(v___x_4630_) == 0 {
                    leanh::lean_inc_ref(v_buckets_4613_);
                    leanh::lean_inc(v_size_4612_);
                    v_isSharedCheck_4653_ = (!leanh::lean_is_exclusive(v_m_4609_)) as u8;
                    if v_isSharedCheck_4653_ == 0 {
                        v_unused_4654_ = leanh::lean_ctor_get(v_m_4609_, 1);
                        leanh::lean_dec(v_unused_4654_);
                        v_unused_4655_ = leanh::lean_ctor_get(v_m_4609_, 0);
                        leanh::lean_dec(v_unused_4655_);
                        v___x_4632_ = v_m_4609_;
                        v_isShared_4633_ = v_isSharedCheck_4653_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_4609_);
                        v___x_4632_ = leanh::lean_box(0);
                        v_isShared_4633_ = v_isSharedCheck_4653_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_4611_);
                    leanh::lean_dec(v_a_4610_);
                    leanh::lean_dec_ref(v_inst_4608_);
                    v___x_4656_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4656_, 0, v___x_4630_);
                    leanh::lean_ctor_set(v___x_4656_, 1, v_m_4609_);
                    return v___x_4656_;
                }
            }
            1 => {
                v___x_4634_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_4635_ = lean_nat_add(v_size_4612_, v___x_4634_);
                leanh::lean_dec(v_size_4612_);
                leanh::lean_inc(v_bkt_4629_);
                v___x_4636_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4636_, 0, v_a_4610_);
                leanh::lean_ctor_set(v___x_4636_, 1, v_b_4611_);
                leanh::lean_ctor_set(v___x_4636_, 2, v_bkt_4629_);
                v_buckets_x27_4637_ = lean_array_uset(v_buckets_4613_, v___x_4628_, v___x_4636_);
                v___x_4638_ = leanh::lean_unsigned_to_nat(4);
                v___x_4639_ = lean_nat_mul(v_size_x27_4635_, v___x_4638_);
                v___x_4640_ = leanh::lean_unsigned_to_nat(3);
                v___x_4641_ = lean_nat_div(v___x_4639_, v___x_4640_);
                leanh::lean_dec(v___x_4639_);
                v___x_4642_ = lean_array_get_size(v_buckets_x27_4637_);
                v___x_4643_ = lean_nat_dec_le(v___x_4641_, v___x_4642_);
                leanh::lean_dec(v___x_4641_);
                if v___x_4643_ == 0 {
                    v_val_4644_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_4608_,
                        v_buckets_x27_4637_,
                    );
                    if v_isShared_4633_ == 0 {
                        leanh::lean_ctor_set(v___x_4632_, 1, v_val_4644_);
                        leanh::lean_ctor_set(v___x_4632_, 0, v_size_x27_4635_);
                        v___x_4646_ = v___x_4632_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4648_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_size_x27_4635_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4648_, 1, v_val_4644_);
                        v___x_4646_ = v_reuseFailAlloc_4648_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_4608_);
                    if v_isShared_4633_ == 0 {
                        leanh::lean_ctor_set(v___x_4632_, 1, v_buckets_x27_4637_);
                        leanh::lean_ctor_set(v___x_4632_, 0, v_size_x27_4635_);
                        v___x_4650_ = v___x_4632_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4652_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_size_x27_4635_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4652_, 1, v_buckets_x27_4637_);
                        v___x_4650_ = v_reuseFailAlloc_4652_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4647_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4647_, 0, v___x_4630_);
                leanh::lean_ctor_set(v___x_4647_, 1, v___x_4646_);
                return v___x_4647_;
            }
            3 => {
                v___x_4651_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4651_, 0, v___x_4630_);
                leanh::lean_ctor_set(v___x_4651_, 1, v___x_4650_);
                return v___x_4651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getThenInsertIfNew_x3f(
    mut v_00_u03b1_4657_: *mut leanh::LeanObject,
    mut v_00_u03b2_4658_: *mut leanh::LeanObject,
    mut v_inst_4659_: *mut leanh::LeanObject,
    mut v_inst_4660_: *mut leanh::LeanObject,
    mut v_m_4661_: *mut leanh::LeanObject,
    mut v_a_4662_: *mut leanh::LeanObject,
    mut v_b_4663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: u64 = 0;
    let mut v___x_4669_: u64 = 0;
    let mut v___x_4670_: u64 = 0;
    let mut v___x_4671_: u64 = 0;
    let mut v_fold_4672_: u64 = 0;
    let mut v___x_4673_: u64 = 0;
    let mut v___x_4674_: u64 = 0;
    let mut v___x_4675_: u64 = 0;
    let mut v___x_4676_: usize = 0;
    let mut v___x_4677_: usize = 0;
    let mut v___x_4678_: usize = 0;
    let mut v___x_4679_: usize = 0;
    let mut v___x_4680_: usize = 0;
    let mut v_bkt_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4685_: u8 = 0;
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: u8 = 0;
    let mut v_val_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4705_: u8 = 0;
    let mut v_unused_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4664_ = leanh::lean_ctor_get(v_m_4661_, 0);
                v_buckets_4665_ = leanh::lean_ctor_get(v_m_4661_, 1);
                v___x_4666_ = lean_array_get_size(v_buckets_4665_);
                leanh::lean_inc_ref(v_inst_4660_);
                leanh::lean_inc_n(v_a_4662_, 2);
                v___x_4667_ = leanh::lean_apply_1(v_inst_4660_, v_a_4662_);
                v___x_4668_ = 32u64;
                v___x_4669_ = leanh::lean_unbox_uint64(v___x_4667_);
                v___x_4670_ = lean_uint64_shift_right(v___x_4669_, v___x_4668_);
                v___x_4671_ = leanh::lean_unbox_uint64(v___x_4667_);
                leanh::lean_dec_ref(v___x_4667_);
                v_fold_4672_ = lean_uint64_xor(v___x_4671_, v___x_4670_);
                v___x_4673_ = 16u64;
                v___x_4674_ = lean_uint64_shift_right(v_fold_4672_, v___x_4673_);
                v___x_4675_ = lean_uint64_xor(v_fold_4672_, v___x_4674_);
                v___x_4676_ = lean_uint64_to_usize(v___x_4675_);
                v___x_4677_ = lean_usize_of_nat(v___x_4666_);
                v___x_4678_ = 1usize;
                v___x_4679_ = lean_usize_sub(v___x_4677_, v___x_4678_);
                v___x_4680_ = lean_usize_land(v___x_4676_, v___x_4679_);
                v_bkt_4681_ = lean_array_uget_borrowed(v_buckets_4665_, v___x_4680_);
                leanh::lean_inc(v_bkt_4681_);
                v___x_4682_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
                    v_inst_4659_,
                    v_a_4662_,
                    v_bkt_4681_,
                );
                if leanh::lean_obj_tag(v___x_4682_) == 0 {
                    leanh::lean_inc_ref(v_buckets_4665_);
                    leanh::lean_inc(v_size_4664_);
                    v_isSharedCheck_4705_ = (!leanh::lean_is_exclusive(v_m_4661_)) as u8;
                    if v_isSharedCheck_4705_ == 0 {
                        v_unused_4706_ = leanh::lean_ctor_get(v_m_4661_, 1);
                        leanh::lean_dec(v_unused_4706_);
                        v_unused_4707_ = leanh::lean_ctor_get(v_m_4661_, 0);
                        leanh::lean_dec(v_unused_4707_);
                        v___x_4684_ = v_m_4661_;
                        v_isShared_4685_ = v_isSharedCheck_4705_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_4661_);
                        v___x_4684_ = leanh::lean_box(0);
                        v_isShared_4685_ = v_isSharedCheck_4705_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_4663_);
                    leanh::lean_dec(v_a_4662_);
                    leanh::lean_dec_ref(v_inst_4660_);
                    v___x_4708_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4708_, 0, v___x_4682_);
                    leanh::lean_ctor_set(v___x_4708_, 1, v_m_4661_);
                    return v___x_4708_;
                }
            }
            1 => {
                v___x_4686_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_4687_ = lean_nat_add(v_size_4664_, v___x_4686_);
                leanh::lean_dec(v_size_4664_);
                leanh::lean_inc(v_bkt_4681_);
                v___x_4688_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4688_, 0, v_a_4662_);
                leanh::lean_ctor_set(v___x_4688_, 1, v_b_4663_);
                leanh::lean_ctor_set(v___x_4688_, 2, v_bkt_4681_);
                v_buckets_x27_4689_ = lean_array_uset(v_buckets_4665_, v___x_4680_, v___x_4688_);
                v___x_4690_ = leanh::lean_unsigned_to_nat(4);
                v___x_4691_ = lean_nat_mul(v_size_x27_4687_, v___x_4690_);
                v___x_4692_ = leanh::lean_unsigned_to_nat(3);
                v___x_4693_ = lean_nat_div(v___x_4691_, v___x_4692_);
                leanh::lean_dec(v___x_4691_);
                v___x_4694_ = lean_array_get_size(v_buckets_x27_4689_);
                v___x_4695_ = lean_nat_dec_le(v___x_4693_, v___x_4694_);
                leanh::lean_dec(v___x_4693_);
                if v___x_4695_ == 0 {
                    v_val_4696_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_inst_4660_,
                        v_buckets_x27_4689_,
                    );
                    if v_isShared_4685_ == 0 {
                        leanh::lean_ctor_set(v___x_4684_, 1, v_val_4696_);
                        leanh::lean_ctor_set(v___x_4684_, 0, v_size_x27_4687_);
                        v___x_4698_ = v___x_4684_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4700_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_size_x27_4687_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 1, v_val_4696_);
                        v___x_4698_ = v_reuseFailAlloc_4700_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_4660_);
                    if v_isShared_4685_ == 0 {
                        leanh::lean_ctor_set(v___x_4684_, 1, v_buckets_x27_4689_);
                        leanh::lean_ctor_set(v___x_4684_, 0, v_size_x27_4687_);
                        v___x_4702_ = v___x_4684_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4704_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_size_x27_4687_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 1, v_buckets_x27_4689_);
                        v___x_4702_ = v_reuseFailAlloc_4704_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4699_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4699_, 0, v___x_4682_);
                leanh::lean_ctor_set(v___x_4699_, 1, v___x_4698_);
                return v___x_4699_;
            }
            3 => {
                v___x_4703_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4703_, 0, v___x_4682_);
                leanh::lean_ctor_set(v___x_4703_, 1, v___x_4702_);
                return v___x_4703_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg___lam__0(
    mut v_inst_4709_: *mut leanh::LeanObject,
    mut v_inst_4710_: *mut leanh::LeanObject,
    mut v_x_4711_: *mut leanh::LeanObject,
    mut v_____s_4712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_4713_ = leanh::lean_ctor_get(v_x_4711_, 0);
    leanh::lean_inc(v_fst_4713_);
    v_snd_4714_ = leanh::lean_ctor_get(v_x_4711_, 1);
    leanh::lean_inc(v_snd_4714_);
    leanh::lean_dec_ref(v_x_4711_);
    v_r_4715_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_inst_4709_,
        v_inst_4710_,
        v_____s_4712_,
        v_fst_4713_,
        v_snd_4714_,
    );
    v___x_4716_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4716_, 0, v_r_4715_);
    return v___x_4716_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
    mut v_inst_4717_: *mut leanh::LeanObject,
    mut v_inst_4718_: *mut leanh::LeanObject,
    mut v_inst_4719_: *mut leanh::LeanObject,
    mut v_m_4720_: *mut leanh::LeanObject,
    mut v_l_4721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4722_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_4722_, 0, v_inst_4718_);
    leanh::lean_closure_set(v___f_4722_, 1, v_inst_4719_);
    v___x_4723_ = leanh::lean_apply_4(
        v_inst_4717_,
        leanh::lean_box(0),
        v_l_4721_,
        v_m_4720_,
        v___f_4722_,
    );
    return v___x_4723_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany(
    mut v_00_u03b1_4724_: *mut leanh::LeanObject,
    mut v_00_u03b2_4725_: *mut leanh::LeanObject,
    mut v_00_u03c1_4726_: *mut leanh::LeanObject,
    mut v_inst_4727_: *mut leanh::LeanObject,
    mut v_inst_4728_: *mut leanh::LeanObject,
    mut v_inst_4729_: *mut leanh::LeanObject,
    mut v_m_4730_: *mut leanh::LeanObject,
    mut v_l_4731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4732_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(
        v_inst_4727_,
        v_inst_4728_,
        v_inst_4729_,
        v_m_4730_,
        v_l_4731_,
    );
    return v___x_4732_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg___lam__0(
    mut v_inst_4733_: *mut leanh::LeanObject,
    mut v_inst_4734_: *mut leanh::LeanObject,
    mut v_a_4735_: *mut leanh::LeanObject,
    mut v_____s_4736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4737_ = leanh::lean_box(0);
    v_r_4738_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_4733_,
        v_inst_4734_,
        v_____s_4736_,
        v_a_4735_,
        v___x_4737_,
    );
    v___x_4739_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4739_, 0, v_r_4738_);
    return v___x_4739_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
    mut v_inst_4740_: *mut leanh::LeanObject,
    mut v_inst_4741_: *mut leanh::LeanObject,
    mut v_inst_4742_: *mut leanh::LeanObject,
    mut v_m_4743_: *mut leanh::LeanObject,
    mut v_l_4744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4745_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_4745_, 0, v_inst_4741_);
    leanh::lean_closure_set(v___f_4745_, 1, v_inst_4742_);
    v___x_4746_ = leanh::lean_apply_4(
        v_inst_4740_,
        leanh::lean_box(0),
        v_l_4744_,
        v_m_4743_,
        v___f_4745_,
    );
    return v___x_4746_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit(
    mut v_00_u03b1_4747_: *mut leanh::LeanObject,
    mut v_00_u03c1_4748_: *mut leanh::LeanObject,
    mut v_inst_4749_: *mut leanh::LeanObject,
    mut v_inst_4750_: *mut leanh::LeanObject,
    mut v_inst_4751_: *mut leanh::LeanObject,
    mut v_m_4752_: *mut leanh::LeanObject,
    mut v_l_4753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v_inst_4749_,
        v_inst_4750_,
        v_inst_4751_,
        v_m_4752_,
        v_l_4753_,
    );
    return v___x_4754_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
    mut v_inst_4755_: *mut leanh::LeanObject,
    mut v_inst_4756_: *mut leanh::LeanObject,
    mut v_m_4757_: *mut leanh::LeanObject,
    mut v_a_4758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: u64 = 0;
    let mut v___x_4763_: u64 = 0;
    let mut v___x_4764_: u64 = 0;
    let mut v___x_4765_: u64 = 0;
    let mut v_fold_4766_: u64 = 0;
    let mut v___x_4767_: u64 = 0;
    let mut v___x_4768_: u64 = 0;
    let mut v___x_4769_: u64 = 0;
    let mut v___x_4770_: usize = 0;
    let mut v___x_4771_: usize = 0;
    let mut v___x_4772_: usize = 0;
    let mut v___x_4773_: usize = 0;
    let mut v___x_4774_: usize = 0;
    let mut v___x_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4759_ = leanh::lean_ctor_get(v_m_4757_, 1);
    v___x_4760_ = lean_array_get_size(v_buckets_4759_);
    leanh::lean_inc(v_a_4758_);
    v___x_4761_ = leanh::lean_apply_1(v_inst_4756_, v_a_4758_);
    v___x_4762_ = 32u64;
    v___x_4763_ = leanh::lean_unbox_uint64(v___x_4761_);
    v___x_4764_ = lean_uint64_shift_right(v___x_4763_, v___x_4762_);
    v___x_4765_ = leanh::lean_unbox_uint64(v___x_4761_);
    leanh::lean_dec_ref(v___x_4761_);
    v_fold_4766_ = lean_uint64_xor(v___x_4765_, v___x_4764_);
    v___x_4767_ = 16u64;
    v___x_4768_ = lean_uint64_shift_right(v_fold_4766_, v___x_4767_);
    v___x_4769_ = lean_uint64_xor(v_fold_4766_, v___x_4768_);
    v___x_4770_ = lean_uint64_to_usize(v___x_4769_);
    v___x_4771_ = lean_usize_of_nat(v___x_4760_);
    v___x_4772_ = 1usize;
    v___x_4773_ = lean_usize_sub(v___x_4771_, v___x_4772_);
    v___x_4774_ = lean_usize_land(v___x_4770_, v___x_4773_);
    v___x_4775_ = lean_array_uget_borrowed(v_buckets_4759_, v___x_4774_);
    leanh::lean_inc(v___x_4775_);
    v___x_4776_ =
        l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(v_inst_4755_, v_a_4758_, v___x_4775_);
    return v___x_4776_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg___boxed(
    mut v_inst_4777_: *mut leanh::LeanObject,
    mut v_inst_4778_: *mut leanh::LeanObject,
    mut v_m_4779_: *mut leanh::LeanObject,
    mut v_a_4780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4781_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_inst_4777_,
        v_inst_4778_,
        v_m_4779_,
        v_a_4780_,
    );
    leanh::lean_dec_ref(v_m_4779_);
    return v_res_4781_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f(
    mut v_00_u03b1_4782_: *mut leanh::LeanObject,
    mut v_00_u03b2_4783_: *mut leanh::LeanObject,
    mut v_inst_4784_: *mut leanh::LeanObject,
    mut v_inst_4785_: *mut leanh::LeanObject,
    mut v_m_4786_: *mut leanh::LeanObject,
    mut v_a_4787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4788_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_inst_4784_,
        v_inst_4785_,
        v_m_4786_,
        v_a_4787_,
    );
    return v___x_4788_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___boxed(
    mut v_00_u03b1_4789_: *mut leanh::LeanObject,
    mut v_00_u03b2_4790_: *mut leanh::LeanObject,
    mut v_inst_4791_: *mut leanh::LeanObject,
    mut v_inst_4792_: *mut leanh::LeanObject,
    mut v_m_4793_: *mut leanh::LeanObject,
    mut v_a_4794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4795_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f(
        v_00_u03b1_4789_,
        v_00_u03b2_4790_,
        v_inst_4791_,
        v_inst_4792_,
        v_m_4793_,
        v_a_4794_,
    );
    leanh::lean_dec_ref(v_m_4793_);
    return v_res_4795_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
    mut v_inst_4796_: *mut leanh::LeanObject,
    mut v_inst_4797_: *mut leanh::LeanObject,
    mut v_m_4798_: *mut leanh::LeanObject,
    mut v_a_4799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: u64 = 0;
    let mut v___x_4804_: u64 = 0;
    let mut v___x_4805_: u64 = 0;
    let mut v___x_4806_: u64 = 0;
    let mut v_fold_4807_: u64 = 0;
    let mut v___x_4808_: u64 = 0;
    let mut v___x_4809_: u64 = 0;
    let mut v___x_4810_: u64 = 0;
    let mut v___x_4811_: usize = 0;
    let mut v___x_4812_: usize = 0;
    let mut v___x_4813_: usize = 0;
    let mut v___x_4814_: usize = 0;
    let mut v___x_4815_: usize = 0;
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4800_ = leanh::lean_ctor_get(v_m_4798_, 1);
    v___x_4801_ = lean_array_get_size(v_buckets_4800_);
    leanh::lean_inc(v_a_4799_);
    v___x_4802_ = leanh::lean_apply_1(v_inst_4797_, v_a_4799_);
    v___x_4803_ = 32u64;
    v___x_4804_ = leanh::lean_unbox_uint64(v___x_4802_);
    v___x_4805_ = lean_uint64_shift_right(v___x_4804_, v___x_4803_);
    v___x_4806_ = leanh::lean_unbox_uint64(v___x_4802_);
    leanh::lean_dec_ref(v___x_4802_);
    v_fold_4807_ = lean_uint64_xor(v___x_4806_, v___x_4805_);
    v___x_4808_ = 16u64;
    v___x_4809_ = lean_uint64_shift_right(v_fold_4807_, v___x_4808_);
    v___x_4810_ = lean_uint64_xor(v_fold_4807_, v___x_4809_);
    v___x_4811_ = lean_uint64_to_usize(v___x_4810_);
    v___x_4812_ = lean_usize_of_nat(v___x_4801_);
    v___x_4813_ = 1usize;
    v___x_4814_ = lean_usize_sub(v___x_4812_, v___x_4813_);
    v___x_4815_ = lean_usize_land(v___x_4811_, v___x_4814_);
    v___x_4816_ = lean_array_uget_borrowed(v_buckets_4800_, v___x_4815_);
    leanh::lean_inc(v___x_4816_);
    v___x_4817_ =
        l_Std_DHashMap_Internal_AssocList_getKey___redArg(v_inst_4796_, v_a_4799_, v___x_4816_);
    return v___x_4817_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg___boxed(
    mut v_inst_4818_: *mut leanh::LeanObject,
    mut v_inst_4819_: *mut leanh::LeanObject,
    mut v_m_4820_: *mut leanh::LeanObject,
    mut v_a_4821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4822_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_4818_,
        v_inst_4819_,
        v_m_4820_,
        v_a_4821_,
    );
    leanh::lean_dec_ref(v_m_4820_);
    return v_res_4822_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey(
    mut v_00_u03b1_4823_: *mut leanh::LeanObject,
    mut v_00_u03b2_4824_: *mut leanh::LeanObject,
    mut v_inst_4825_: *mut leanh::LeanObject,
    mut v_inst_4826_: *mut leanh::LeanObject,
    mut v_m_4827_: *mut leanh::LeanObject,
    mut v_a_4828_: *mut leanh::LeanObject,
    mut v_hma_4829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4830_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_inst_4825_,
        v_inst_4826_,
        v_m_4827_,
        v_a_4828_,
    );
    return v___x_4830_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey___boxed(
    mut v_00_u03b1_4831_: *mut leanh::LeanObject,
    mut v_00_u03b2_4832_: *mut leanh::LeanObject,
    mut v_inst_4833_: *mut leanh::LeanObject,
    mut v_inst_4834_: *mut leanh::LeanObject,
    mut v_m_4835_: *mut leanh::LeanObject,
    mut v_a_4836_: *mut leanh::LeanObject,
    mut v_hma_4837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4838_ = l_Std_DHashMap_Internal_Raw_u2080_getKey(
        v_00_u03b1_4831_,
        v_00_u03b2_4832_,
        v_inst_4833_,
        v_inst_4834_,
        v_m_4835_,
        v_a_4836_,
        v_hma_4837_,
    );
    leanh::lean_dec_ref(v_m_4835_);
    return v_res_4838_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
    mut v_inst_4839_: *mut leanh::LeanObject,
    mut v_inst_4840_: *mut leanh::LeanObject,
    mut v_m_4841_: *mut leanh::LeanObject,
    mut v_a_4842_: *mut leanh::LeanObject,
    mut v_fallback_4843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: u64 = 0;
    let mut v___x_4848_: u64 = 0;
    let mut v___x_4849_: u64 = 0;
    let mut v___x_4850_: u64 = 0;
    let mut v_fold_4851_: u64 = 0;
    let mut v___x_4852_: u64 = 0;
    let mut v___x_4853_: u64 = 0;
    let mut v___x_4854_: u64 = 0;
    let mut v___x_4855_: usize = 0;
    let mut v___x_4856_: usize = 0;
    let mut v___x_4857_: usize = 0;
    let mut v___x_4858_: usize = 0;
    let mut v___x_4859_: usize = 0;
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4844_ = leanh::lean_ctor_get(v_m_4841_, 1);
    v___x_4845_ = lean_array_get_size(v_buckets_4844_);
    leanh::lean_inc(v_a_4842_);
    v___x_4846_ = leanh::lean_apply_1(v_inst_4840_, v_a_4842_);
    v___x_4847_ = 32u64;
    v___x_4848_ = leanh::lean_unbox_uint64(v___x_4846_);
    v___x_4849_ = lean_uint64_shift_right(v___x_4848_, v___x_4847_);
    v___x_4850_ = leanh::lean_unbox_uint64(v___x_4846_);
    leanh::lean_dec_ref(v___x_4846_);
    v_fold_4851_ = lean_uint64_xor(v___x_4850_, v___x_4849_);
    v___x_4852_ = 16u64;
    v___x_4853_ = lean_uint64_shift_right(v_fold_4851_, v___x_4852_);
    v___x_4854_ = lean_uint64_xor(v_fold_4851_, v___x_4853_);
    v___x_4855_ = lean_uint64_to_usize(v___x_4854_);
    v___x_4856_ = lean_usize_of_nat(v___x_4845_);
    v___x_4857_ = 1usize;
    v___x_4858_ = lean_usize_sub(v___x_4856_, v___x_4857_);
    v___x_4859_ = lean_usize_land(v___x_4855_, v___x_4858_);
    v___x_4860_ = lean_array_uget_borrowed(v_buckets_4844_, v___x_4859_);
    leanh::lean_inc(v___x_4860_);
    v___x_4861_ = l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(
        v_inst_4839_,
        v_a_4842_,
        v_fallback_4843_,
        v___x_4860_,
    );
    return v___x_4861_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg___boxed(
    mut v_inst_4862_: *mut leanh::LeanObject,
    mut v_inst_4863_: *mut leanh::LeanObject,
    mut v_m_4864_: *mut leanh::LeanObject,
    mut v_a_4865_: *mut leanh::LeanObject,
    mut v_fallback_4866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4867_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
        v_inst_4862_,
        v_inst_4863_,
        v_m_4864_,
        v_a_4865_,
        v_fallback_4866_,
    );
    leanh::lean_dec(v_fallback_4866_);
    leanh::lean_dec_ref(v_m_4864_);
    return v_res_4867_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKeyD(
    mut v_00_u03b1_4868_: *mut leanh::LeanObject,
    mut v_00_u03b2_4869_: *mut leanh::LeanObject,
    mut v_inst_4870_: *mut leanh::LeanObject,
    mut v_inst_4871_: *mut leanh::LeanObject,
    mut v_m_4872_: *mut leanh::LeanObject,
    mut v_a_4873_: *mut leanh::LeanObject,
    mut v_fallback_4874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4875_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
        v_inst_4870_,
        v_inst_4871_,
        v_m_4872_,
        v_a_4873_,
        v_fallback_4874_,
    );
    return v___x_4875_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKeyD___boxed(
    mut v_00_u03b1_4876_: *mut leanh::LeanObject,
    mut v_00_u03b2_4877_: *mut leanh::LeanObject,
    mut v_inst_4878_: *mut leanh::LeanObject,
    mut v_inst_4879_: *mut leanh::LeanObject,
    mut v_m_4880_: *mut leanh::LeanObject,
    mut v_a_4881_: *mut leanh::LeanObject,
    mut v_fallback_4882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4883_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD(
        v_00_u03b1_4876_,
        v_00_u03b2_4877_,
        v_inst_4878_,
        v_inst_4879_,
        v_m_4880_,
        v_a_4881_,
        v_fallback_4882_,
    );
    leanh::lean_dec(v_fallback_4882_);
    leanh::lean_dec_ref(v_m_4880_);
    return v_res_4883_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
    mut v_inst_4884_: *mut leanh::LeanObject,
    mut v_inst_4885_: *mut leanh::LeanObject,
    mut v_inst_4886_: *mut leanh::LeanObject,
    mut v_m_4887_: *mut leanh::LeanObject,
    mut v_a_4888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: u64 = 0;
    let mut v___x_4893_: u64 = 0;
    let mut v___x_4894_: u64 = 0;
    let mut v___x_4895_: u64 = 0;
    let mut v_fold_4896_: u64 = 0;
    let mut v___x_4897_: u64 = 0;
    let mut v___x_4898_: u64 = 0;
    let mut v___x_4899_: u64 = 0;
    let mut v___x_4900_: usize = 0;
    let mut v___x_4901_: usize = 0;
    let mut v___x_4902_: usize = 0;
    let mut v___x_4903_: usize = 0;
    let mut v___x_4904_: usize = 0;
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4889_ = leanh::lean_ctor_get(v_m_4887_, 1);
    v___x_4890_ = lean_array_get_size(v_buckets_4889_);
    leanh::lean_inc(v_a_4888_);
    v___x_4891_ = leanh::lean_apply_1(v_inst_4885_, v_a_4888_);
    v___x_4892_ = 32u64;
    v___x_4893_ = leanh::lean_unbox_uint64(v___x_4891_);
    v___x_4894_ = lean_uint64_shift_right(v___x_4893_, v___x_4892_);
    v___x_4895_ = leanh::lean_unbox_uint64(v___x_4891_);
    leanh::lean_dec_ref(v___x_4891_);
    v_fold_4896_ = lean_uint64_xor(v___x_4895_, v___x_4894_);
    v___x_4897_ = 16u64;
    v___x_4898_ = lean_uint64_shift_right(v_fold_4896_, v___x_4897_);
    v___x_4899_ = lean_uint64_xor(v_fold_4896_, v___x_4898_);
    v___x_4900_ = lean_uint64_to_usize(v___x_4899_);
    v___x_4901_ = lean_usize_of_nat(v___x_4890_);
    v___x_4902_ = 1usize;
    v___x_4903_ = lean_usize_sub(v___x_4901_, v___x_4902_);
    v___x_4904_ = lean_usize_land(v___x_4900_, v___x_4903_);
    v___x_4905_ = lean_array_uget_borrowed(v_buckets_4889_, v___x_4904_);
    leanh::lean_inc(v___x_4905_);
    v___x_4906_ = l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg(
        v_inst_4884_,
        v_inst_4886_,
        v_a_4888_,
        v___x_4905_,
    );
    return v___x_4906_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___boxed(
    mut v_inst_4907_: *mut leanh::LeanObject,
    mut v_inst_4908_: *mut leanh::LeanObject,
    mut v_inst_4909_: *mut leanh::LeanObject,
    mut v_m_4910_: *mut leanh::LeanObject,
    mut v_a_4911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4912_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
        v_inst_4907_,
        v_inst_4908_,
        v_inst_4909_,
        v_m_4910_,
        v_a_4911_,
    );
    leanh::lean_dec_ref(v_m_4910_);
    leanh::lean_dec(v_inst_4909_);
    return v_res_4912_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x21(
    mut v_00_u03b1_4913_: *mut leanh::LeanObject,
    mut v_00_u03b2_4914_: *mut leanh::LeanObject,
    mut v_inst_4915_: *mut leanh::LeanObject,
    mut v_inst_4916_: *mut leanh::LeanObject,
    mut v_inst_4917_: *mut leanh::LeanObject,
    mut v_m_4918_: *mut leanh::LeanObject,
    mut v_a_4919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4920_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
        v_inst_4915_,
        v_inst_4916_,
        v_inst_4917_,
        v_m_4918_,
        v_a_4919_,
    );
    return v___x_4920_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___boxed(
    mut v_00_u03b1_4921_: *mut leanh::LeanObject,
    mut v_00_u03b2_4922_: *mut leanh::LeanObject,
    mut v_inst_4923_: *mut leanh::LeanObject,
    mut v_inst_4924_: *mut leanh::LeanObject,
    mut v_inst_4925_: *mut leanh::LeanObject,
    mut v_m_4926_: *mut leanh::LeanObject,
    mut v_a_4927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4928_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21(
        v_00_u03b1_4921_,
        v_00_u03b2_4922_,
        v_inst_4923_,
        v_inst_4924_,
        v_inst_4925_,
        v_m_4926_,
        v_a_4927_,
    );
    leanh::lean_dec_ref(v_m_4926_);
    leanh::lean_dec(v_inst_4925_);
    return v_res_4928_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Internal_Defs(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_RawDef(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Internal_List_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Index(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Power2_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Internal_Defs(
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
pub unsafe fn initialize_Std_Data_DHashMap_Internal_Defs(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_RawDef(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Internal_List_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_Index(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Power2_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Impl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Internal_Defs(builtin);
}