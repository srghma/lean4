// Lean compiler output
// Module: Std.Http.Internal.IndexMultiMap
// Imports: Init.Grind Init.Data.Int.OfNat Std.Data.HashMap
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_size, lean_array_to_list, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_sub, lean_nat_to_int, lean_string_length, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l_Array_instRepr___redArg___lam__0___boxed, l_Array_mapFinIdxM_map___redArg,
    l_Array_repr___redArg,
};
use crate::r#gen::Init::Data::Int::OfNat::{
    initialize_Init_Data_Int_OfNat, runtime_initialize_Init_Data_Int_OfNat,
};
use crate::r#gen::Init::Data::Repr::{
    l_List_repr___redArg, l_Prod_repr___boxed, l_Repr_addAppParen, l_instReprNat___lam__0___boxed,
    l_instReprTupleOfRepr___redArg___lam__0,
};
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
use crate::r#gen::Init::Prelude::{l_List_foldl___redArg, l_panic___redArg};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::l_Std_DHashMap_Internal_AssocList_foldrM___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
};
use crate::r#gen::Std::Data::HashMap::{
    initialize_Std_Data_HashMap, runtime_initialize_Std_Data_HashMap,
};
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0_value:
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
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1_value:
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
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2_value:
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
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3_value:
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
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4_value:
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
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5_value:
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
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6_value:
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
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7_value:
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
        core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8_value:
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
        core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [101, 110, 116, 114, 105, 101, 115, 0],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16_value:
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
    m_fun: l_instReprNat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17_value:
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
    m_fun: l_Array_instRepr___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [123, 32, 0],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20_value:
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
    m_data: [44, 0],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [105, 110, 100, 101, 120, 101, 115, 0],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24_value:
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
    m_fun: l_instReprTupleOfRepr___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25_value:
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
        83, 116, 100, 46, 72, 97, 115, 104, 77, 97, 112, 46, 111, 102, 76, 105, 115, 116, 32, 0,
    ],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [118, 97, 108, 105, 100, 105, 116, 121, 0],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29_value:
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
    m_data: [95, 0],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [32, 125, 0],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36_value:
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
    m_fun: l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__37_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__37:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__37_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_instInhabitedIndexMultiMap___closed__0_value:
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
static mut l_Std_Internal_instInhabitedIndexMultiMap___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_instInhabitedIndexMultiMap___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_instInhabitedIndexMultiMap___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_instInhabitedIndexMultiMap___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Internal_instInhabitedIndexMultiMap___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_instInhabitedIndexMultiMap___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Internal_instInhabitedIndexMultiMap___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_instInhabitedIndexMultiMap___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0_value:
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
static mut l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115,
        105, 99, 65, 117, 120, 0,
    ],
};
static mut l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
};
static mut l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
    ],
};
static mut l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__0(
    mut v_a_1267_: *mut leanh::LeanObject,
    mut v_b_1268_: *mut leanh::LeanObject,
    mut v_d_1269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1270_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1270_, 0, v_a_1267_);
    leanh::lean_ctor_set(v___x_1270_, 1, v_b_1268_);
    v___x_1271_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1271_, 0, v___x_1270_);
    leanh::lean_ctor_set(v___x_1271_, 1, v_d_1269_);
    return v___x_1271_;
}
pub unsafe fn l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__1(
    mut v___x_1272_: *mut leanh::LeanObject,
    mut v___f_1273_: *mut leanh::LeanObject,
    mut v_l_1274_: *mut leanh::LeanObject,
    mut v_acc_1275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1276_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_1272_,
        v___f_1273_,
        v_acc_1275_,
        v_l_1274_,
    );
    return v___x_1276_;
}
pub unsafe fn _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = leanh::lean_unsigned_to_nat(11);
    v___x_1313_ = lean_nat_to_int(v___x_1312_);
    return v___x_1313_;
}
pub unsafe fn _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32()
-> *mut leanh::LeanObject {
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18;
    v___x_1333_ = lean_string_length(v___x_1332_);
    return v___x_1333_;
}
pub unsafe fn _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1334_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32),
        core::ptr::addr_of_mut!(
            l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32_once
        ),
        _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32,
    );
    v___x_1335_ = lean_nat_to_int(v___x_1334_);
    return v___x_1335_;
}
pub unsafe fn l_Std_Internal_instReprIndexMultiMap_repr___redArg(
    mut v_inst_1344_: *mut leanh::LeanObject,
    mut v_inst_1345_: *mut leanh::LeanObject,
    mut v_x_1346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1351_: u8 = 0;
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1356_: u8 = 0;
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: u8 = 0;
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: u8 = 0;
    let mut v___f_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: usize = 0;
    let mut v___x_1407_: usize = 0;
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1411_: u8 = 0;
    let mut v_unused_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_entries_1347_ = leanh::lean_ctor_get(v_x_1346_, 0);
                v_indexes_1348_ = leanh::lean_ctor_get(v_x_1346_, 1);
                v_isSharedCheck_1413_ = (!leanh::lean_is_exclusive(v_x_1346_)) as u8;
                if v_isSharedCheck_1413_ == 0 {
                    v___x_1350_ = v_x_1346_;
                    v_isShared_1351_ = v_isSharedCheck_1413_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_1348_);
                    leanh::lean_inc(v_entries_1347_);
                    leanh::lean_dec(v_x_1346_);
                    v___x_1350_ = leanh::lean_box(0);
                    v_isShared_1351_ = v_isSharedCheck_1413_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1352_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
                v_buckets_1353_ = leanh::lean_ctor_get(v_indexes_1348_, 1);
                v_isSharedCheck_1411_ = (!leanh::lean_is_exclusive(v_indexes_1348_)) as u8;
                if v_isSharedCheck_1411_ == 0 {
                    v_unused_1412_ = leanh::lean_ctor_get(v_indexes_1348_, 0);
                    leanh::lean_dec(v_unused_1412_);
                    v___x_1355_ = v_indexes_1348_;
                    v_isShared_1356_ = v_isSharedCheck_1411_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1353_);
                    leanh::lean_dec(v_indexes_1348_);
                    v___x_1355_ = leanh::lean_box(0);
                    v_isShared_1356_ = v_isSharedCheck_1411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1357_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14;
                v___x_1358_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15;
                v___f_1359_ = leanh::lean_alloc_closure(
                    l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___f_1359_, 0, v_inst_1345_);
                leanh::lean_inc_ref(v_inst_1344_);
                v___x_1360_ = leanh::lean_alloc_closure(
                    l_Prod_repr___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                leanh::lean_closure_set(v___x_1360_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1360_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1360_, 2, v_inst_1344_);
                leanh::lean_closure_set(v___x_1360_, 3, v___f_1359_);
                v___x_1361_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19_once
                    ),
                    _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19,
                );
                v___x_1362_ = l_Array_repr___redArg(v___x_1360_, v_entries_1347_);
                if v_isShared_1356_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1355_, 4);
                    leanh::lean_ctor_set(v___x_1355_, 1, v___x_1362_);
                    leanh::lean_ctor_set(v___x_1355_, 0, v___x_1361_);
                    v___x_1364_ = v___x_1355_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1410_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1361_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 1, v___x_1362_);
                    v___x_1364_ = v_reuseFailAlloc_1410_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1365_ = 0;
                v___x_1366_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1366_, 0, v___x_1364_);
                leanh::lean_ctor_set_uint8(
                    v___x_1366_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1365_,
                );
                if v_isShared_1351_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1350_, 5);
                    leanh::lean_ctor_set(v___x_1350_, 1, v___x_1366_);
                    leanh::lean_ctor_set(v___x_1350_, 0, v___x_1358_);
                    v___x_1368_ = v___x_1350_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1409_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1358_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 1, v___x_1366_);
                    v___x_1368_ = v_reuseFailAlloc_1409_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1369_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21;
                v___x_1370_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1370_, 0, v___x_1368_);
                leanh::lean_ctor_set(v___x_1370_, 1, v___x_1369_);
                v___x_1371_ = leanh::lean_box(1);
                v___x_1372_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1372_, 0, v___x_1370_);
                leanh::lean_ctor_set(v___x_1372_, 1, v___x_1371_);
                v___x_1373_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23;
                v___x_1374_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1374_, 0, v___x_1372_);
                leanh::lean_ctor_set(v___x_1374_, 1, v___x_1373_);
                v___x_1375_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1375_, 0, v___x_1374_);
                leanh::lean_ctor_set(v___x_1375_, 1, v___x_1357_);
                v___f_1376_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24;
                v___x_1377_ = leanh::lean_alloc_closure(
                    l_Prod_repr___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                leanh::lean_closure_set(v___x_1377_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1377_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1377_, 2, v_inst_1344_);
                leanh::lean_closure_set(v___x_1377_, 3, v___f_1376_);
                v___x_1378_ = leanh::lean_unsigned_to_nat(0);
                v___x_1379_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26;
                v___x_1402_ = leanh::lean_box(0);
                v___x_1403_ = lean_array_get_size(v_buckets_1353_);
                v___x_1404_ = lean_nat_dec_lt(v___x_1378_, v___x_1403_);
                if v___x_1404_ == 0 {
                    leanh::lean_dec_ref(v_buckets_1353_);
                    v___y_1381_ = v___x_1402_;
                    state = 5;
                    continue;
                } else {
                    v___f_1405_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__37;
                    v___x_1406_ = lean_usize_of_nat(v___x_1403_);
                    v___x_1407_ = 0usize;
                    v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1352_,
                        v___f_1405_,
                        v_buckets_1353_,
                        v___x_1406_,
                        v___x_1407_,
                        v___x_1402_,
                    );
                    v___y_1381_ = v___x_1408_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1382_ = l_List_repr___redArg(v___x_1377_, v___y_1381_);
                v___x_1383_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1383_, 0, v___x_1379_);
                leanh::lean_ctor_set(v___x_1383_, 1, v___x_1382_);
                v___x_1384_ = l_Repr_addAppParen(v___x_1383_, v___x_1378_);
                v___x_1385_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1385_, 0, v___x_1361_);
                leanh::lean_ctor_set(v___x_1385_, 1, v___x_1384_);
                v___x_1386_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1386_, 0, v___x_1385_);
                leanh::lean_ctor_set_uint8(
                    v___x_1386_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1365_,
                );
                v___x_1387_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1387_, 0, v___x_1375_);
                leanh::lean_ctor_set(v___x_1387_, 1, v___x_1386_);
                v___x_1388_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1388_, 0, v___x_1387_);
                leanh::lean_ctor_set(v___x_1388_, 1, v___x_1369_);
                v___x_1389_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1389_, 0, v___x_1388_);
                leanh::lean_ctor_set(v___x_1389_, 1, v___x_1371_);
                v___x_1390_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28;
                v___x_1391_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1391_, 0, v___x_1389_);
                leanh::lean_ctor_set(v___x_1391_, 1, v___x_1390_);
                v___x_1392_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1392_, 0, v___x_1391_);
                leanh::lean_ctor_set(v___x_1392_, 1, v___x_1357_);
                v___x_1393_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30;
                v___x_1394_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1394_, 0, v___x_1392_);
                leanh::lean_ctor_set(v___x_1394_, 1, v___x_1393_);
                v___x_1395_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33_once
                    ),
                    _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33,
                );
                v___x_1396_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34;
                v___x_1397_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1397_, 0, v___x_1396_);
                leanh::lean_ctor_set(v___x_1397_, 1, v___x_1394_);
                v___x_1398_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35;
                v___x_1399_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1399_, 0, v___x_1397_);
                leanh::lean_ctor_set(v___x_1399_, 1, v___x_1398_);
                v___x_1400_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1400_, 0, v___x_1395_);
                leanh::lean_ctor_set(v___x_1400_, 1, v___x_1399_);
                v___x_1401_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1401_, 0, v___x_1400_);
                leanh::lean_ctor_set_uint8(
                    v___x_1401_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1365_,
                );
                return v___x_1401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_instReprIndexMultiMap_repr(
    mut v_00_u03b1_1414_: *mut leanh::LeanObject,
    mut v_00_u03b2_1415_: *mut leanh::LeanObject,
    mut v_inst_1416_: *mut leanh::LeanObject,
    mut v_inst_1417_: *mut leanh::LeanObject,
    mut v_inst_1418_: *mut leanh::LeanObject,
    mut v_inst_1419_: *mut leanh::LeanObject,
    mut v_x_1420_: *mut leanh::LeanObject,
    mut v_prec_1421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1422_ =
        l_Std_Internal_instReprIndexMultiMap_repr___redArg(v_inst_1418_, v_inst_1419_, v_x_1420_);
    return v___x_1422_;
}
pub unsafe fn l_Std_Internal_instReprIndexMultiMap_repr___boxed(
    mut v_00_u03b1_1423_: *mut leanh::LeanObject,
    mut v_00_u03b2_1424_: *mut leanh::LeanObject,
    mut v_inst_1425_: *mut leanh::LeanObject,
    mut v_inst_1426_: *mut leanh::LeanObject,
    mut v_inst_1427_: *mut leanh::LeanObject,
    mut v_inst_1428_: *mut leanh::LeanObject,
    mut v_x_1429_: *mut leanh::LeanObject,
    mut v_prec_1430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1431_ = l_Std_Internal_instReprIndexMultiMap_repr(
        v_00_u03b1_1423_,
        v_00_u03b2_1424_,
        v_inst_1425_,
        v_inst_1426_,
        v_inst_1427_,
        v_inst_1428_,
        v_x_1429_,
        v_prec_1430_,
    );
    leanh::lean_dec(v_prec_1430_);
    leanh::lean_dec_ref(v_inst_1426_);
    leanh::lean_dec_ref(v_inst_1425_);
    return v_res_1431_;
}
pub unsafe fn l_Std_Internal_instReprIndexMultiMap___redArg(
    mut v_inst_1432_: *mut leanh::LeanObject,
    mut v_inst_1433_: *mut leanh::LeanObject,
    mut v_inst_1434_: *mut leanh::LeanObject,
    mut v_inst_1435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1436_ = leanh::lean_alloc_closure(
        l_Std_Internal_instReprIndexMultiMap_repr___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    leanh::lean_closure_set(v___x_1436_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1436_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1436_, 2, v_inst_1432_);
    leanh::lean_closure_set(v___x_1436_, 3, v_inst_1433_);
    leanh::lean_closure_set(v___x_1436_, 4, v_inst_1434_);
    leanh::lean_closure_set(v___x_1436_, 5, v_inst_1435_);
    return v___x_1436_;
}
pub unsafe fn l_Std_Internal_instReprIndexMultiMap(
    mut v_00_u03b1_1437_: *mut leanh::LeanObject,
    mut v_00_u03b2_1438_: *mut leanh::LeanObject,
    mut v_inst_1439_: *mut leanh::LeanObject,
    mut v_inst_1440_: *mut leanh::LeanObject,
    mut v_inst_1441_: *mut leanh::LeanObject,
    mut v_inst_1442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1443_ = leanh::lean_alloc_closure(
        l_Std_Internal_instReprIndexMultiMap_repr___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    leanh::lean_closure_set(v___x_1443_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1443_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1443_, 2, v_inst_1439_);
    leanh::lean_closure_set(v___x_1443_, 3, v_inst_1440_);
    leanh::lean_closure_set(v___x_1443_, 4, v_inst_1441_);
    leanh::lean_closure_set(v___x_1443_, 5, v_inst_1442_);
    return v___x_1443_;
}
pub unsafe fn _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1446_ = leanh::lean_box(0);
    v___x_1447_ = leanh::lean_unsigned_to_nat(16);
    v___x_1448_ = lean_mk_array(v___x_1447_, v___x_1446_);
    return v___x_1448_;
}
pub unsafe fn _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1449_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_instInhabitedIndexMultiMap___closed__1),
        core::ptr::addr_of_mut!(l_Std_Internal_instInhabitedIndexMultiMap___closed__1_once),
        _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__1,
    );
    v___x_1450_ = leanh::lean_unsigned_to_nat(0);
    v___x_1451_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1451_, 0, v___x_1450_);
    leanh::lean_ctor_set(v___x_1451_, 1, v___x_1449_);
    return v___x_1451_;
}
pub unsafe fn _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1452_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_instInhabitedIndexMultiMap___closed__2),
        core::ptr::addr_of_mut!(l_Std_Internal_instInhabitedIndexMultiMap___closed__2_once),
        _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__2,
    );
    v___x_1453_ = l_Std_Internal_instInhabitedIndexMultiMap___closed__0;
    v___x_1454_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1454_, 0, v___x_1453_);
    leanh::lean_ctor_set(v___x_1454_, 1, v___x_1452_);
    return v___x_1454_;
}
pub unsafe fn l_Std_Internal_instInhabitedIndexMultiMap(
    mut v_00_u03b1_1455_: *mut leanh::LeanObject,
    mut v_00_u03b2_1456_: *mut leanh::LeanObject,
    mut v_inst_1457_: *mut leanh::LeanObject,
    mut v_inst_1458_: *mut leanh::LeanObject,
    mut v_inst_1459_: *mut leanh::LeanObject,
    mut v_inst_1460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1461_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_instInhabitedIndexMultiMap___closed__3),
        core::ptr::addr_of_mut!(l_Std_Internal_instInhabitedIndexMultiMap___closed__3_once),
        _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__3,
    );
    return v___x_1461_;
}
pub unsafe fn l_Std_Internal_instInhabitedIndexMultiMap___boxed(
    mut v_00_u03b1_1462_: *mut leanh::LeanObject,
    mut v_00_u03b2_1463_: *mut leanh::LeanObject,
    mut v_inst_1464_: *mut leanh::LeanObject,
    mut v_inst_1465_: *mut leanh::LeanObject,
    mut v_inst_1466_: *mut leanh::LeanObject,
    mut v_inst_1467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1468_ = l_Std_Internal_instInhabitedIndexMultiMap(
        v_00_u03b1_1462_,
        v_00_u03b2_1463_,
        v_inst_1464_,
        v_inst_1465_,
        v_inst_1466_,
        v_inst_1467_,
    );
    leanh::lean_dec(v_inst_1467_);
    leanh::lean_dec(v_inst_1466_);
    leanh::lean_dec_ref(v_inst_1465_);
    leanh::lean_dec_ref(v_inst_1464_);
    return v_res_1468_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instMembership(
    mut v_00_u03b1_1469_: *mut leanh::LeanObject,
    mut v_00_u03b2_1470_: *mut leanh::LeanObject,
    mut v_inst_1471_: *mut leanh::LeanObject,
    mut v_inst_1472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1473_ = leanh::lean_box(0);
    return v___x_1473_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instMembership___boxed(
    mut v_00_u03b1_1474_: *mut leanh::LeanObject,
    mut v_00_u03b2_1475_: *mut leanh::LeanObject,
    mut v_inst_1476_: *mut leanh::LeanObject,
    mut v_inst_1477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1478_ = l_Std_Internal_IndexMultiMap_instMembership(
        v_00_u03b1_1474_,
        v_00_u03b2_1475_,
        v_inst_1476_,
        v_inst_1477_,
    );
    leanh::lean_dec_ref(v_inst_1477_);
    leanh::lean_dec_ref(v_inst_1476_);
    return v_res_1478_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
    mut v_inst_1479_: *mut leanh::LeanObject,
    mut v_inst_1480_: *mut leanh::LeanObject,
    mut v_key_1481_: *mut leanh::LeanObject,
    mut v_map_1482_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_indexes_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: u8 = 0;
    v_indexes_1483_ = leanh::lean_ctor_get(v_map_1482_, 1);
    v___x_1484_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_1479_,
        v_inst_1480_,
        v_indexes_1483_,
        v_key_1481_,
    );
    return v___x_1484_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instDecidableMem___redArg___boxed(
    mut v_inst_1485_: *mut leanh::LeanObject,
    mut v_inst_1486_: *mut leanh::LeanObject,
    mut v_key_1487_: *mut leanh::LeanObject,
    mut v_map_1488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1489_: u8 = 0;
    let mut v_r_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1489_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_1485_,
        v_inst_1486_,
        v_key_1487_,
        v_map_1488_,
    );
    leanh::lean_dec_ref(v_map_1488_);
    v_r_1490_ = leanh::lean_box((v_res_1489_) as usize);
    return v_r_1490_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instDecidableMem(
    mut v_00_u03b1_1491_: *mut leanh::LeanObject,
    mut v_00_u03b2_1492_: *mut leanh::LeanObject,
    mut v_inst_1493_: *mut leanh::LeanObject,
    mut v_inst_1494_: *mut leanh::LeanObject,
    mut v_key_1495_: *mut leanh::LeanObject,
    mut v_map_1496_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1497_: u8 = 0;
    v___x_1497_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_1493_,
        v_inst_1494_,
        v_key_1495_,
        v_map_1496_,
    );
    return v___x_1497_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instDecidableMem___boxed(
    mut v_00_u03b1_1498_: *mut leanh::LeanObject,
    mut v_00_u03b2_1499_: *mut leanh::LeanObject,
    mut v_inst_1500_: *mut leanh::LeanObject,
    mut v_inst_1501_: *mut leanh::LeanObject,
    mut v_key_1502_: *mut leanh::LeanObject,
    mut v_map_1503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1504_: u8 = 0;
    let mut v_r_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1504_ = l_Std_Internal_IndexMultiMap_instDecidableMem(
        v_00_u03b1_1498_,
        v_00_u03b2_1499_,
        v_inst_1500_,
        v_inst_1501_,
        v_key_1502_,
        v_map_1503_,
    );
    leanh::lean_dec_ref(v_map_1503_);
    v_r_1505_ = leanh::lean_box((v_res_1504_) as usize);
    return v_r_1505_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(
    mut v___x_1506_: *mut leanh::LeanObject,
    mut v_entries_1507_: *mut leanh::LeanObject,
    mut v_x1_1508_: *mut leanh::LeanObject,
    mut v_x2_1509_: *mut leanh::LeanObject,
    mut v_x3_1510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ = lean_array_fget_borrowed(v___x_1506_, v_x1_1508_);
    v___x_1512_ = lean_array_fget_borrowed(v_entries_1507_, v___x_1511_);
    v_snd_1513_ = leanh::lean_ctor_get(v___x_1512_, 1);
    leanh::lean_inc(v_snd_1513_);
    return v_snd_1513_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed(
    mut v___x_1514_: *mut leanh::LeanObject,
    mut v_entries_1515_: *mut leanh::LeanObject,
    mut v_x1_1516_: *mut leanh::LeanObject,
    mut v_x2_1517_: *mut leanh::LeanObject,
    mut v_x3_1518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1519_ = l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(
        v___x_1514_,
        v_entries_1515_,
        v_x1_1516_,
        v_x2_1517_,
        v_x3_1518_,
    );
    leanh::lean_dec(v_x2_1517_);
    leanh::lean_dec(v_x1_1516_);
    leanh::lean_dec_ref(v_entries_1515_);
    leanh::lean_dec_ref(v___x_1514_);
    return v_res_1519_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_getAll___redArg(
    mut v_inst_1520_: *mut leanh::LeanObject,
    mut v_inst_1521_: *mut leanh::LeanObject,
    mut v_map_1522_: *mut leanh::LeanObject,
    mut v_key_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_entries_1524_ = leanh::lean_ctor_get(v_map_1522_, 0);
    leanh::lean_inc_ref(v_entries_1524_);
    v_indexes_1525_ = leanh::lean_ctor_get(v_map_1522_, 1);
    leanh::lean_inc_ref(v_indexes_1525_);
    leanh::lean_dec_ref(v_map_1522_);
    v___x_1526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_1520_,
        v_inst_1521_,
        v_indexes_1525_,
        v_key_1523_,
    );
    leanh::lean_dec_ref(v_indexes_1525_);
    leanh::lean_inc(v___x_1526_);
    v___f_1527_ = leanh::lean_alloc_closure(
        l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_1527_, 0, v___x_1526_);
    leanh::lean_closure_set(v___f_1527_, 1, v_entries_1524_);
    v___x_1528_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
    v___x_1529_ = lean_array_get_size(v___x_1526_);
    v___x_1530_ = leanh::lean_unsigned_to_nat(0);
    v___x_1531_ = lean_mk_empty_array_with_capacity(v___x_1529_);
    v_entries_1532_ = l_Array_mapFinIdxM_map___redArg(
        v___x_1528_,
        v___x_1526_,
        v___f_1527_,
        v___x_1529_,
        v___x_1530_,
        v___x_1531_,
    );
    return v_entries_1532_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_getAll(
    mut v_00_u03b1_1533_: *mut leanh::LeanObject,
    mut v_00_u03b2_1534_: *mut leanh::LeanObject,
    mut v_inst_1535_: *mut leanh::LeanObject,
    mut v_inst_1536_: *mut leanh::LeanObject,
    mut v_map_1537_: *mut leanh::LeanObject,
    mut v_key_1538_: *mut leanh::LeanObject,
    mut v_h_1539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_entries_1540_ = leanh::lean_ctor_get(v_map_1537_, 0);
    leanh::lean_inc_ref(v_entries_1540_);
    v_indexes_1541_ = leanh::lean_ctor_get(v_map_1537_, 1);
    leanh::lean_inc_ref(v_indexes_1541_);
    leanh::lean_dec_ref(v_map_1537_);
    v___x_1542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_1535_,
        v_inst_1536_,
        v_indexes_1541_,
        v_key_1538_,
    );
    leanh::lean_dec_ref(v_indexes_1541_);
    leanh::lean_inc(v___x_1542_);
    v___f_1543_ = leanh::lean_alloc_closure(
        l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_1543_, 0, v___x_1542_);
    leanh::lean_closure_set(v___f_1543_, 1, v_entries_1540_);
    v___x_1544_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
    v___x_1545_ = lean_array_get_size(v___x_1542_);
    v___x_1546_ = leanh::lean_unsigned_to_nat(0);
    v___x_1547_ = lean_mk_empty_array_with_capacity(v___x_1545_);
    v_entries_1548_ = l_Array_mapFinIdxM_map___redArg(
        v___x_1544_,
        v___x_1542_,
        v___f_1543_,
        v___x_1545_,
        v___x_1546_,
        v___x_1547_,
    );
    return v_entries_1548_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_get___redArg(
    mut v_inst_1549_: *mut leanh::LeanObject,
    mut v_inst_1550_: *mut leanh::LeanObject,
    mut v_map_1551_: *mut leanh::LeanObject,
    mut v_key_1552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_entries_1553_ = leanh::lean_ctor_get(v_map_1551_, 0);
    v_indexes_1554_ = leanh::lean_ctor_get(v_map_1551_, 1);
    v___x_1555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_1549_,
        v_inst_1550_,
        v_indexes_1554_,
        v_key_1552_,
    );
    v___x_1556_ = leanh::lean_unsigned_to_nat(0);
    v_entry_1557_ = lean_array_fget(v___x_1555_, v___x_1556_);
    leanh::lean_dec(v___x_1555_);
    v___x_1558_ = lean_array_fget_borrowed(v_entries_1553_, v_entry_1557_);
    leanh::lean_dec(v_entry_1557_);
    v_snd_1559_ = leanh::lean_ctor_get(v___x_1558_, 1);
    leanh::lean_inc(v_snd_1559_);
    return v_snd_1559_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_get___redArg___boxed(
    mut v_inst_1560_: *mut leanh::LeanObject,
    mut v_inst_1561_: *mut leanh::LeanObject,
    mut v_map_1562_: *mut leanh::LeanObject,
    mut v_key_1563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1564_ = l_Std_Internal_IndexMultiMap_get___redArg(
        v_inst_1560_,
        v_inst_1561_,
        v_map_1562_,
        v_key_1563_,
    );
    leanh::lean_dec_ref(v_map_1562_);
    return v_res_1564_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_get(
    mut v_00_u03b1_1565_: *mut leanh::LeanObject,
    mut v_00_u03b2_1566_: *mut leanh::LeanObject,
    mut v_inst_1567_: *mut leanh::LeanObject,
    mut v_inst_1568_: *mut leanh::LeanObject,
    mut v_map_1569_: *mut leanh::LeanObject,
    mut v_key_1570_: *mut leanh::LeanObject,
    mut v_h_1571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_entries_1572_ = leanh::lean_ctor_get(v_map_1569_, 0);
    v_indexes_1573_ = leanh::lean_ctor_get(v_map_1569_, 1);
    v___x_1574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v_inst_1567_,
        v_inst_1568_,
        v_indexes_1573_,
        v_key_1570_,
    );
    v___x_1575_ = leanh::lean_unsigned_to_nat(0);
    v_entry_1576_ = lean_array_fget(v___x_1574_, v___x_1575_);
    leanh::lean_dec(v___x_1574_);
    v___x_1577_ = lean_array_fget_borrowed(v_entries_1572_, v_entry_1576_);
    leanh::lean_dec(v_entry_1576_);
    v_snd_1578_ = leanh::lean_ctor_get(v___x_1577_, 1);
    leanh::lean_inc(v_snd_1578_);
    return v_snd_1578_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_get___boxed(
    mut v_00_u03b1_1579_: *mut leanh::LeanObject,
    mut v_00_u03b2_1580_: *mut leanh::LeanObject,
    mut v_inst_1581_: *mut leanh::LeanObject,
    mut v_inst_1582_: *mut leanh::LeanObject,
    mut v_map_1583_: *mut leanh::LeanObject,
    mut v_key_1584_: *mut leanh::LeanObject,
    mut v_h_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1586_ = l_Std_Internal_IndexMultiMap_get(
        v_00_u03b1_1579_,
        v_00_u03b2_1580_,
        v_inst_1581_,
        v_inst_1582_,
        v_map_1583_,
        v_key_1584_,
        v_h_1585_,
    );
    leanh::lean_dec_ref(v_map_1583_);
    return v_res_1586_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_getAll_x3f___redArg(
    mut v_inst_1587_: *mut leanh::LeanObject,
    mut v_inst_1588_: *mut leanh::LeanObject,
    mut v_map_1589_: *mut leanh::LeanObject,
    mut v_key_1590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1591_: u8 = 0;
    leanh::lean_inc(v_key_1590_);
    leanh::lean_inc_ref(v_inst_1588_);
    leanh::lean_inc_ref(v_inst_1587_);
    v___x_1591_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_1587_,
        v_inst_1588_,
        v_key_1590_,
        v_map_1589_,
    );
    if v___x_1591_ == 0 {
        let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_key_1590_);
        leanh::lean_dec_ref(v_map_1589_);
        leanh::lean_dec_ref(v_inst_1588_);
        leanh::lean_dec_ref(v_inst_1587_);
        v___x_1592_ = leanh::lean_box(0);
        return v___x_1592_;
    } else {
        let mut v_entries_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_entries_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_entries_1593_ = leanh::lean_ctor_get(v_map_1589_, 0);
        leanh::lean_inc_ref(v_entries_1593_);
        v_indexes_1594_ = leanh::lean_ctor_get(v_map_1589_, 1);
        leanh::lean_inc_ref(v_indexes_1594_);
        leanh::lean_dec_ref(v_map_1589_);
        v___x_1595_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v_inst_1587_,
            v_inst_1588_,
            v_indexes_1594_,
            v_key_1590_,
        );
        leanh::lean_dec_ref(v_indexes_1594_);
        leanh::lean_inc(v___x_1595_);
        v___f_1596_ = leanh::lean_alloc_closure(
            l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_1596_, 0, v___x_1595_);
        leanh::lean_closure_set(v___f_1596_, 1, v_entries_1593_);
        v___x_1597_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
        v___x_1598_ = lean_array_get_size(v___x_1595_);
        v___x_1599_ = leanh::lean_unsigned_to_nat(0);
        v___x_1600_ = lean_mk_empty_array_with_capacity(v___x_1598_);
        v_entries_1601_ = l_Array_mapFinIdxM_map___redArg(
            v___x_1597_,
            v___x_1595_,
            v___f_1596_,
            v___x_1598_,
            v___x_1599_,
            v___x_1600_,
        );
        v___x_1602_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1602_, 0, v_entries_1601_);
        return v___x_1602_;
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_getAll_x3f(
    mut v_00_u03b1_1603_: *mut leanh::LeanObject,
    mut v_00_u03b2_1604_: *mut leanh::LeanObject,
    mut v_inst_1605_: *mut leanh::LeanObject,
    mut v_inst_1606_: *mut leanh::LeanObject,
    mut v_map_1607_: *mut leanh::LeanObject,
    mut v_key_1608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1609_: u8 = 0;
    leanh::lean_inc(v_key_1608_);
    leanh::lean_inc_ref(v_inst_1606_);
    leanh::lean_inc_ref(v_inst_1605_);
    v___x_1609_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_1605_,
        v_inst_1606_,
        v_key_1608_,
        v_map_1607_,
    );
    if v___x_1609_ == 0 {
        let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_key_1608_);
        leanh::lean_dec_ref(v_map_1607_);
        leanh::lean_dec_ref(v_inst_1606_);
        leanh::lean_dec_ref(v_inst_1605_);
        v___x_1610_ = leanh::lean_box(0);
        return v___x_1610_;
    } else {
        let mut v_entries_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_entries_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_entries_1611_ = leanh::lean_ctor_get(v_map_1607_, 0);
        leanh::lean_inc_ref(v_entries_1611_);
        v_indexes_1612_ = leanh::lean_ctor_get(v_map_1607_, 1);
        leanh::lean_inc_ref(v_indexes_1612_);
        leanh::lean_dec_ref(v_map_1607_);
        v___x_1613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v_inst_1605_,
            v_inst_1606_,
            v_indexes_1612_,
            v_key_1608_,
        );
        leanh::lean_dec_ref(v_indexes_1612_);
        leanh::lean_inc(v___x_1613_);
        v___f_1614_ = leanh::lean_alloc_closure(
            l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_1614_, 0, v___x_1613_);
        leanh::lean_closure_set(v___f_1614_, 1, v_entries_1611_);
        v___x_1615_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
        v___x_1616_ = lean_array_get_size(v___x_1613_);
        v___x_1617_ = leanh::lean_unsigned_to_nat(0);
        v___x_1618_ = lean_mk_empty_array_with_capacity(v___x_1616_);
        v_entries_1619_ = l_Array_mapFinIdxM_map___redArg(
            v___x_1615_,
            v___x_1613_,
            v___f_1614_,
            v___x_1616_,
            v___x_1617_,
            v___x_1618_,
        );
        v___x_1620_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1620_, 0, v_entries_1619_);
        return v___x_1620_;
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_get_x3f___redArg(
    mut v_inst_1621_: *mut leanh::LeanObject,
    mut v_inst_1622_: *mut leanh::LeanObject,
    mut v_map_1623_: *mut leanh::LeanObject,
    mut v_key_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1625_: u8 = 0;
    leanh::lean_inc(v_key_1624_);
    leanh::lean_inc_ref(v_inst_1622_);
    leanh::lean_inc_ref(v_inst_1621_);
    v___x_1625_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_1621_,
        v_inst_1622_,
        v_key_1624_,
        v_map_1623_,
    );
    if v___x_1625_ == 0 {
        let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_key_1624_);
        leanh::lean_dec_ref(v_inst_1622_);
        leanh::lean_dec_ref(v_inst_1621_);
        v___x_1626_ = leanh::lean_box(0);
        return v___x_1626_;
    } else {
        let mut v_entries_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_entry_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_entries_1627_ = leanh::lean_ctor_get(v_map_1623_, 0);
        v_indexes_1628_ = leanh::lean_ctor_get(v_map_1623_, 1);
        v___x_1629_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v_inst_1621_,
            v_inst_1622_,
            v_indexes_1628_,
            v_key_1624_,
        );
        v___x_1630_ = leanh::lean_unsigned_to_nat(0);
        v_entry_1631_ = lean_array_fget(v___x_1629_, v___x_1630_);
        leanh::lean_dec(v___x_1629_);
        v___x_1632_ = lean_array_fget_borrowed(v_entries_1627_, v_entry_1631_);
        leanh::lean_dec(v_entry_1631_);
        v_snd_1633_ = leanh::lean_ctor_get(v___x_1632_, 1);
        leanh::lean_inc(v_snd_1633_);
        v___x_1634_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1634_, 0, v_snd_1633_);
        return v___x_1634_;
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_get_x3f___redArg___boxed(
    mut v_inst_1635_: *mut leanh::LeanObject,
    mut v_inst_1636_: *mut leanh::LeanObject,
    mut v_map_1637_: *mut leanh::LeanObject,
    mut v_key_1638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1639_ = l_Std_Internal_IndexMultiMap_get_x3f___redArg(
        v_inst_1635_,
        v_inst_1636_,
        v_map_1637_,
        v_key_1638_,
    );
    leanh::lean_dec_ref(v_map_1637_);
    return v_res_1639_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_get_x3f(
    mut v_00_u03b1_1640_: *mut leanh::LeanObject,
    mut v_00_u03b2_1641_: *mut leanh::LeanObject,
    mut v_inst_1642_: *mut leanh::LeanObject,
    mut v_inst_1643_: *mut leanh::LeanObject,
    mut v_map_1644_: *mut leanh::LeanObject,
    mut v_key_1645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1646_: u8 = 0;
    leanh::lean_inc(v_key_1645_);
    leanh::lean_inc_ref(v_inst_1643_);
    leanh::lean_inc_ref(v_inst_1642_);
    v___x_1646_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_1642_,
        v_inst_1643_,
        v_key_1645_,
        v_map_1644_,
    );
    if v___x_1646_ == 0 {
        let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_key_1645_);
        leanh::lean_dec_ref(v_inst_1643_);
        leanh::lean_dec_ref(v_inst_1642_);
        v___x_1647_ = leanh::lean_box(0);
        return v___x_1647_;
    } else {
        let mut v_entries_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_entry_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_entries_1648_ = leanh::lean_ctor_get(v_map_1644_, 0);
        v_indexes_1649_ = leanh::lean_ctor_get(v_map_1644_, 1);
        v___x_1650_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v_inst_1642_,
            v_inst_1643_,
            v_indexes_1649_,
            v_key_1645_,
        );
        v___x_1651_ = leanh::lean_unsigned_to_nat(0);
        v_entry_1652_ = lean_array_fget(v___x_1650_, v___x_1651_);
        leanh::lean_dec(v___x_1650_);
        v___x_1653_ = lean_array_fget_borrowed(v_entries_1648_, v_entry_1652_);
        leanh::lean_dec(v_entry_1652_);
        v_snd_1654_ = leanh::lean_ctor_get(v___x_1653_, 1);
        leanh::lean_inc(v_snd_1654_);
        v___x_1655_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1655_, 0, v_snd_1654_);
        return v___x_1655_;
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_get_x3f___boxed(
    mut v_00_u03b1_1656_: *mut leanh::LeanObject,
    mut v_00_u03b2_1657_: *mut leanh::LeanObject,
    mut v_inst_1658_: *mut leanh::LeanObject,
    mut v_inst_1659_: *mut leanh::LeanObject,
    mut v_map_1660_: *mut leanh::LeanObject,
    mut v_key_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1662_ = l_Std_Internal_IndexMultiMap_get_x3f(
        v_00_u03b1_1656_,
        v_00_u03b2_1657_,
        v_inst_1658_,
        v_inst_1659_,
        v_map_1660_,
        v_key_1661_,
    );
    leanh::lean_dec_ref(v_map_1660_);
    return v_res_1662_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(
    mut v_inst_1663_: *mut leanh::LeanObject,
    mut v_value_1664_: *mut leanh::LeanObject,
    mut v___x_1665_: *mut leanh::LeanObject,
    mut v___x_1666_: *mut leanh::LeanObject,
    mut v_a_1667_: *mut leanh::LeanObject,
    mut v_x_1668_: *mut leanh::LeanObject,
    mut v___y_1669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: u8 = 0;
    leanh::lean_inc(v_a_1667_);
    v___x_1670_ = leanh::lean_apply_2(v_inst_1663_, v_a_1667_, v_value_1664_);
    v___x_1671_ = (leanh::lean_unbox(v___x_1670_) as u8);
    if v___x_1671_ == 0 {
        let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_1667_);
        v___x_1672_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1672_, 0, v___x_1665_);
        return v___x_1672_;
    } else {
        let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_1665_);
        v___x_1673_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1673_, 0, v_a_1667_);
        v___x_1674_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1674_, 0, v___x_1673_);
        v___x_1675_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1675_, 0, v___x_1674_);
        leanh::lean_ctor_set(v___x_1675_, 1, v___x_1666_);
        v___x_1676_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1676_, 0, v___x_1675_);
        return v___x_1676_;
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed(
    mut v_inst_1677_: *mut leanh::LeanObject,
    mut v_value_1678_: *mut leanh::LeanObject,
    mut v___x_1679_: *mut leanh::LeanObject,
    mut v___x_1680_: *mut leanh::LeanObject,
    mut v_a_1681_: *mut leanh::LeanObject,
    mut v_x_1682_: *mut leanh::LeanObject,
    mut v___y_1683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1684_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(
        v_inst_1677_,
        v_value_1678_,
        v___x_1679_,
        v___x_1680_,
        v_a_1681_,
        v_x_1682_,
        v___y_1683_,
    );
    leanh::lean_dec_ref(v___y_1683_);
    return v_res_1684_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_hasEntry___redArg(
    mut v_inst_1688_: *mut leanh::LeanObject,
    mut v_inst_1689_: *mut leanh::LeanObject,
    mut v_map_1690_: *mut leanh::LeanObject,
    mut v_inst_1691_: *mut leanh::LeanObject,
    mut v_key_1692_: *mut leanh::LeanObject,
    mut v_value_1693_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1694_: u8 = 0;
    leanh::lean_inc(v_key_1692_);
    leanh::lean_inc_ref(v_inst_1689_);
    leanh::lean_inc_ref(v_inst_1688_);
    v___x_1694_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_1688_,
        v_inst_1689_,
        v_key_1692_,
        v_map_1690_,
    );
    if v___x_1694_ == 0 {
        leanh::lean_dec(v_value_1693_);
        leanh::lean_dec(v_key_1692_);
        leanh::lean_dec_ref(v_inst_1691_);
        leanh::lean_dec_ref(v_map_1690_);
        leanh::lean_dec_ref(v_inst_1689_);
        leanh::lean_dec_ref(v_inst_1688_);
        return v___x_1694_;
    } else {
        let mut v_entries_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_entries_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1707_: usize = 0;
        let mut v___x_1708_: usize = 0;
        let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_entries_1695_ = leanh::lean_ctor_get(v_map_1690_, 0);
        leanh::lean_inc_ref(v_entries_1695_);
        v_indexes_1696_ = leanh::lean_ctor_get(v_map_1690_, 1);
        leanh::lean_inc_ref(v_indexes_1696_);
        leanh::lean_dec_ref(v_map_1690_);
        v___x_1697_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v_inst_1688_,
            v_inst_1689_,
            v_indexes_1696_,
            v_key_1692_,
        );
        leanh::lean_dec_ref(v_indexes_1696_);
        leanh::lean_inc(v___x_1697_);
        v___f_1698_ = leanh::lean_alloc_closure(
            l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_1698_, 0, v___x_1697_);
        leanh::lean_closure_set(v___f_1698_, 1, v_entries_1695_);
        v___x_1699_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
        v___x_1700_ = lean_array_get_size(v___x_1697_);
        v___x_1701_ = leanh::lean_unsigned_to_nat(0);
        v___x_1702_ = lean_mk_empty_array_with_capacity(v___x_1700_);
        v_entries_1703_ = l_Array_mapFinIdxM_map___redArg(
            v___x_1699_,
            v___x_1697_,
            v___f_1698_,
            v___x_1700_,
            v___x_1701_,
            v___x_1702_,
        );
        v___x_1704_ = leanh::lean_box(0);
        v___x_1705_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0;
        v___f_1706_ = leanh::lean_alloc_closure(
            l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed
                as *mut core::ffi::c_void,
            7,
            4,
        );
        leanh::lean_closure_set(v___f_1706_, 0, v_inst_1691_);
        leanh::lean_closure_set(v___f_1706_, 1, v_value_1693_);
        leanh::lean_closure_set(v___f_1706_, 2, v___x_1705_);
        leanh::lean_closure_set(v___f_1706_, 3, v___x_1704_);
        v_sz_1707_ = lean_array_size(v_entries_1703_);
        v___x_1708_ = 0usize;
        v___x_1709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1699_,
            v_entries_1703_,
            v___f_1706_,
            v_sz_1707_,
            v___x_1708_,
            v___x_1705_,
        );
        v_fst_1710_ = leanh::lean_ctor_get(v___x_1709_, 0);
        leanh::lean_inc(v_fst_1710_);
        leanh::lean_dec(v___x_1709_);
        if leanh::lean_obj_tag(v_fst_1710_) == 0 {
            let mut v___x_1711_: u8 = 0;
            v___x_1711_ = 0;
            return v___x_1711_;
        } else {
            let mut v_val_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_1712_ = leanh::lean_ctor_get(v_fst_1710_, 0);
            leanh::lean_inc(v_val_1712_);
            leanh::lean_dec_ref_known(v_fst_1710_, 1);
            if leanh::lean_obj_tag(v_val_1712_) == 0 {
                let mut v___x_1713_: u8 = 0;
                v___x_1713_ = 0;
                return v___x_1713_;
            } else {
                leanh::lean_dec_ref_known(v_val_1712_, 1);
                return v___x_1694_;
            }
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_hasEntry___redArg___boxed(
    mut v_inst_1714_: *mut leanh::LeanObject,
    mut v_inst_1715_: *mut leanh::LeanObject,
    mut v_map_1716_: *mut leanh::LeanObject,
    mut v_inst_1717_: *mut leanh::LeanObject,
    mut v_key_1718_: *mut leanh::LeanObject,
    mut v_value_1719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1720_: u8 = 0;
    let mut v_r_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1720_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg(
        v_inst_1714_,
        v_inst_1715_,
        v_map_1716_,
        v_inst_1717_,
        v_key_1718_,
        v_value_1719_,
    );
    v_r_1721_ = leanh::lean_box((v_res_1720_) as usize);
    return v_r_1721_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_hasEntry(
    mut v_00_u03b1_1722_: *mut leanh::LeanObject,
    mut v_00_u03b2_1723_: *mut leanh::LeanObject,
    mut v_inst_1724_: *mut leanh::LeanObject,
    mut v_inst_1725_: *mut leanh::LeanObject,
    mut v_map_1726_: *mut leanh::LeanObject,
    mut v_inst_1727_: *mut leanh::LeanObject,
    mut v_key_1728_: *mut leanh::LeanObject,
    mut v_value_1729_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1730_: u8 = 0;
    leanh::lean_inc(v_key_1728_);
    leanh::lean_inc_ref(v_inst_1725_);
    leanh::lean_inc_ref(v_inst_1724_);
    v___x_1730_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_1724_,
        v_inst_1725_,
        v_key_1728_,
        v_map_1726_,
    );
    if v___x_1730_ == 0 {
        leanh::lean_dec(v_value_1729_);
        leanh::lean_dec(v_key_1728_);
        leanh::lean_dec_ref(v_inst_1727_);
        leanh::lean_dec_ref(v_map_1726_);
        leanh::lean_dec_ref(v_inst_1725_);
        leanh::lean_dec_ref(v_inst_1724_);
        return v___x_1730_;
    } else {
        let mut v_entries_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_entries_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1743_: usize = 0;
        let mut v___x_1744_: usize = 0;
        let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_entries_1731_ = leanh::lean_ctor_get(v_map_1726_, 0);
        leanh::lean_inc_ref(v_entries_1731_);
        v_indexes_1732_ = leanh::lean_ctor_get(v_map_1726_, 1);
        leanh::lean_inc_ref(v_indexes_1732_);
        leanh::lean_dec_ref(v_map_1726_);
        v___x_1733_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v_inst_1724_,
            v_inst_1725_,
            v_indexes_1732_,
            v_key_1728_,
        );
        leanh::lean_dec_ref(v_indexes_1732_);
        leanh::lean_inc(v___x_1733_);
        v___f_1734_ = leanh::lean_alloc_closure(
            l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_1734_, 0, v___x_1733_);
        leanh::lean_closure_set(v___f_1734_, 1, v_entries_1731_);
        v___x_1735_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
        v___x_1736_ = lean_array_get_size(v___x_1733_);
        v___x_1737_ = leanh::lean_unsigned_to_nat(0);
        v___x_1738_ = lean_mk_empty_array_with_capacity(v___x_1736_);
        v_entries_1739_ = l_Array_mapFinIdxM_map___redArg(
            v___x_1735_,
            v___x_1733_,
            v___f_1734_,
            v___x_1736_,
            v___x_1737_,
            v___x_1738_,
        );
        v___x_1740_ = leanh::lean_box(0);
        v___x_1741_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0;
        v___f_1742_ = leanh::lean_alloc_closure(
            l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed
                as *mut core::ffi::c_void,
            7,
            4,
        );
        leanh::lean_closure_set(v___f_1742_, 0, v_inst_1727_);
        leanh::lean_closure_set(v___f_1742_, 1, v_value_1729_);
        leanh::lean_closure_set(v___f_1742_, 2, v___x_1741_);
        leanh::lean_closure_set(v___f_1742_, 3, v___x_1740_);
        v_sz_1743_ = lean_array_size(v_entries_1739_);
        v___x_1744_ = 0usize;
        v___x_1745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1735_,
            v_entries_1739_,
            v___f_1742_,
            v_sz_1743_,
            v___x_1744_,
            v___x_1741_,
        );
        v_fst_1746_ = leanh::lean_ctor_get(v___x_1745_, 0);
        leanh::lean_inc(v_fst_1746_);
        leanh::lean_dec(v___x_1745_);
        if leanh::lean_obj_tag(v_fst_1746_) == 0 {
            let mut v___x_1747_: u8 = 0;
            v___x_1747_ = 0;
            return v___x_1747_;
        } else {
            let mut v_val_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_1748_ = leanh::lean_ctor_get(v_fst_1746_, 0);
            leanh::lean_inc(v_val_1748_);
            leanh::lean_dec_ref_known(v_fst_1746_, 1);
            if leanh::lean_obj_tag(v_val_1748_) == 0 {
                let mut v___x_1749_: u8 = 0;
                v___x_1749_ = 0;
                return v___x_1749_;
            } else {
                leanh::lean_dec_ref_known(v_val_1748_, 1);
                return v___x_1730_;
            }
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_hasEntry___boxed(
    mut v_00_u03b1_1750_: *mut leanh::LeanObject,
    mut v_00_u03b2_1751_: *mut leanh::LeanObject,
    mut v_inst_1752_: *mut leanh::LeanObject,
    mut v_inst_1753_: *mut leanh::LeanObject,
    mut v_map_1754_: *mut leanh::LeanObject,
    mut v_inst_1755_: *mut leanh::LeanObject,
    mut v_key_1756_: *mut leanh::LeanObject,
    mut v_value_1757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1758_: u8 = 0;
    let mut v_r_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1758_ = l_Std_Internal_IndexMultiMap_hasEntry(
        v_00_u03b1_1750_,
        v_00_u03b2_1751_,
        v_inst_1752_,
        v_inst_1753_,
        v_map_1754_,
        v_inst_1755_,
        v_key_1756_,
        v_value_1757_,
    );
    v_r_1759_ = leanh::lean_box((v_res_1758_) as usize);
    return v_r_1759_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_getLast_x3f___redArg(
    mut v_inst_1760_: *mut leanh::LeanObject,
    mut v_inst_1761_: *mut leanh::LeanObject,
    mut v_map_1762_: *mut leanh::LeanObject,
    mut v_key_1763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1764_: u8 = 0;
    leanh::lean_inc(v_key_1763_);
    leanh::lean_inc_ref(v_inst_1761_);
    leanh::lean_inc_ref(v_inst_1760_);
    v___x_1764_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_1760_,
        v_inst_1761_,
        v_key_1763_,
        v_map_1762_,
    );
    if v___x_1764_ == 0 {
        let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_key_1763_);
        leanh::lean_dec_ref(v_map_1762_);
        leanh::lean_dec_ref(v_inst_1761_);
        leanh::lean_dec_ref(v_inst_1760_);
        v___x_1765_ = leanh::lean_box(0);
        return v___x_1765_;
    } else {
        let mut v_entries_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_entries_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1778_: u8 = 0;
        v_entries_1766_ = leanh::lean_ctor_get(v_map_1762_, 0);
        leanh::lean_inc_ref(v_entries_1766_);
        v_indexes_1767_ = leanh::lean_ctor_get(v_map_1762_, 1);
        leanh::lean_inc_ref(v_indexes_1767_);
        leanh::lean_dec_ref(v_map_1762_);
        v___x_1768_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v_inst_1760_,
            v_inst_1761_,
            v_indexes_1767_,
            v_key_1763_,
        );
        leanh::lean_dec_ref(v_indexes_1767_);
        leanh::lean_inc(v___x_1768_);
        v___f_1769_ = leanh::lean_alloc_closure(
            l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_1769_, 0, v___x_1768_);
        leanh::lean_closure_set(v___f_1769_, 1, v_entries_1766_);
        v___x_1770_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
        v___x_1771_ = lean_array_get_size(v___x_1768_);
        v___x_1772_ = leanh::lean_unsigned_to_nat(0);
        v___x_1773_ = lean_mk_empty_array_with_capacity(v___x_1771_);
        v_entries_1774_ = l_Array_mapFinIdxM_map___redArg(
            v___x_1770_,
            v___x_1768_,
            v___f_1769_,
            v___x_1771_,
            v___x_1772_,
            v___x_1773_,
        );
        v___x_1775_ = lean_array_get_size(v_entries_1774_);
        v___x_1776_ = leanh::lean_unsigned_to_nat(1);
        v___x_1777_ = lean_nat_sub(v___x_1775_, v___x_1776_);
        v___x_1778_ = lean_nat_dec_lt(v___x_1777_, v___x_1775_);
        if v___x_1778_ == 0 {
            let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1777_);
            leanh::lean_dec(v_entries_1774_);
            v___x_1779_ = leanh::lean_box(0);
            return v___x_1779_;
        } else {
            let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1780_ = lean_array_fget(v_entries_1774_, v___x_1777_);
            leanh::lean_dec(v___x_1777_);
            leanh::lean_dec(v_entries_1774_);
            v___x_1781_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1781_, 0, v___x_1780_);
            return v___x_1781_;
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_getLast_x3f(
    mut v_00_u03b1_1782_: *mut leanh::LeanObject,
    mut v_00_u03b2_1783_: *mut leanh::LeanObject,
    mut v_inst_1784_: *mut leanh::LeanObject,
    mut v_inst_1785_: *mut leanh::LeanObject,
    mut v_map_1786_: *mut leanh::LeanObject,
    mut v_key_1787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1788_: u8 = 0;
    leanh::lean_inc(v_key_1787_);
    leanh::lean_inc_ref(v_inst_1785_);
    leanh::lean_inc_ref(v_inst_1784_);
    v___x_1788_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_1784_,
        v_inst_1785_,
        v_key_1787_,
        v_map_1786_,
    );
    if v___x_1788_ == 0 {
        let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_key_1787_);
        leanh::lean_dec_ref(v_map_1786_);
        leanh::lean_dec_ref(v_inst_1785_);
        leanh::lean_dec_ref(v_inst_1784_);
        v___x_1789_ = leanh::lean_box(0);
        return v___x_1789_;
    } else {
        let mut v_entries_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_entries_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1802_: u8 = 0;
        v_entries_1790_ = leanh::lean_ctor_get(v_map_1786_, 0);
        leanh::lean_inc_ref(v_entries_1790_);
        v_indexes_1791_ = leanh::lean_ctor_get(v_map_1786_, 1);
        leanh::lean_inc_ref(v_indexes_1791_);
        leanh::lean_dec_ref(v_map_1786_);
        v___x_1792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v_inst_1784_,
            v_inst_1785_,
            v_indexes_1791_,
            v_key_1787_,
        );
        leanh::lean_dec_ref(v_indexes_1791_);
        leanh::lean_inc(v___x_1792_);
        v___f_1793_ = leanh::lean_alloc_closure(
            l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            2,
        );
        leanh::lean_closure_set(v___f_1793_, 0, v___x_1792_);
        leanh::lean_closure_set(v___f_1793_, 1, v_entries_1790_);
        v___x_1794_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
        v___x_1795_ = lean_array_get_size(v___x_1792_);
        v___x_1796_ = leanh::lean_unsigned_to_nat(0);
        v___x_1797_ = lean_mk_empty_array_with_capacity(v___x_1795_);
        v_entries_1798_ = l_Array_mapFinIdxM_map___redArg(
            v___x_1794_,
            v___x_1792_,
            v___f_1793_,
            v___x_1795_,
            v___x_1796_,
            v___x_1797_,
        );
        v___x_1799_ = lean_array_get_size(v_entries_1798_);
        v___x_1800_ = leanh::lean_unsigned_to_nat(1);
        v___x_1801_ = lean_nat_sub(v___x_1799_, v___x_1800_);
        v___x_1802_ = lean_nat_dec_lt(v___x_1801_, v___x_1799_);
        if v___x_1802_ == 0 {
            let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1801_);
            leanh::lean_dec(v_entries_1798_);
            v___x_1803_ = leanh::lean_box(0);
            return v___x_1803_;
        } else {
            let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1804_ = lean_array_fget(v_entries_1798_, v___x_1801_);
            leanh::lean_dec(v___x_1801_);
            leanh::lean_dec(v_entries_1798_);
            v___x_1805_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1805_, 0, v___x_1804_);
            return v___x_1805_;
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_getD___redArg(
    mut v_inst_1806_: *mut leanh::LeanObject,
    mut v_inst_1807_: *mut leanh::LeanObject,
    mut v_map_1808_: *mut leanh::LeanObject,
    mut v_key_1809_: *mut leanh::LeanObject,
    mut v_d_1810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1811_: u8 = 0;
    leanh::lean_inc(v_key_1809_);
    leanh::lean_inc_ref(v_inst_1807_);
    leanh::lean_inc_ref(v_inst_1806_);
    v___x_1811_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_1806_,
        v_inst_1807_,
        v_key_1809_,
        v_map_1808_,
    );
    if v___x_1811_ == 0 {
        leanh::lean_dec(v_key_1809_);
        leanh::lean_dec_ref(v_inst_1807_);
        leanh::lean_dec_ref(v_inst_1806_);
        leanh::lean_inc(v_d_1810_);
        return v_d_1810_;
    } else {
        let mut v_entries_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_entry_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_entries_1812_ = leanh::lean_ctor_get(v_map_1808_, 0);
        v_indexes_1813_ = leanh::lean_ctor_get(v_map_1808_, 1);
        v___x_1814_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v_inst_1806_,
            v_inst_1807_,
            v_indexes_1813_,
            v_key_1809_,
        );
        v___x_1815_ = leanh::lean_unsigned_to_nat(0);
        v_entry_1816_ = lean_array_fget(v___x_1814_, v___x_1815_);
        leanh::lean_dec(v___x_1814_);
        v___x_1817_ = lean_array_fget_borrowed(v_entries_1812_, v_entry_1816_);
        leanh::lean_dec(v_entry_1816_);
        v_snd_1818_ = leanh::lean_ctor_get(v___x_1817_, 1);
        leanh::lean_inc(v_snd_1818_);
        return v_snd_1818_;
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_getD___redArg___boxed(
    mut v_inst_1819_: *mut leanh::LeanObject,
    mut v_inst_1820_: *mut leanh::LeanObject,
    mut v_map_1821_: *mut leanh::LeanObject,
    mut v_key_1822_: *mut leanh::LeanObject,
    mut v_d_1823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1824_ = l_Std_Internal_IndexMultiMap_getD___redArg(
        v_inst_1819_,
        v_inst_1820_,
        v_map_1821_,
        v_key_1822_,
        v_d_1823_,
    );
    leanh::lean_dec(v_d_1823_);
    leanh::lean_dec_ref(v_map_1821_);
    return v_res_1824_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_getD(
    mut v_00_u03b1_1825_: *mut leanh::LeanObject,
    mut v_00_u03b2_1826_: *mut leanh::LeanObject,
    mut v_inst_1827_: *mut leanh::LeanObject,
    mut v_inst_1828_: *mut leanh::LeanObject,
    mut v_map_1829_: *mut leanh::LeanObject,
    mut v_key_1830_: *mut leanh::LeanObject,
    mut v_d_1831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1832_: u8 = 0;
    leanh::lean_inc(v_key_1830_);
    leanh::lean_inc_ref(v_inst_1828_);
    leanh::lean_inc_ref(v_inst_1827_);
    v___x_1832_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_1827_,
        v_inst_1828_,
        v_key_1830_,
        v_map_1829_,
    );
    if v___x_1832_ == 0 {
        leanh::lean_dec(v_key_1830_);
        leanh::lean_dec_ref(v_inst_1828_);
        leanh::lean_dec_ref(v_inst_1827_);
        leanh::lean_inc(v_d_1831_);
        return v_d_1831_;
    } else {
        let mut v_entries_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_entry_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_entries_1833_ = leanh::lean_ctor_get(v_map_1829_, 0);
        v_indexes_1834_ = leanh::lean_ctor_get(v_map_1829_, 1);
        v___x_1835_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v_inst_1827_,
            v_inst_1828_,
            v_indexes_1834_,
            v_key_1830_,
        );
        v___x_1836_ = leanh::lean_unsigned_to_nat(0);
        v_entry_1837_ = lean_array_fget(v___x_1835_, v___x_1836_);
        leanh::lean_dec(v___x_1835_);
        v___x_1838_ = lean_array_fget_borrowed(v_entries_1833_, v_entry_1837_);
        leanh::lean_dec(v_entry_1837_);
        v_snd_1839_ = leanh::lean_ctor_get(v___x_1838_, 1);
        leanh::lean_inc(v_snd_1839_);
        return v_snd_1839_;
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_getD___boxed(
    mut v_00_u03b1_1840_: *mut leanh::LeanObject,
    mut v_00_u03b2_1841_: *mut leanh::LeanObject,
    mut v_inst_1842_: *mut leanh::LeanObject,
    mut v_inst_1843_: *mut leanh::LeanObject,
    mut v_map_1844_: *mut leanh::LeanObject,
    mut v_key_1845_: *mut leanh::LeanObject,
    mut v_d_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1847_ = l_Std_Internal_IndexMultiMap_getD(
        v_00_u03b1_1840_,
        v_00_u03b2_1841_,
        v_inst_1842_,
        v_inst_1843_,
        v_map_1844_,
        v_key_1845_,
        v_d_1846_,
    );
    leanh::lean_dec(v_d_1846_);
    leanh::lean_dec_ref(v_map_1844_);
    return v_res_1847_;
}
pub unsafe fn _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1851_ = l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2;
    v___x_1852_ = leanh::lean_unsigned_to_nat(14);
    v___x_1853_ = leanh::lean_unsigned_to_nat(22);
    v___x_1854_ = l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1;
    v___x_1855_ = l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0;
    v___x_1856_ = l_mkPanicMessageWithDecl(
        v___x_1855_,
        v___x_1854_,
        v___x_1853_,
        v___x_1852_,
        v___x_1851_,
    );
    return v___x_1856_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_get_x21___redArg(
    mut v_inst_1857_: *mut leanh::LeanObject,
    mut v_inst_1858_: *mut leanh::LeanObject,
    mut v_inst_1859_: *mut leanh::LeanObject,
    mut v_map_1860_: *mut leanh::LeanObject,
    mut v_key_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1862_: u8 = 0;
    leanh::lean_inc(v_key_1861_);
    leanh::lean_inc_ref(v_inst_1858_);
    leanh::lean_inc_ref(v_inst_1857_);
    v___x_1862_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_1857_,
        v_inst_1858_,
        v_key_1861_,
        v_map_1860_,
    );
    if v___x_1862_ == 0 {
        let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_key_1861_);
        leanh::lean_dec_ref(v_inst_1858_);
        leanh::lean_dec_ref(v_inst_1857_);
        v___x_1863_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once),
            _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3,
        );
        v___x_1864_ = l_panic___redArg(v_inst_1859_, v___x_1863_);
        return v___x_1864_;
    } else {
        let mut v_entries_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_entry_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_entries_1865_ = leanh::lean_ctor_get(v_map_1860_, 0);
        v_indexes_1866_ = leanh::lean_ctor_get(v_map_1860_, 1);
        v___x_1867_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v_inst_1857_,
            v_inst_1858_,
            v_indexes_1866_,
            v_key_1861_,
        );
        v___x_1868_ = leanh::lean_unsigned_to_nat(0);
        v_entry_1869_ = lean_array_fget(v___x_1867_, v___x_1868_);
        leanh::lean_dec(v___x_1867_);
        v___x_1870_ = lean_array_fget_borrowed(v_entries_1865_, v_entry_1869_);
        leanh::lean_dec(v_entry_1869_);
        v_snd_1871_ = leanh::lean_ctor_get(v___x_1870_, 1);
        leanh::lean_inc(v_snd_1871_);
        return v_snd_1871_;
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_get_x21___redArg___boxed(
    mut v_inst_1872_: *mut leanh::LeanObject,
    mut v_inst_1873_: *mut leanh::LeanObject,
    mut v_inst_1874_: *mut leanh::LeanObject,
    mut v_map_1875_: *mut leanh::LeanObject,
    mut v_key_1876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1877_ = l_Std_Internal_IndexMultiMap_get_x21___redArg(
        v_inst_1872_,
        v_inst_1873_,
        v_inst_1874_,
        v_map_1875_,
        v_key_1876_,
    );
    leanh::lean_dec_ref(v_map_1875_);
    leanh::lean_dec(v_inst_1874_);
    return v_res_1877_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_get_x21(
    mut v_00_u03b1_1878_: *mut leanh::LeanObject,
    mut v_00_u03b2_1879_: *mut leanh::LeanObject,
    mut v_inst_1880_: *mut leanh::LeanObject,
    mut v_inst_1881_: *mut leanh::LeanObject,
    mut v_inst_1882_: *mut leanh::LeanObject,
    mut v_map_1883_: *mut leanh::LeanObject,
    mut v_key_1884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1885_: u8 = 0;
    leanh::lean_inc(v_key_1884_);
    leanh::lean_inc_ref(v_inst_1881_);
    leanh::lean_inc_ref(v_inst_1880_);
    v___x_1885_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_1880_,
        v_inst_1881_,
        v_key_1884_,
        v_map_1883_,
    );
    if v___x_1885_ == 0 {
        let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_key_1884_);
        leanh::lean_dec_ref(v_inst_1881_);
        leanh::lean_dec_ref(v_inst_1880_);
        v___x_1886_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once),
            _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3,
        );
        v___x_1887_ = l_panic___redArg(v_inst_1882_, v___x_1886_);
        return v___x_1887_;
    } else {
        let mut v_entries_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_entry_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_entries_1888_ = leanh::lean_ctor_get(v_map_1883_, 0);
        v_indexes_1889_ = leanh::lean_ctor_get(v_map_1883_, 1);
        v___x_1890_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v_inst_1880_,
            v_inst_1881_,
            v_indexes_1889_,
            v_key_1884_,
        );
        v___x_1891_ = leanh::lean_unsigned_to_nat(0);
        v_entry_1892_ = lean_array_fget(v___x_1890_, v___x_1891_);
        leanh::lean_dec(v___x_1890_);
        v___x_1893_ = lean_array_fget_borrowed(v_entries_1888_, v_entry_1892_);
        leanh::lean_dec(v_entry_1892_);
        v_snd_1894_ = leanh::lean_ctor_get(v___x_1893_, 1);
        leanh::lean_inc(v_snd_1894_);
        return v_snd_1894_;
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_get_x21___boxed(
    mut v_00_u03b1_1895_: *mut leanh::LeanObject,
    mut v_00_u03b2_1896_: *mut leanh::LeanObject,
    mut v_inst_1897_: *mut leanh::LeanObject,
    mut v_inst_1898_: *mut leanh::LeanObject,
    mut v_inst_1899_: *mut leanh::LeanObject,
    mut v_map_1900_: *mut leanh::LeanObject,
    mut v_key_1901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Std_Internal_IndexMultiMap_get_x21(
        v_00_u03b1_1895_,
        v_00_u03b2_1896_,
        v_inst_1897_,
        v_inst_1898_,
        v_inst_1899_,
        v_map_1900_,
        v_key_1901_,
    );
    leanh::lean_dec_ref(v_map_1900_);
    leanh::lean_dec(v_inst_1899_);
    return v_res_1902_;
}
pub unsafe fn l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter___redArg(
    mut v_x_1903_: *mut leanh::LeanObject,
    mut v_h__1_1904_: *mut leanh::LeanObject,
    mut v_h__2_1905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1903_) == 0 {
        let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1904_);
        v___x_1906_ = leanh::lean_box(0);
        v___x_1907_ = leanh::lean_apply_1(v_h__2_1905_, v___x_1906_);
        return v___x_1907_;
    } else {
        let mut v_val_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1905_);
        v_val_1908_ = leanh::lean_ctor_get(v_x_1903_, 0);
        leanh::lean_inc(v_val_1908_);
        leanh::lean_dec_ref_known(v_x_1903_, 1);
        v___x_1909_ = leanh::lean_apply_1(v_h__1_1904_, v_val_1908_);
        return v___x_1909_;
    }
}
pub unsafe fn l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter(
    mut v_motive_1910_: *mut leanh::LeanObject,
    mut v_x_1911_: *mut leanh::LeanObject,
    mut v_h__1_1912_: *mut leanh::LeanObject,
    mut v_h__2_1913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1911_) == 0 {
        let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1912_);
        v___x_1914_ = leanh::lean_box(0);
        v___x_1915_ = leanh::lean_apply_1(v_h__2_1913_, v___x_1914_);
        return v___x_1915_;
    } else {
        let mut v_val_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1913_);
        v_val_1916_ = leanh::lean_ctor_get(v_x_1911_, 0);
        leanh::lean_inc(v_val_1916_);
        leanh::lean_dec_ref_known(v_x_1911_, 1);
        v___x_1917_ = leanh::lean_apply_1(v_h__1_1912_, v_val_1916_);
        return v___x_1917_;
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(
    mut v_i_1918_: *mut leanh::LeanObject,
    mut v_x_1919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1927_: u8 = 0;
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1919_) == 0 {
                    v___x_1920_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1921_ = lean_mk_empty_array_with_capacity(v___x_1920_);
                    v___x_1922_ = lean_array_push(v___x_1921_, v_i_1918_);
                    v___x_1923_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1923_, 0, v___x_1922_);
                    return v___x_1923_;
                } else {
                    v_val_1924_ = leanh::lean_ctor_get(v_x_1919_, 0);
                    v_isSharedCheck_1932_ = (!leanh::lean_is_exclusive(v_x_1919_)) as u8;
                    if v_isSharedCheck_1932_ == 0 {
                        v___x_1926_ = v_x_1919_;
                        v_isShared_1927_ = v_isSharedCheck_1932_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1924_);
                        leanh::lean_dec(v_x_1919_);
                        v___x_1926_ = leanh::lean_box(0);
                        v_isShared_1927_ = v_isSharedCheck_1932_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1928_ = lean_array_push(v_val_1924_, v_i_1918_);
                if v_isShared_1927_ == 0 {
                    leanh::lean_ctor_set(v___x_1926_, 0, v___x_1928_);
                    v___x_1930_ = v___x_1926_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1931_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
                    v___x_1930_ = v_reuseFailAlloc_1931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_insert___redArg(
    mut v_inst_1933_: *mut leanh::LeanObject,
    mut v_inst_1934_: *mut leanh::LeanObject,
    mut v_map_1935_: *mut leanh::LeanObject,
    mut v_key_1936_: *mut leanh::LeanObject,
    mut v_value_1937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1942_: u8 = 0;
    let mut v_i_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_entries_1938_ = leanh::lean_ctor_get(v_map_1935_, 0);
                v_indexes_1939_ = leanh::lean_ctor_get(v_map_1935_, 1);
                v_isSharedCheck_1951_ = (!leanh::lean_is_exclusive(v_map_1935_)) as u8;
                if v_isSharedCheck_1951_ == 0 {
                    v___x_1941_ = v_map_1935_;
                    v_isShared_1942_ = v_isSharedCheck_1951_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_1939_);
                    leanh::lean_inc(v_entries_1938_);
                    leanh::lean_dec(v_map_1935_);
                    v___x_1941_ = leanh::lean_box(0);
                    v_isShared_1942_ = v_isSharedCheck_1951_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_i_1943_ = lean_array_get_size(v_entries_1938_);
                v_f_1944_ = leanh::lean_alloc_closure(
                    l_Std_Internal_IndexMultiMap_insert___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v_f_1944_, 0, v_i_1943_);
                leanh::lean_inc(v_key_1936_);
                v___x_1945_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1945_, 0, v_key_1936_);
                leanh::lean_ctor_set(v___x_1945_, 1, v_value_1937_);
                v_entries_1946_ = lean_array_push(v_entries_1938_, v___x_1945_);
                v_indexes_1947_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v_inst_1933_,
                    v_inst_1934_,
                    v_indexes_1939_,
                    v_key_1936_,
                    v_f_1944_,
                );
                if v_isShared_1942_ == 0 {
                    leanh::lean_ctor_set(v___x_1941_, 1, v_indexes_1947_);
                    leanh::lean_ctor_set(v___x_1941_, 0, v_entries_1946_);
                    v___x_1949_ = v___x_1941_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1950_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_entries_1946_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_indexes_1947_);
                    v___x_1949_ = v_reuseFailAlloc_1950_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_insert(
    mut v_00_u03b1_1952_: *mut leanh::LeanObject,
    mut v_00_u03b2_1953_: *mut leanh::LeanObject,
    mut v_inst_1954_: *mut leanh::LeanObject,
    mut v_inst_1955_: *mut leanh::LeanObject,
    mut v_inst_1956_: *mut leanh::LeanObject,
    mut v_inst_1957_: *mut leanh::LeanObject,
    mut v_map_1958_: *mut leanh::LeanObject,
    mut v_key_1959_: *mut leanh::LeanObject,
    mut v_value_1960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1965_: u8 = 0;
    let mut v_i_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1974_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_entries_1961_ = leanh::lean_ctor_get(v_map_1958_, 0);
                v_indexes_1962_ = leanh::lean_ctor_get(v_map_1958_, 1);
                v_isSharedCheck_1974_ = (!leanh::lean_is_exclusive(v_map_1958_)) as u8;
                if v_isSharedCheck_1974_ == 0 {
                    v___x_1964_ = v_map_1958_;
                    v_isShared_1965_ = v_isSharedCheck_1974_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_1962_);
                    leanh::lean_inc(v_entries_1961_);
                    leanh::lean_dec(v_map_1958_);
                    v___x_1964_ = leanh::lean_box(0);
                    v_isShared_1965_ = v_isSharedCheck_1974_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_i_1966_ = lean_array_get_size(v_entries_1961_);
                v_f_1967_ = leanh::lean_alloc_closure(
                    l_Std_Internal_IndexMultiMap_insert___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v_f_1967_, 0, v_i_1966_);
                leanh::lean_inc(v_key_1959_);
                v___x_1968_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1968_, 0, v_key_1959_);
                leanh::lean_ctor_set(v___x_1968_, 1, v_value_1960_);
                v_entries_1969_ = lean_array_push(v_entries_1961_, v___x_1968_);
                v_indexes_1970_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v_inst_1954_,
                    v_inst_1955_,
                    v_indexes_1962_,
                    v_key_1959_,
                    v_f_1967_,
                );
                if v_isShared_1965_ == 0 {
                    leanh::lean_ctor_set(v___x_1964_, 1, v_indexes_1970_);
                    leanh::lean_ctor_set(v___x_1964_, 0, v_entries_1969_);
                    v___x_1972_ = v___x_1964_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1973_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_entries_1969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_indexes_1970_);
                    v___x_1972_ = v_reuseFailAlloc_1973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1972_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1(
    mut v_key_1975_: *mut leanh::LeanObject,
    mut v_inst_1976_: *mut leanh::LeanObject,
    mut v_inst_1977_: *mut leanh::LeanObject,
    mut v_x1_1978_: *mut leanh::LeanObject,
    mut v_x2_1979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1984_: u8 = 0;
    let mut v_i_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_entries_1980_ = leanh::lean_ctor_get(v_x1_1978_, 0);
                v_indexes_1981_ = leanh::lean_ctor_get(v_x1_1978_, 1);
                v_isSharedCheck_1993_ = (!leanh::lean_is_exclusive(v_x1_1978_)) as u8;
                if v_isSharedCheck_1993_ == 0 {
                    v___x_1983_ = v_x1_1978_;
                    v_isShared_1984_ = v_isSharedCheck_1993_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_1981_);
                    leanh::lean_inc(v_entries_1980_);
                    leanh::lean_dec(v_x1_1978_);
                    v___x_1983_ = leanh::lean_box(0);
                    v_isShared_1984_ = v_isSharedCheck_1993_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_i_1985_ = lean_array_get_size(v_entries_1980_);
                v_f_1986_ = leanh::lean_alloc_closure(
                    l_Std_Internal_IndexMultiMap_insert___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v_f_1986_, 0, v_i_1985_);
                leanh::lean_inc(v_key_1975_);
                v___x_1987_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1987_, 0, v_key_1975_);
                leanh::lean_ctor_set(v___x_1987_, 1, v_x2_1979_);
                v_entries_1988_ = lean_array_push(v_entries_1980_, v___x_1987_);
                v_indexes_1989_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v_inst_1976_,
                    v_inst_1977_,
                    v_indexes_1981_,
                    v_key_1975_,
                    v_f_1986_,
                );
                if v_isShared_1984_ == 0 {
                    leanh::lean_ctor_set(v___x_1983_, 1, v_indexes_1989_);
                    leanh::lean_ctor_set(v___x_1983_, 0, v_entries_1988_);
                    v___x_1991_ = v___x_1983_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1992_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_entries_1988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_indexes_1989_);
                    v___x_1991_ = v_reuseFailAlloc_1992_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1991_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_insertMany___redArg(
    mut v_inst_1994_: *mut leanh::LeanObject,
    mut v_inst_1995_: *mut leanh::LeanObject,
    mut v_map_1996_: *mut leanh::LeanObject,
    mut v_key_1997_: *mut leanh::LeanObject,
    mut v_values_1998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: u8 = 0;
    v___x_1999_ = leanh::lean_unsigned_to_nat(0);
    v___x_2000_ = lean_array_get_size(v_values_1998_);
    v___x_2001_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
    v___x_2002_ = lean_nat_dec_lt(v___x_1999_, v___x_2000_);
    if v___x_2002_ == 0 {
        leanh::lean_dec_ref(v_values_1998_);
        leanh::lean_dec(v_key_1997_);
        leanh::lean_dec_ref(v_inst_1995_);
        leanh::lean_dec_ref(v_inst_1994_);
        return v_map_1996_;
    } else {
        let mut v___f_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2004_: u8 = 0;
        v___f_2003_ = leanh::lean_alloc_closure(
            l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            3,
        );
        leanh::lean_closure_set(v___f_2003_, 0, v_key_1997_);
        leanh::lean_closure_set(v___f_2003_, 1, v_inst_1994_);
        leanh::lean_closure_set(v___f_2003_, 2, v_inst_1995_);
        v___x_2004_ = lean_nat_dec_le(v___x_2000_, v___x_2000_);
        if v___x_2004_ == 0 {
            if v___x_2002_ == 0 {
                leanh::lean_dec_ref(v___f_2003_);
                leanh::lean_dec_ref(v_values_1998_);
                return v_map_1996_;
            } else {
                let mut v___x_2005_: usize = 0;
                let mut v___x_2006_: usize = 0;
                let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2005_ = 0usize;
                v___x_2006_ = lean_usize_of_nat(v___x_2000_);
                v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2001_,
                    v___f_2003_,
                    v_values_1998_,
                    v___x_2005_,
                    v___x_2006_,
                    v_map_1996_,
                );
                return v___x_2007_;
            }
        } else {
            let mut v___x_2008_: usize = 0;
            let mut v___x_2009_: usize = 0;
            let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2008_ = 0usize;
            v___x_2009_ = lean_usize_of_nat(v___x_2000_);
            v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_2001_,
                v___f_2003_,
                v_values_1998_,
                v___x_2008_,
                v___x_2009_,
                v_map_1996_,
            );
            return v___x_2010_;
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_insertMany(
    mut v_00_u03b1_2011_: *mut leanh::LeanObject,
    mut v_00_u03b2_2012_: *mut leanh::LeanObject,
    mut v_inst_2013_: *mut leanh::LeanObject,
    mut v_inst_2014_: *mut leanh::LeanObject,
    mut v_inst_2015_: *mut leanh::LeanObject,
    mut v_inst_2016_: *mut leanh::LeanObject,
    mut v_map_2017_: *mut leanh::LeanObject,
    mut v_key_2018_: *mut leanh::LeanObject,
    mut v_values_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    v___x_2020_ = leanh::lean_unsigned_to_nat(0);
    v___x_2021_ = lean_array_get_size(v_values_2019_);
    v___x_2022_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
    v___x_2023_ = lean_nat_dec_lt(v___x_2020_, v___x_2021_);
    if v___x_2023_ == 0 {
        leanh::lean_dec_ref(v_values_2019_);
        leanh::lean_dec(v_key_2018_);
        leanh::lean_dec_ref(v_inst_2014_);
        leanh::lean_dec_ref(v_inst_2013_);
        return v_map_2017_;
    } else {
        let mut v___f_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2025_: u8 = 0;
        v___f_2024_ = leanh::lean_alloc_closure(
            l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            3,
        );
        leanh::lean_closure_set(v___f_2024_, 0, v_key_2018_);
        leanh::lean_closure_set(v___f_2024_, 1, v_inst_2013_);
        leanh::lean_closure_set(v___f_2024_, 2, v_inst_2014_);
        v___x_2025_ = lean_nat_dec_le(v___x_2021_, v___x_2021_);
        if v___x_2025_ == 0 {
            if v___x_2023_ == 0 {
                leanh::lean_dec_ref(v___f_2024_);
                leanh::lean_dec_ref(v_values_2019_);
                return v_map_2017_;
            } else {
                let mut v___x_2026_: usize = 0;
                let mut v___x_2027_: usize = 0;
                let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2026_ = 0usize;
                v___x_2027_ = lean_usize_of_nat(v___x_2021_);
                v___x_2028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2022_,
                    v___f_2024_,
                    v_values_2019_,
                    v___x_2026_,
                    v___x_2027_,
                    v_map_2017_,
                );
                return v___x_2028_;
            }
        } else {
            let mut v___x_2029_: usize = 0;
            let mut v___x_2030_: usize = 0;
            let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2029_ = 0usize;
            v___x_2030_ = lean_usize_of_nat(v___x_2021_);
            v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_2022_,
                v___f_2024_,
                v_values_2019_,
                v___x_2029_,
                v___x_2030_,
                v_map_2017_,
            );
            return v___x_2031_;
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_empty(
    mut v_00_u03b1_2032_: *mut leanh::LeanObject,
    mut v_00_u03b2_2033_: *mut leanh::LeanObject,
    mut v_inst_2034_: *mut leanh::LeanObject,
    mut v_inst_2035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2036_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_instInhabitedIndexMultiMap___closed__3),
        core::ptr::addr_of_mut!(l_Std_Internal_instInhabitedIndexMultiMap___closed__3_once),
        _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__3,
    );
    return v___x_2036_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_empty___boxed(
    mut v_00_u03b1_2037_: *mut leanh::LeanObject,
    mut v_00_u03b2_2038_: *mut leanh::LeanObject,
    mut v_inst_2039_: *mut leanh::LeanObject,
    mut v_inst_2040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2041_ = l_Std_Internal_IndexMultiMap_empty(
        v_00_u03b1_2037_,
        v_00_u03b2_2038_,
        v_inst_2039_,
        v_inst_2040_,
    );
    leanh::lean_dec_ref(v_inst_2040_);
    leanh::lean_dec_ref(v_inst_2039_);
    return v_res_2041_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1(
    mut v_inst_2042_: *mut leanh::LeanObject,
    mut v_inst_2043_: *mut leanh::LeanObject,
    mut v_acc_2044_: *mut leanh::LeanObject,
    mut v_x_2045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v_i_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2059_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2046_ = leanh::lean_ctor_get(v_x_2045_, 0);
                leanh::lean_inc(v_fst_2046_);
                v_entries_2047_ = leanh::lean_ctor_get(v_acc_2044_, 0);
                v_indexes_2048_ = leanh::lean_ctor_get(v_acc_2044_, 1);
                v_isSharedCheck_2059_ = (!leanh::lean_is_exclusive(v_acc_2044_)) as u8;
                if v_isSharedCheck_2059_ == 0 {
                    v___x_2050_ = v_acc_2044_;
                    v_isShared_2051_ = v_isSharedCheck_2059_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_2048_);
                    leanh::lean_inc(v_entries_2047_);
                    leanh::lean_dec(v_acc_2044_);
                    v___x_2050_ = leanh::lean_box(0);
                    v_isShared_2051_ = v_isSharedCheck_2059_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_i_2052_ = lean_array_get_size(v_entries_2047_);
                v_f_2053_ = leanh::lean_alloc_closure(
                    l_Std_Internal_IndexMultiMap_insert___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v_f_2053_, 0, v_i_2052_);
                v_entries_2054_ = lean_array_push(v_entries_2047_, v_x_2045_);
                v_indexes_2055_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v_inst_2042_,
                    v_inst_2043_,
                    v_indexes_2048_,
                    v_fst_2046_,
                    v_f_2053_,
                );
                if v_isShared_2051_ == 0 {
                    leanh::lean_ctor_set(v___x_2050_, 1, v_indexes_2055_);
                    leanh::lean_ctor_set(v___x_2050_, 0, v_entries_2054_);
                    v___x_2057_ = v___x_2050_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2058_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_entries_2054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_indexes_2055_);
                    v___x_2057_ = v_reuseFailAlloc_2058_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_ofList___redArg(
    mut v_inst_2060_: *mut leanh::LeanObject,
    mut v_inst_2061_: *mut leanh::LeanObject,
    mut v_pairs_2062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_2061_);
    leanh::lean_inc_ref(v_inst_2060_);
    v___f_2063_ = leanh::lean_alloc_closure(
        l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2063_, 0, v_inst_2060_);
    leanh::lean_closure_set(v___f_2063_, 1, v_inst_2061_);
    v___x_2064_ = l_Std_Internal_IndexMultiMap_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_2060_,
        v_inst_2061_,
    );
    leanh::lean_dec_ref(v_inst_2061_);
    leanh::lean_dec_ref(v_inst_2060_);
    v___x_2065_ = l_List_foldl___redArg(v___f_2063_, v___x_2064_, v_pairs_2062_);
    return v___x_2065_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_ofList(
    mut v_00_u03b1_2066_: *mut leanh::LeanObject,
    mut v_00_u03b2_2067_: *mut leanh::LeanObject,
    mut v_inst_2068_: *mut leanh::LeanObject,
    mut v_inst_2069_: *mut leanh::LeanObject,
    mut v_inst_2070_: *mut leanh::LeanObject,
    mut v_inst_2071_: *mut leanh::LeanObject,
    mut v_pairs_2072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2073_ =
        l_Std_Internal_IndexMultiMap_ofList___redArg(v_inst_2068_, v_inst_2069_, v_pairs_2072_);
    return v___x_2073_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_contains___redArg(
    mut v_inst_2074_: *mut leanh::LeanObject,
    mut v_inst_2075_: *mut leanh::LeanObject,
    mut v_map_2076_: *mut leanh::LeanObject,
    mut v_key_2077_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_indexes_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: u8 = 0;
    v_indexes_2078_ = leanh::lean_ctor_get(v_map_2076_, 1);
    v___x_2079_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_2074_,
        v_inst_2075_,
        v_indexes_2078_,
        v_key_2077_,
    );
    return v___x_2079_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_contains___redArg___boxed(
    mut v_inst_2080_: *mut leanh::LeanObject,
    mut v_inst_2081_: *mut leanh::LeanObject,
    mut v_map_2082_: *mut leanh::LeanObject,
    mut v_key_2083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2084_: u8 = 0;
    let mut v_r_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2084_ = l_Std_Internal_IndexMultiMap_contains___redArg(
        v_inst_2080_,
        v_inst_2081_,
        v_map_2082_,
        v_key_2083_,
    );
    leanh::lean_dec_ref(v_map_2082_);
    v_r_2085_ = leanh::lean_box((v_res_2084_) as usize);
    return v_r_2085_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_contains(
    mut v_00_u03b1_2086_: *mut leanh::LeanObject,
    mut v_00_u03b2_2087_: *mut leanh::LeanObject,
    mut v_inst_2088_: *mut leanh::LeanObject,
    mut v_inst_2089_: *mut leanh::LeanObject,
    mut v_map_2090_: *mut leanh::LeanObject,
    mut v_key_2091_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_indexes_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: u8 = 0;
    v_indexes_2092_ = leanh::lean_ctor_get(v_map_2090_, 1);
    v___x_2093_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_2088_,
        v_inst_2089_,
        v_indexes_2092_,
        v_key_2091_,
    );
    return v___x_2093_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_contains___boxed(
    mut v_00_u03b1_2094_: *mut leanh::LeanObject,
    mut v_00_u03b2_2095_: *mut leanh::LeanObject,
    mut v_inst_2096_: *mut leanh::LeanObject,
    mut v_inst_2097_: *mut leanh::LeanObject,
    mut v_map_2098_: *mut leanh::LeanObject,
    mut v_key_2099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2100_: u8 = 0;
    let mut v_r_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2100_ = l_Std_Internal_IndexMultiMap_contains(
        v_00_u03b1_2094_,
        v_00_u03b2_2095_,
        v_inst_2096_,
        v_inst_2097_,
        v_map_2098_,
        v_key_2099_,
    );
    leanh::lean_dec_ref(v_map_2098_);
    v_r_2101_ = leanh::lean_box((v_res_2100_) as usize);
    return v_r_2101_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_update___redArg___lam__1(
    mut v_inst_2102_: *mut leanh::LeanObject,
    mut v_inst_2103_: *mut leanh::LeanObject,
    mut v_key_2104_: *mut leanh::LeanObject,
    mut v_f_2105_: *mut leanh::LeanObject,
    mut v_x1_2106_: *mut leanh::LeanObject,
    mut v_x2_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___y_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2119_: u8 = 0;
    let mut v_i_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2130_: u8 = 0;
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2134_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2108_ = leanh::lean_ctor_get(v_x2_2107_, 0);
                v_snd_2109_ = leanh::lean_ctor_get(v_x2_2107_, 1);
                v_isSharedCheck_2134_ = (!leanh::lean_is_exclusive(v_x2_2107_)) as u8;
                if v_isSharedCheck_2134_ == 0 {
                    v___x_2111_ = v_x2_2107_;
                    v_isShared_2112_ = v_isSharedCheck_2134_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2109_);
                    leanh::lean_inc(v_fst_2108_);
                    leanh::lean_dec(v_x2_2107_);
                    v___x_2111_ = leanh::lean_box(0);
                    v_isShared_2112_ = v_isSharedCheck_2134_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_2102_);
                leanh::lean_inc(v_fst_2108_);
                v___x_2131_ = leanh::lean_apply_2(v_inst_2102_, v_fst_2108_, v_key_2104_);
                v___x_2132_ = (leanh::lean_unbox(v___x_2131_) as u8);
                if v___x_2132_ == 0 {
                    leanh::lean_dec(v_f_2105_);
                    v___y_2114_ = v_snd_2109_;
                    state = 2;
                    continue;
                } else {
                    v___x_2133_ = leanh::lean_apply_1(v_f_2105_, v_snd_2109_);
                    v___y_2114_ = v___x_2133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_entries_2115_ = leanh::lean_ctor_get(v_x1_2106_, 0);
                v_indexes_2116_ = leanh::lean_ctor_get(v_x1_2106_, 1);
                v_isSharedCheck_2130_ = (!leanh::lean_is_exclusive(v_x1_2106_)) as u8;
                if v_isSharedCheck_2130_ == 0 {
                    v___x_2118_ = v_x1_2106_;
                    v_isShared_2119_ = v_isSharedCheck_2130_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_2116_);
                    leanh::lean_inc(v_entries_2115_);
                    leanh::lean_dec(v_x1_2106_);
                    v___x_2118_ = leanh::lean_box(0);
                    v_isShared_2119_ = v_isSharedCheck_2130_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_i_2120_ = lean_array_get_size(v_entries_2115_);
                v_f_2121_ = leanh::lean_alloc_closure(
                    l_Std_Internal_IndexMultiMap_insert___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v_f_2121_, 0, v_i_2120_);
                leanh::lean_inc(v_fst_2108_);
                if v_isShared_2112_ == 0 {
                    leanh::lean_ctor_set(v___x_2111_, 1, v___y_2114_);
                    v___x_2123_ = v___x_2111_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2129_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_fst_2108_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 1, v___y_2114_);
                    v___x_2123_ = v_reuseFailAlloc_2129_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_entries_2124_ = lean_array_push(v_entries_2115_, v___x_2123_);
                v_indexes_2125_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v_inst_2102_,
                    v_inst_2103_,
                    v_indexes_2116_,
                    v_fst_2108_,
                    v_f_2121_,
                );
                if v_isShared_2119_ == 0 {
                    leanh::lean_ctor_set(v___x_2118_, 1, v_indexes_2125_);
                    leanh::lean_ctor_set(v___x_2118_, 0, v_entries_2124_);
                    v___x_2127_ = v___x_2118_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2128_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_entries_2124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_indexes_2125_);
                    v___x_2127_ = v_reuseFailAlloc_2128_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2127_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_update___redArg(
    mut v_inst_2135_: *mut leanh::LeanObject,
    mut v_inst_2136_: *mut leanh::LeanObject,
    mut v_map_2137_: *mut leanh::LeanObject,
    mut v_key_2138_: *mut leanh::LeanObject,
    mut v_f_2139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2140_: u8 = 0;
    leanh::lean_inc(v_key_2138_);
    leanh::lean_inc_ref(v_inst_2136_);
    leanh::lean_inc_ref(v_inst_2135_);
    v___x_2140_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_2135_,
        v_inst_2136_,
        v_key_2138_,
        v_map_2137_,
    );
    if v___x_2140_ == 0 {
        leanh::lean_dec(v_f_2139_);
        leanh::lean_dec(v_key_2138_);
        leanh::lean_dec_ref(v_inst_2136_);
        leanh::lean_dec_ref(v_inst_2135_);
        return v_map_2137_;
    } else {
        let mut v_entries_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2146_: u8 = 0;
        v_entries_2141_ = leanh::lean_ctor_get(v_map_2137_, 0);
        leanh::lean_inc_ref(v_entries_2141_);
        leanh::lean_dec_ref(v_map_2137_);
        v___x_2142_ = l_Std_Internal_IndexMultiMap_empty(
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_2135_,
            v_inst_2136_,
        );
        v___x_2143_ = leanh::lean_unsigned_to_nat(0);
        v___x_2144_ = lean_array_get_size(v_entries_2141_);
        v___x_2145_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
        v___x_2146_ = lean_nat_dec_lt(v___x_2143_, v___x_2144_);
        if v___x_2146_ == 0 {
            leanh::lean_dec_ref(v_entries_2141_);
            leanh::lean_dec(v_f_2139_);
            leanh::lean_dec(v_key_2138_);
            leanh::lean_dec_ref(v_inst_2136_);
            leanh::lean_dec_ref(v_inst_2135_);
            return v___x_2142_;
        } else {
            let mut v___f_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2148_: u8 = 0;
            v___f_2147_ = leanh::lean_alloc_closure(
                l_Std_Internal_IndexMultiMap_update___redArg___lam__1 as *mut core::ffi::c_void,
                6,
                4,
            );
            leanh::lean_closure_set(v___f_2147_, 0, v_inst_2135_);
            leanh::lean_closure_set(v___f_2147_, 1, v_inst_2136_);
            leanh::lean_closure_set(v___f_2147_, 2, v_key_2138_);
            leanh::lean_closure_set(v___f_2147_, 3, v_f_2139_);
            v___x_2148_ = lean_nat_dec_le(v___x_2144_, v___x_2144_);
            if v___x_2148_ == 0 {
                if v___x_2146_ == 0 {
                    leanh::lean_dec_ref(v___f_2147_);
                    leanh::lean_dec_ref(v_entries_2141_);
                    return v___x_2142_;
                } else {
                    let mut v___x_2149_: usize = 0;
                    let mut v___x_2150_: usize = 0;
                    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_2149_ = 0usize;
                    v___x_2150_ = lean_usize_of_nat(v___x_2144_);
                    v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2145_,
                        v___f_2147_,
                        v_entries_2141_,
                        v___x_2149_,
                        v___x_2150_,
                        v___x_2142_,
                    );
                    return v___x_2151_;
                }
            } else {
                let mut v___x_2152_: usize = 0;
                let mut v___x_2153_: usize = 0;
                let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2152_ = 0usize;
                v___x_2153_ = lean_usize_of_nat(v___x_2144_);
                v___x_2154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2145_,
                    v___f_2147_,
                    v_entries_2141_,
                    v___x_2152_,
                    v___x_2153_,
                    v___x_2142_,
                );
                return v___x_2154_;
            }
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_update(
    mut v_00_u03b1_2155_: *mut leanh::LeanObject,
    mut v_00_u03b2_2156_: *mut leanh::LeanObject,
    mut v_inst_2157_: *mut leanh::LeanObject,
    mut v_inst_2158_: *mut leanh::LeanObject,
    mut v_inst_2159_: *mut leanh::LeanObject,
    mut v_inst_2160_: *mut leanh::LeanObject,
    mut v_map_2161_: *mut leanh::LeanObject,
    mut v_key_2162_: *mut leanh::LeanObject,
    mut v_f_2163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2164_: u8 = 0;
    leanh::lean_inc(v_key_2162_);
    leanh::lean_inc_ref(v_inst_2158_);
    leanh::lean_inc_ref(v_inst_2157_);
    v___x_2164_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v_inst_2157_,
        v_inst_2158_,
        v_key_2162_,
        v_map_2161_,
    );
    if v___x_2164_ == 0 {
        leanh::lean_dec(v_f_2163_);
        leanh::lean_dec(v_key_2162_);
        leanh::lean_dec_ref(v_inst_2158_);
        leanh::lean_dec_ref(v_inst_2157_);
        return v_map_2161_;
    } else {
        let mut v_entries_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2170_: u8 = 0;
        v_entries_2165_ = leanh::lean_ctor_get(v_map_2161_, 0);
        leanh::lean_inc_ref(v_entries_2165_);
        leanh::lean_dec_ref(v_map_2161_);
        v___x_2166_ = l_Std_Internal_IndexMultiMap_empty(
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_2157_,
            v_inst_2158_,
        );
        v___x_2167_ = leanh::lean_unsigned_to_nat(0);
        v___x_2168_ = lean_array_get_size(v_entries_2165_);
        v___x_2169_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
        v___x_2170_ = lean_nat_dec_lt(v___x_2167_, v___x_2168_);
        if v___x_2170_ == 0 {
            leanh::lean_dec_ref(v_entries_2165_);
            leanh::lean_dec(v_f_2163_);
            leanh::lean_dec(v_key_2162_);
            leanh::lean_dec_ref(v_inst_2158_);
            leanh::lean_dec_ref(v_inst_2157_);
            return v___x_2166_;
        } else {
            let mut v___f_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2172_: u8 = 0;
            v___f_2171_ = leanh::lean_alloc_closure(
                l_Std_Internal_IndexMultiMap_update___redArg___lam__1 as *mut core::ffi::c_void,
                6,
                4,
            );
            leanh::lean_closure_set(v___f_2171_, 0, v_inst_2157_);
            leanh::lean_closure_set(v___f_2171_, 1, v_inst_2158_);
            leanh::lean_closure_set(v___f_2171_, 2, v_key_2162_);
            leanh::lean_closure_set(v___f_2171_, 3, v_f_2163_);
            v___x_2172_ = lean_nat_dec_le(v___x_2168_, v___x_2168_);
            if v___x_2172_ == 0 {
                if v___x_2170_ == 0 {
                    leanh::lean_dec_ref(v___f_2171_);
                    leanh::lean_dec_ref(v_entries_2165_);
                    return v___x_2166_;
                } else {
                    let mut v___x_2173_: usize = 0;
                    let mut v___x_2174_: usize = 0;
                    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_2173_ = 0usize;
                    v___x_2174_ = lean_usize_of_nat(v___x_2168_);
                    v___x_2175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2169_,
                        v___f_2171_,
                        v_entries_2165_,
                        v___x_2173_,
                        v___x_2174_,
                        v___x_2166_,
                    );
                    return v___x_2175_;
                }
            } else {
                let mut v___x_2176_: usize = 0;
                let mut v___x_2177_: usize = 0;
                let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2176_ = 0usize;
                v___x_2177_ = lean_usize_of_nat(v___x_2168_);
                v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2169_,
                    v___f_2171_,
                    v_entries_2165_,
                    v___x_2176_,
                    v___x_2177_,
                    v___x_2166_,
                );
                return v___x_2178_;
            }
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_replaceLast___redArg(
    mut v_inst_2179_: *mut leanh::LeanObject,
    mut v_inst_2180_: *mut leanh::LeanObject,
    mut v_map_2181_: *mut leanh::LeanObject,
    mut v_key_2182_: *mut leanh::LeanObject,
    mut v_value_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2184_: u8 = 0;
    let mut v_entries_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v_idxs_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastIdx_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2200_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_key_2182_);
                leanh::lean_inc_ref(v_inst_2180_);
                leanh::lean_inc_ref(v_inst_2179_);
                v___x_2184_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
                    v_inst_2179_,
                    v_inst_2180_,
                    v_key_2182_,
                    v_map_2181_,
                );
                if v___x_2184_ == 0 {
                    leanh::lean_dec(v_value_2183_);
                    leanh::lean_dec(v_key_2182_);
                    leanh::lean_dec_ref(v_inst_2180_);
                    leanh::lean_dec_ref(v_inst_2179_);
                    return v_map_2181_;
                } else {
                    v_entries_2185_ = leanh::lean_ctor_get(v_map_2181_, 0);
                    v_indexes_2186_ = leanh::lean_ctor_get(v_map_2181_, 1);
                    v_isSharedCheck_2200_ = (!leanh::lean_is_exclusive(v_map_2181_)) as u8;
                    if v_isSharedCheck_2200_ == 0 {
                        v___x_2188_ = v_map_2181_;
                        v_isShared_2189_ = v_isSharedCheck_2200_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_indexes_2186_);
                        leanh::lean_inc(v_entries_2185_);
                        leanh::lean_dec(v_map_2181_);
                        v___x_2188_ = leanh::lean_box(0);
                        v_isShared_2189_ = v_isSharedCheck_2200_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_key_2182_);
                v_idxs_2190_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
                    v_inst_2179_,
                    v_inst_2180_,
                    v_indexes_2186_,
                    v_key_2182_,
                );
                v___x_2191_ = lean_array_get_size(v_idxs_2190_);
                v___x_2192_ = leanh::lean_unsigned_to_nat(1);
                v___x_2193_ = lean_nat_sub(v___x_2191_, v___x_2192_);
                v_lastIdx_2194_ = lean_array_fget(v_idxs_2190_, v___x_2193_);
                leanh::lean_dec(v___x_2193_);
                leanh::lean_dec(v_idxs_2190_);
                v___x_2195_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2195_, 0, v_key_2182_);
                leanh::lean_ctor_set(v___x_2195_, 1, v_value_2183_);
                v_entries_2196_ = lean_array_fset(v_entries_2185_, v_lastIdx_2194_, v___x_2195_);
                leanh::lean_dec(v_lastIdx_2194_);
                if v_isShared_2189_ == 0 {
                    leanh::lean_ctor_set(v___x_2188_, 0, v_entries_2196_);
                    v___x_2198_ = v___x_2188_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2199_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_entries_2196_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_indexes_2186_);
                    v___x_2198_ = v_reuseFailAlloc_2199_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2198_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_replaceLast(
    mut v_00_u03b1_2201_: *mut leanh::LeanObject,
    mut v_00_u03b2_2202_: *mut leanh::LeanObject,
    mut v_inst_2203_: *mut leanh::LeanObject,
    mut v_inst_2204_: *mut leanh::LeanObject,
    mut v_map_2205_: *mut leanh::LeanObject,
    mut v_key_2206_: *mut leanh::LeanObject,
    mut v_value_2207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2208_: u8 = 0;
    let mut v_entries_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v_idxs_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastIdx_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2224_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_key_2206_);
                leanh::lean_inc_ref(v_inst_2204_);
                leanh::lean_inc_ref(v_inst_2203_);
                v___x_2208_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
                    v_inst_2203_,
                    v_inst_2204_,
                    v_key_2206_,
                    v_map_2205_,
                );
                if v___x_2208_ == 0 {
                    leanh::lean_dec(v_value_2207_);
                    leanh::lean_dec(v_key_2206_);
                    leanh::lean_dec_ref(v_inst_2204_);
                    leanh::lean_dec_ref(v_inst_2203_);
                    return v_map_2205_;
                } else {
                    v_entries_2209_ = leanh::lean_ctor_get(v_map_2205_, 0);
                    v_indexes_2210_ = leanh::lean_ctor_get(v_map_2205_, 1);
                    v_isSharedCheck_2224_ = (!leanh::lean_is_exclusive(v_map_2205_)) as u8;
                    if v_isSharedCheck_2224_ == 0 {
                        v___x_2212_ = v_map_2205_;
                        v_isShared_2213_ = v_isSharedCheck_2224_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_indexes_2210_);
                        leanh::lean_inc(v_entries_2209_);
                        leanh::lean_dec(v_map_2205_);
                        v___x_2212_ = leanh::lean_box(0);
                        v_isShared_2213_ = v_isSharedCheck_2224_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_key_2206_);
                v_idxs_2214_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
                    v_inst_2203_,
                    v_inst_2204_,
                    v_indexes_2210_,
                    v_key_2206_,
                );
                v___x_2215_ = lean_array_get_size(v_idxs_2214_);
                v___x_2216_ = leanh::lean_unsigned_to_nat(1);
                v___x_2217_ = lean_nat_sub(v___x_2215_, v___x_2216_);
                v_lastIdx_2218_ = lean_array_fget(v_idxs_2214_, v___x_2217_);
                leanh::lean_dec(v___x_2217_);
                leanh::lean_dec(v_idxs_2214_);
                v___x_2219_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2219_, 0, v_key_2206_);
                leanh::lean_ctor_set(v___x_2219_, 1, v_value_2207_);
                v_entries_2220_ = lean_array_fset(v_entries_2209_, v_lastIdx_2218_, v___x_2219_);
                leanh::lean_dec(v_lastIdx_2218_);
                if v_isShared_2213_ == 0 {
                    leanh::lean_ctor_set(v___x_2212_, 0, v_entries_2220_);
                    v___x_2222_ = v___x_2212_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2223_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_entries_2220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_indexes_2210_);
                    v___x_2222_ = v_reuseFailAlloc_2223_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2222_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_erase___redArg___lam__1(
    mut v_inst_2225_: *mut leanh::LeanObject,
    mut v_inst_2226_: *mut leanh::LeanObject,
    mut v_x1_2227_: *mut leanh::LeanObject,
    mut v_x2_2228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2234_: u8 = 0;
    let mut v_i_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2229_ = leanh::lean_ctor_get(v_x2_2228_, 0);
                leanh::lean_inc(v_fst_2229_);
                v_entries_2230_ = leanh::lean_ctor_get(v_x1_2227_, 0);
                v_indexes_2231_ = leanh::lean_ctor_get(v_x1_2227_, 1);
                v_isSharedCheck_2242_ = (!leanh::lean_is_exclusive(v_x1_2227_)) as u8;
                if v_isSharedCheck_2242_ == 0 {
                    v___x_2233_ = v_x1_2227_;
                    v_isShared_2234_ = v_isSharedCheck_2242_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_2231_);
                    leanh::lean_inc(v_entries_2230_);
                    leanh::lean_dec(v_x1_2227_);
                    v___x_2233_ = leanh::lean_box(0);
                    v_isShared_2234_ = v_isSharedCheck_2242_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_i_2235_ = lean_array_get_size(v_entries_2230_);
                v_f_2236_ = leanh::lean_alloc_closure(
                    l_Std_Internal_IndexMultiMap_insert___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v_f_2236_, 0, v_i_2235_);
                v_entries_2237_ = lean_array_push(v_entries_2230_, v_x2_2228_);
                v_indexes_2238_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v_inst_2225_,
                    v_inst_2226_,
                    v_indexes_2231_,
                    v_fst_2229_,
                    v_f_2236_,
                );
                if v_isShared_2234_ == 0 {
                    leanh::lean_ctor_set(v___x_2233_, 1, v_indexes_2238_);
                    leanh::lean_ctor_set(v___x_2233_, 0, v_entries_2237_);
                    v___x_2240_ = v___x_2233_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_entries_2237_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_indexes_2238_);
                    v___x_2240_ = v_reuseFailAlloc_2241_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2240_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_erase___redArg___lam__0(
    mut v_inst_2243_: *mut leanh::LeanObject,
    mut v_key_2244_: *mut leanh::LeanObject,
    mut v_x1_2245_: *mut leanh::LeanObject,
    mut v_x2_2246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: u8 = 0;
    v_fst_2247_ = leanh::lean_ctor_get(v_x2_2246_, 0);
    leanh::lean_inc(v_fst_2247_);
    v___x_2248_ = leanh::lean_apply_2(v_inst_2243_, v_fst_2247_, v_key_2244_);
    v___x_2249_ = (leanh::lean_unbox(v___x_2248_) as u8);
    if v___x_2249_ == 0 {
        let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2250_ = lean_array_push(v_x1_2245_, v_x2_2246_);
        return v___x_2250_;
    } else {
        leanh::lean_dec_ref(v_x2_2246_);
        return v_x1_2245_;
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_erase___redArg(
    mut v_inst_2251_: *mut leanh::LeanObject,
    mut v_inst_2252_: *mut leanh::LeanObject,
    mut v_map_2253_: *mut leanh::LeanObject,
    mut v_key_2254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2255_: u8 = 0;
    let mut v_entries_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: u8 = 0;
    let mut v___x_2265_: u8 = 0;
    let mut v___x_2266_: usize = 0;
    let mut v___x_2267_: usize = 0;
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: usize = 0;
    let mut v___x_2270_: usize = 0;
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: u8 = 0;
    let mut v___f_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: u8 = 0;
    let mut v___x_2278_: usize = 0;
    let mut v___x_2279_: usize = 0;
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: usize = 0;
    let mut v___x_2282_: usize = 0;
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_key_2254_);
                leanh::lean_inc_ref(v_inst_2252_);
                leanh::lean_inc_ref(v_inst_2251_);
                v___x_2255_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
                    v_inst_2251_,
                    v_inst_2252_,
                    v_key_2254_,
                    v_map_2253_,
                );
                if v___x_2255_ == 0 {
                    leanh::lean_dec(v_key_2254_);
                    leanh::lean_dec_ref(v_inst_2252_);
                    leanh::lean_dec_ref(v_inst_2251_);
                    return v_map_2253_;
                } else {
                    v_entries_2256_ = leanh::lean_ctor_get(v_map_2253_, 0);
                    leanh::lean_inc_ref(v_entries_2256_);
                    leanh::lean_dec_ref(v_map_2253_);
                    leanh::lean_inc_ref(v_inst_2252_);
                    leanh::lean_inc_ref(v_inst_2251_);
                    v___f_2257_ = leanh::lean_alloc_closure(
                        l_Std_Internal_IndexMultiMap_erase___redArg___lam__1
                            as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_2257_, 0, v_inst_2251_);
                    leanh::lean_closure_set(v___f_2257_, 1, v_inst_2252_);
                    v___x_2258_ = l_Std_Internal_IndexMultiMap_empty(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_2251_,
                        v_inst_2252_,
                    );
                    leanh::lean_dec_ref(v_inst_2252_);
                    v___x_2259_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2272_ = lean_array_get_size(v_entries_2256_);
                    v___x_2273_ = l_Std_Internal_instInhabitedIndexMultiMap___closed__0;
                    v___x_2274_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
                    v___x_2275_ = lean_nat_dec_lt(v___x_2259_, v___x_2272_);
                    if v___x_2275_ == 0 {
                        leanh::lean_dec_ref(v_entries_2256_);
                        leanh::lean_dec(v_key_2254_);
                        leanh::lean_dec_ref(v_inst_2251_);
                        v___y_2261_ = v___x_2273_;
                        state = 1;
                        continue;
                    } else {
                        v___f_2276_ = leanh::lean_alloc_closure(
                            l_Std_Internal_IndexMultiMap_erase___redArg___lam__0
                                as *mut core::ffi::c_void,
                            4,
                            2,
                        );
                        leanh::lean_closure_set(v___f_2276_, 0, v_inst_2251_);
                        leanh::lean_closure_set(v___f_2276_, 1, v_key_2254_);
                        v___x_2277_ = lean_nat_dec_le(v___x_2272_, v___x_2272_);
                        if v___x_2277_ == 0 {
                            if v___x_2275_ == 0 {
                                leanh::lean_dec_ref(v___f_2276_);
                                leanh::lean_dec_ref(v_entries_2256_);
                                v___y_2261_ = v___x_2273_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2278_ = 0usize;
                                v___x_2279_ = lean_usize_of_nat(v___x_2272_);
                                v___x_2280_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v___x_2274_,
                                        v___f_2276_,
                                        v_entries_2256_,
                                        v___x_2278_,
                                        v___x_2279_,
                                        v___x_2273_,
                                    );
                                v___y_2261_ = v___x_2280_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2281_ = 0usize;
                            v___x_2282_ = lean_usize_of_nat(v___x_2272_);
                            v___x_2283_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_2274_,
                                    v___f_2276_,
                                    v_entries_2256_,
                                    v___x_2281_,
                                    v___x_2282_,
                                    v___x_2273_,
                                );
                            v___y_2261_ = v___x_2283_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2262_ = lean_array_get_size(v___y_2261_);
                v___x_2263_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
                v___x_2264_ = lean_nat_dec_lt(v___x_2259_, v___x_2262_);
                if v___x_2264_ == 0 {
                    leanh::lean_dec_ref(v___y_2261_);
                    leanh::lean_dec_ref(v___f_2257_);
                    return v___x_2258_;
                } else {
                    v___x_2265_ = lean_nat_dec_le(v___x_2262_, v___x_2262_);
                    if v___x_2265_ == 0 {
                        if v___x_2264_ == 0 {
                            leanh::lean_dec_ref(v___y_2261_);
                            leanh::lean_dec_ref(v___f_2257_);
                            return v___x_2258_;
                        } else {
                            v___x_2266_ = 0usize;
                            v___x_2267_ = lean_usize_of_nat(v___x_2262_);
                            v___x_2268_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_2263_,
                                    v___f_2257_,
                                    v___y_2261_,
                                    v___x_2266_,
                                    v___x_2267_,
                                    v___x_2258_,
                                );
                            return v___x_2268_;
                        }
                    } else {
                        v___x_2269_ = 0usize;
                        v___x_2270_ = lean_usize_of_nat(v___x_2262_);
                        v___x_2271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2263_,
                            v___f_2257_,
                            v___y_2261_,
                            v___x_2269_,
                            v___x_2270_,
                            v___x_2258_,
                        );
                        return v___x_2271_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_erase(
    mut v_00_u03b1_2284_: *mut leanh::LeanObject,
    mut v_00_u03b2_2285_: *mut leanh::LeanObject,
    mut v_inst_2286_: *mut leanh::LeanObject,
    mut v_inst_2287_: *mut leanh::LeanObject,
    mut v_inst_2288_: *mut leanh::LeanObject,
    mut v_inst_2289_: *mut leanh::LeanObject,
    mut v_map_2290_: *mut leanh::LeanObject,
    mut v_key_2291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2292_: u8 = 0;
    let mut v_entries_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: u8 = 0;
    let mut v___x_2302_: u8 = 0;
    let mut v___x_2303_: usize = 0;
    let mut v___x_2304_: usize = 0;
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: usize = 0;
    let mut v___x_2307_: usize = 0;
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: u8 = 0;
    let mut v___f_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: u8 = 0;
    let mut v___x_2315_: usize = 0;
    let mut v___x_2316_: usize = 0;
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: usize = 0;
    let mut v___x_2319_: usize = 0;
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_key_2291_);
                leanh::lean_inc_ref(v_inst_2287_);
                leanh::lean_inc_ref(v_inst_2286_);
                v___x_2292_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
                    v_inst_2286_,
                    v_inst_2287_,
                    v_key_2291_,
                    v_map_2290_,
                );
                if v___x_2292_ == 0 {
                    leanh::lean_dec(v_key_2291_);
                    leanh::lean_dec_ref(v_inst_2287_);
                    leanh::lean_dec_ref(v_inst_2286_);
                    return v_map_2290_;
                } else {
                    v_entries_2293_ = leanh::lean_ctor_get(v_map_2290_, 0);
                    leanh::lean_inc_ref(v_entries_2293_);
                    leanh::lean_dec_ref(v_map_2290_);
                    leanh::lean_inc_ref(v_inst_2287_);
                    leanh::lean_inc_ref(v_inst_2286_);
                    v___f_2294_ = leanh::lean_alloc_closure(
                        l_Std_Internal_IndexMultiMap_erase___redArg___lam__1
                            as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_2294_, 0, v_inst_2286_);
                    leanh::lean_closure_set(v___f_2294_, 1, v_inst_2287_);
                    v___x_2295_ = l_Std_Internal_IndexMultiMap_empty(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_2286_,
                        v_inst_2287_,
                    );
                    leanh::lean_dec_ref(v_inst_2287_);
                    v___x_2296_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2309_ = lean_array_get_size(v_entries_2293_);
                    v___x_2310_ = l_Std_Internal_instInhabitedIndexMultiMap___closed__0;
                    v___x_2311_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
                    v___x_2312_ = lean_nat_dec_lt(v___x_2296_, v___x_2309_);
                    if v___x_2312_ == 0 {
                        leanh::lean_dec_ref(v_entries_2293_);
                        leanh::lean_dec(v_key_2291_);
                        leanh::lean_dec_ref(v_inst_2286_);
                        v___y_2298_ = v___x_2310_;
                        state = 1;
                        continue;
                    } else {
                        v___f_2313_ = leanh::lean_alloc_closure(
                            l_Std_Internal_IndexMultiMap_erase___redArg___lam__0
                                as *mut core::ffi::c_void,
                            4,
                            2,
                        );
                        leanh::lean_closure_set(v___f_2313_, 0, v_inst_2286_);
                        leanh::lean_closure_set(v___f_2313_, 1, v_key_2291_);
                        v___x_2314_ = lean_nat_dec_le(v___x_2309_, v___x_2309_);
                        if v___x_2314_ == 0 {
                            if v___x_2312_ == 0 {
                                leanh::lean_dec_ref(v___f_2313_);
                                leanh::lean_dec_ref(v_entries_2293_);
                                v___y_2298_ = v___x_2310_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2315_ = 0usize;
                                v___x_2316_ = lean_usize_of_nat(v___x_2309_);
                                v___x_2317_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v___x_2311_,
                                        v___f_2313_,
                                        v_entries_2293_,
                                        v___x_2315_,
                                        v___x_2316_,
                                        v___x_2310_,
                                    );
                                v___y_2298_ = v___x_2317_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2318_ = 0usize;
                            v___x_2319_ = lean_usize_of_nat(v___x_2309_);
                            v___x_2320_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_2311_,
                                    v___f_2313_,
                                    v_entries_2293_,
                                    v___x_2318_,
                                    v___x_2319_,
                                    v___x_2310_,
                                );
                            v___y_2298_ = v___x_2320_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2299_ = lean_array_get_size(v___y_2298_);
                v___x_2300_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
                v___x_2301_ = lean_nat_dec_lt(v___x_2296_, v___x_2299_);
                if v___x_2301_ == 0 {
                    leanh::lean_dec_ref(v___y_2298_);
                    leanh::lean_dec_ref(v___f_2294_);
                    return v___x_2295_;
                } else {
                    v___x_2302_ = lean_nat_dec_le(v___x_2299_, v___x_2299_);
                    if v___x_2302_ == 0 {
                        if v___x_2301_ == 0 {
                            leanh::lean_dec_ref(v___y_2298_);
                            leanh::lean_dec_ref(v___f_2294_);
                            return v___x_2295_;
                        } else {
                            v___x_2303_ = 0usize;
                            v___x_2304_ = lean_usize_of_nat(v___x_2299_);
                            v___x_2305_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_2300_,
                                    v___f_2294_,
                                    v___y_2298_,
                                    v___x_2303_,
                                    v___x_2304_,
                                    v___x_2295_,
                                );
                            return v___x_2305_;
                        }
                    } else {
                        v___x_2306_ = 0usize;
                        v___x_2307_ = lean_usize_of_nat(v___x_2299_);
                        v___x_2308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2300_,
                            v___f_2294_,
                            v___y_2298_,
                            v___x_2306_,
                            v___x_2307_,
                            v___x_2295_,
                        );
                        return v___x_2308_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_size___redArg(
    mut v_map_2321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_entries_2322_ = leanh::lean_ctor_get(v_map_2321_, 0);
    v___x_2323_ = lean_array_get_size(v_entries_2322_);
    return v___x_2323_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_size___redArg___boxed(
    mut v_map_2324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2325_ = l_Std_Internal_IndexMultiMap_size___redArg(v_map_2324_);
    leanh::lean_dec_ref(v_map_2324_);
    return v_res_2325_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_size(
    mut v_00_u03b1_2326_: *mut leanh::LeanObject,
    mut v_00_u03b2_2327_: *mut leanh::LeanObject,
    mut v_inst_2328_: *mut leanh::LeanObject,
    mut v_inst_2329_: *mut leanh::LeanObject,
    mut v_map_2330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_entries_2331_ = leanh::lean_ctor_get(v_map_2330_, 0);
    v___x_2332_ = lean_array_get_size(v_entries_2331_);
    return v___x_2332_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_size___boxed(
    mut v_00_u03b1_2333_: *mut leanh::LeanObject,
    mut v_00_u03b2_2334_: *mut leanh::LeanObject,
    mut v_inst_2335_: *mut leanh::LeanObject,
    mut v_inst_2336_: *mut leanh::LeanObject,
    mut v_map_2337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_Std_Internal_IndexMultiMap_size(
        v_00_u03b1_2333_,
        v_00_u03b2_2334_,
        v_inst_2335_,
        v_inst_2336_,
        v_map_2337_,
    );
    leanh::lean_dec_ref(v_map_2337_);
    leanh::lean_dec_ref(v_inst_2336_);
    leanh::lean_dec_ref(v_inst_2335_);
    return v_res_2338_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_isEmpty___redArg(
    mut v_map_2339_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_entries_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: u8 = 0;
    v_entries_2340_ = leanh::lean_ctor_get(v_map_2339_, 0);
    v___x_2341_ = lean_array_get_size(v_entries_2340_);
    v___x_2342_ = leanh::lean_unsigned_to_nat(0);
    v___x_2343_ = lean_nat_dec_eq(v___x_2341_, v___x_2342_);
    return v___x_2343_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_isEmpty___redArg___boxed(
    mut v_map_2344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2345_: u8 = 0;
    let mut v_r_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2345_ = l_Std_Internal_IndexMultiMap_isEmpty___redArg(v_map_2344_);
    leanh::lean_dec_ref(v_map_2344_);
    v_r_2346_ = leanh::lean_box((v_res_2345_) as usize);
    return v_r_2346_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_isEmpty(
    mut v_00_u03b1_2347_: *mut leanh::LeanObject,
    mut v_00_u03b2_2348_: *mut leanh::LeanObject,
    mut v_inst_2349_: *mut leanh::LeanObject,
    mut v_inst_2350_: *mut leanh::LeanObject,
    mut v_map_2351_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_entries_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: u8 = 0;
    v_entries_2352_ = leanh::lean_ctor_get(v_map_2351_, 0);
    v___x_2353_ = lean_array_get_size(v_entries_2352_);
    v___x_2354_ = leanh::lean_unsigned_to_nat(0);
    v___x_2355_ = lean_nat_dec_eq(v___x_2353_, v___x_2354_);
    return v___x_2355_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_isEmpty___boxed(
    mut v_00_u03b1_2356_: *mut leanh::LeanObject,
    mut v_00_u03b2_2357_: *mut leanh::LeanObject,
    mut v_inst_2358_: *mut leanh::LeanObject,
    mut v_inst_2359_: *mut leanh::LeanObject,
    mut v_map_2360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2361_: u8 = 0;
    let mut v_r_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2361_ = l_Std_Internal_IndexMultiMap_isEmpty(
        v_00_u03b1_2356_,
        v_00_u03b2_2357_,
        v_inst_2358_,
        v_inst_2359_,
        v_map_2360_,
    );
    leanh::lean_dec_ref(v_map_2360_);
    leanh::lean_dec_ref(v_inst_2359_);
    leanh::lean_dec_ref(v_inst_2358_);
    v_r_2362_ = leanh::lean_box((v_res_2361_) as usize);
    return v_r_2362_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_toArray___redArg(
    mut v_map_2363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_entries_2364_ = leanh::lean_ctor_get(v_map_2363_, 0);
    leanh::lean_inc_ref(v_entries_2364_);
    return v_entries_2364_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_toArray___redArg___boxed(
    mut v_map_2365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2366_ = l_Std_Internal_IndexMultiMap_toArray___redArg(v_map_2365_);
    leanh::lean_dec_ref(v_map_2365_);
    return v_res_2366_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_toArray(
    mut v_00_u03b1_2367_: *mut leanh::LeanObject,
    mut v_00_u03b2_2368_: *mut leanh::LeanObject,
    mut v_inst_2369_: *mut leanh::LeanObject,
    mut v_inst_2370_: *mut leanh::LeanObject,
    mut v_map_2371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_entries_2372_ = leanh::lean_ctor_get(v_map_2371_, 0);
    leanh::lean_inc_ref(v_entries_2372_);
    return v_entries_2372_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_toArray___boxed(
    mut v_00_u03b1_2373_: *mut leanh::LeanObject,
    mut v_00_u03b2_2374_: *mut leanh::LeanObject,
    mut v_inst_2375_: *mut leanh::LeanObject,
    mut v_inst_2376_: *mut leanh::LeanObject,
    mut v_map_2377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2378_ = l_Std_Internal_IndexMultiMap_toArray(
        v_00_u03b1_2373_,
        v_00_u03b2_2374_,
        v_inst_2375_,
        v_inst_2376_,
        v_map_2377_,
    );
    leanh::lean_dec_ref(v_map_2377_);
    leanh::lean_dec_ref(v_inst_2376_);
    leanh::lean_dec_ref(v_inst_2375_);
    return v_res_2378_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_toList___redArg(
    mut v_map_2379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_entries_2380_ = leanh::lean_ctor_get(v_map_2379_, 0);
    leanh::lean_inc_ref(v_entries_2380_);
    leanh::lean_dec_ref(v_map_2379_);
    v___x_2381_ = lean_array_to_list(v_entries_2380_);
    return v___x_2381_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_toList(
    mut v_00_u03b1_2382_: *mut leanh::LeanObject,
    mut v_00_u03b2_2383_: *mut leanh::LeanObject,
    mut v_inst_2384_: *mut leanh::LeanObject,
    mut v_inst_2385_: *mut leanh::LeanObject,
    mut v_map_2386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2387_ = l_Std_Internal_IndexMultiMap_toList___redArg(v_map_2386_);
    return v___x_2387_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_toList___boxed(
    mut v_00_u03b1_2388_: *mut leanh::LeanObject,
    mut v_00_u03b2_2389_: *mut leanh::LeanObject,
    mut v_inst_2390_: *mut leanh::LeanObject,
    mut v_inst_2391_: *mut leanh::LeanObject,
    mut v_map_2392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2393_ = l_Std_Internal_IndexMultiMap_toList(
        v_00_u03b1_2388_,
        v_00_u03b2_2389_,
        v_inst_2390_,
        v_inst_2391_,
        v_map_2392_,
    );
    leanh::lean_dec_ref(v_inst_2391_);
    leanh::lean_dec_ref(v_inst_2390_);
    return v_res_2393_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_merge___redArg(
    mut v_inst_2394_: *mut leanh::LeanObject,
    mut v_inst_2395_: *mut leanh::LeanObject,
    mut v_m1_2396_: *mut leanh::LeanObject,
    mut v_m2_2397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: u8 = 0;
    v_entries_2398_ = leanh::lean_ctor_get(v_m2_2397_, 0);
    leanh::lean_inc_ref(v_entries_2398_);
    leanh::lean_dec_ref(v_m2_2397_);
    v___x_2399_ = leanh::lean_unsigned_to_nat(0);
    v___x_2400_ = lean_array_get_size(v_entries_2398_);
    v___x_2401_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9;
    v___x_2402_ = lean_nat_dec_lt(v___x_2399_, v___x_2400_);
    if v___x_2402_ == 0 {
        leanh::lean_dec_ref(v_entries_2398_);
        leanh::lean_dec_ref(v_inst_2395_);
        leanh::lean_dec_ref(v_inst_2394_);
        return v_m1_2396_;
    } else {
        let mut v___f_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2404_: u8 = 0;
        v___f_2403_ = leanh::lean_alloc_closure(
            l_Std_Internal_IndexMultiMap_erase___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2403_, 0, v_inst_2394_);
        leanh::lean_closure_set(v___f_2403_, 1, v_inst_2395_);
        v___x_2404_ = lean_nat_dec_le(v___x_2400_, v___x_2400_);
        if v___x_2404_ == 0 {
            if v___x_2402_ == 0 {
                leanh::lean_dec_ref(v___f_2403_);
                leanh::lean_dec_ref(v_entries_2398_);
                return v_m1_2396_;
            } else {
                let mut v___x_2405_: usize = 0;
                let mut v___x_2406_: usize = 0;
                let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2405_ = 0usize;
                v___x_2406_ = lean_usize_of_nat(v___x_2400_);
                v___x_2407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2401_,
                    v___f_2403_,
                    v_entries_2398_,
                    v___x_2405_,
                    v___x_2406_,
                    v_m1_2396_,
                );
                return v___x_2407_;
            }
        } else {
            let mut v___x_2408_: usize = 0;
            let mut v___x_2409_: usize = 0;
            let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2408_ = 0usize;
            v___x_2409_ = lean_usize_of_nat(v___x_2400_);
            v___x_2410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_2401_,
                v___f_2403_,
                v_entries_2398_,
                v___x_2408_,
                v___x_2409_,
                v_m1_2396_,
            );
            return v___x_2410_;
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_merge(
    mut v_00_u03b1_2411_: *mut leanh::LeanObject,
    mut v_00_u03b2_2412_: *mut leanh::LeanObject,
    mut v_inst_2413_: *mut leanh::LeanObject,
    mut v_inst_2414_: *mut leanh::LeanObject,
    mut v_inst_2415_: *mut leanh::LeanObject,
    mut v_inst_2416_: *mut leanh::LeanObject,
    mut v_m1_2417_: *mut leanh::LeanObject,
    mut v_m2_2418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2419_ = l_Std_Internal_IndexMultiMap_merge___redArg(
        v_inst_2413_,
        v_inst_2414_,
        v_m1_2417_,
        v_m2_2418_,
    );
    return v___x_2419_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(
    mut v_inst_2420_: *mut leanh::LeanObject,
    mut v_inst_2421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2422_ = l_Std_Internal_IndexMultiMap_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_2420_,
        v_inst_2421_,
    );
    return v___x_2422_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg___boxed(
    mut v_inst_2423_: *mut leanh::LeanObject,
    mut v_inst_2424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2425_ =
        l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(v_inst_2423_, v_inst_2424_);
    leanh::lean_dec_ref(v_inst_2424_);
    leanh::lean_dec_ref(v_inst_2423_);
    return v_res_2425_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instEmptyCollection(
    mut v_00_u03b1_2426_: *mut leanh::LeanObject,
    mut v_00_u03b2_2427_: *mut leanh::LeanObject,
    mut v_inst_2428_: *mut leanh::LeanObject,
    mut v_inst_2429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2430_ = l_Std_Internal_IndexMultiMap_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_2428_,
        v_inst_2429_,
    );
    return v___x_2430_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instEmptyCollection___boxed(
    mut v_00_u03b1_2431_: *mut leanh::LeanObject,
    mut v_00_u03b2_2432_: *mut leanh::LeanObject,
    mut v_inst_2433_: *mut leanh::LeanObject,
    mut v_inst_2434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2435_ = l_Std_Internal_IndexMultiMap_instEmptyCollection(
        v_00_u03b1_2431_,
        v_00_u03b2_2432_,
        v_inst_2433_,
        v_inst_2434_,
    );
    leanh::lean_dec_ref(v_inst_2434_);
    leanh::lean_dec_ref(v_inst_2433_);
    return v_res_2435_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1(
    mut v_inst_2436_: *mut leanh::LeanObject,
    mut v_inst_2437_: *mut leanh::LeanObject,
    mut v_x_2438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2445_: u8 = 0;
    let mut v_i_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2439_ = leanh::lean_ctor_get(v_x_2438_, 0);
                leanh::lean_inc(v_fst_2439_);
                v___x_2440_ = l_Std_Internal_IndexMultiMap_empty(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_2436_,
                    v_inst_2437_,
                );
                v_entries_2441_ = leanh::lean_ctor_get(v___x_2440_, 0);
                v_indexes_2442_ = leanh::lean_ctor_get(v___x_2440_, 1);
                v_isSharedCheck_2453_ = (!leanh::lean_is_exclusive(v___x_2440_)) as u8;
                if v_isSharedCheck_2453_ == 0 {
                    v___x_2444_ = v___x_2440_;
                    v_isShared_2445_ = v_isSharedCheck_2453_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_2442_);
                    leanh::lean_inc(v_entries_2441_);
                    leanh::lean_dec(v___x_2440_);
                    v___x_2444_ = leanh::lean_box(0);
                    v_isShared_2445_ = v_isSharedCheck_2453_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_i_2446_ = lean_array_get_size(v_entries_2441_);
                v_f_2447_ = leanh::lean_alloc_closure(
                    l_Std_Internal_IndexMultiMap_insert___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v_f_2447_, 0, v_i_2446_);
                v_entries_2448_ = lean_array_push(v_entries_2441_, v_x_2438_);
                v_indexes_2449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v_inst_2436_,
                    v_inst_2437_,
                    v_indexes_2442_,
                    v_fst_2439_,
                    v_f_2447_,
                );
                if v_isShared_2445_ == 0 {
                    leanh::lean_ctor_set(v___x_2444_, 1, v_indexes_2449_);
                    leanh::lean_ctor_set(v___x_2444_, 0, v_entries_2448_);
                    v___x_2451_ = v___x_2444_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2452_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_entries_2448_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_indexes_2449_);
                    v___x_2451_ = v_reuseFailAlloc_2452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(
    mut v_inst_2454_: *mut leanh::LeanObject,
    mut v_inst_2455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2456_ = leanh::lean_alloc_closure(
        l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2456_, 0, v_inst_2454_);
    leanh::lean_closure_set(v___f_2456_, 1, v_inst_2455_);
    return v___f_2456_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_2457_: *mut leanh::LeanObject,
    mut v_00_u03b2_2458_: *mut leanh::LeanObject,
    mut v_inst_2459_: *mut leanh::LeanObject,
    mut v_inst_2460_: *mut leanh::LeanObject,
    mut v_inst_2461_: *mut leanh::LeanObject,
    mut v_inst_2462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2463_ = leanh::lean_alloc_closure(
        l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2463_, 0, v_inst_2459_);
    leanh::lean_closure_set(v___f_2463_, 1, v_inst_2460_);
    return v___f_2463_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1(
    mut v_inst_2464_: *mut leanh::LeanObject,
    mut v_inst_2465_: *mut leanh::LeanObject,
    mut v_x_2466_: *mut leanh::LeanObject,
    mut v_m_2467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2473_: u8 = 0;
    let mut v_i_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2468_ = leanh::lean_ctor_get(v_x_2466_, 0);
                leanh::lean_inc(v_fst_2468_);
                v_entries_2469_ = leanh::lean_ctor_get(v_m_2467_, 0);
                v_indexes_2470_ = leanh::lean_ctor_get(v_m_2467_, 1);
                v_isSharedCheck_2481_ = (!leanh::lean_is_exclusive(v_m_2467_)) as u8;
                if v_isSharedCheck_2481_ == 0 {
                    v___x_2472_ = v_m_2467_;
                    v_isShared_2473_ = v_isSharedCheck_2481_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_indexes_2470_);
                    leanh::lean_inc(v_entries_2469_);
                    leanh::lean_dec(v_m_2467_);
                    v___x_2472_ = leanh::lean_box(0);
                    v_isShared_2473_ = v_isSharedCheck_2481_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_i_2474_ = lean_array_get_size(v_entries_2469_);
                v_f_2475_ = leanh::lean_alloc_closure(
                    l_Std_Internal_IndexMultiMap_insert___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v_f_2475_, 0, v_i_2474_);
                v_entries_2476_ = lean_array_push(v_entries_2469_, v_x_2466_);
                v_indexes_2477_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v_inst_2464_,
                    v_inst_2465_,
                    v_indexes_2470_,
                    v_fst_2468_,
                    v_f_2475_,
                );
                if v_isShared_2473_ == 0 {
                    leanh::lean_ctor_set(v___x_2472_, 1, v_indexes_2477_);
                    leanh::lean_ctor_set(v___x_2472_, 0, v_entries_2476_);
                    v___x_2479_ = v___x_2472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2480_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_entries_2476_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_indexes_2477_);
                    v___x_2479_ = v_reuseFailAlloc_2480_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(
    mut v_inst_2482_: *mut leanh::LeanObject,
    mut v_inst_2483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2484_ = leanh::lean_alloc_closure(
        l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2484_, 0, v_inst_2482_);
    leanh::lean_closure_set(v___f_2484_, 1, v_inst_2483_);
    return v___f_2484_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_2485_: *mut leanh::LeanObject,
    mut v_00_u03b2_2486_: *mut leanh::LeanObject,
    mut v_inst_2487_: *mut leanh::LeanObject,
    mut v_inst_2488_: *mut leanh::LeanObject,
    mut v_inst_2489_: *mut leanh::LeanObject,
    mut v_inst_2490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2491_ = leanh::lean_alloc_closure(
        l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2491_, 0, v_inst_2487_);
    leanh::lean_closure_set(v___f_2491_, 1, v_inst_2488_);
    return v___f_2491_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable___redArg(
    mut v_inst_2492_: *mut leanh::LeanObject,
    mut v_inst_2493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2494_ = leanh::lean_alloc_closure(
        l_Std_Internal_IndexMultiMap_merge as *mut core::ffi::c_void,
        8,
        6,
    );
    leanh::lean_closure_set(v___x_2494_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2494_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2494_, 2, v_inst_2492_);
    leanh::lean_closure_set(v___x_2494_, 3, v_inst_2493_);
    leanh::lean_closure_set(v___x_2494_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2494_, 5, leanh::lean_box(0));
    return v___x_2494_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_2495_: *mut leanh::LeanObject,
    mut v_00_u03b2_2496_: *mut leanh::LeanObject,
    mut v_inst_2497_: *mut leanh::LeanObject,
    mut v_inst_2498_: *mut leanh::LeanObject,
    mut v_inst_2499_: *mut leanh::LeanObject,
    mut v_inst_2500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2501_ = leanh::lean_alloc_closure(
        l_Std_Internal_IndexMultiMap_merge as *mut core::ffi::c_void,
        8,
        6,
    );
    leanh::lean_closure_set(v___x_2501_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2501_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2501_, 2, v_inst_2497_);
    leanh::lean_closure_set(v___x_2501_, 3, v_inst_2498_);
    leanh::lean_closure_set(v___x_2501_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2501_, 5, leanh::lean_box(0));
    return v___x_2501_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0(
    mut v_f_2502_: *mut leanh::LeanObject,
    mut v_a_2503_: *mut leanh::LeanObject,
    mut v_x_2504_: *mut leanh::LeanObject,
    mut v___y_2505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2506_ = leanh::lean_apply_2(v_f_2502_, v_a_2503_, v___y_2505_);
    return v___x_2506_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1(
    mut v_inst_2507_: *mut leanh::LeanObject,
    mut v_00_u03b2_2508_: *mut leanh::LeanObject,
    mut v_map_2509_: *mut leanh::LeanObject,
    mut v_b_2510_: *mut leanh::LeanObject,
    mut v_f_2511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_entries_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2514_: usize = 0;
    let mut v___x_2515_: usize = 0;
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_entries_2512_ = leanh::lean_ctor_get(v_map_2509_, 0);
    leanh::lean_inc_ref(v_entries_2512_);
    leanh::lean_dec_ref(v_map_2509_);
    v___f_2513_ = leanh::lean_alloc_closure(
        l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2513_, 0, v_f_2511_);
    v_sz_2514_ = lean_array_size(v_entries_2512_);
    v___x_2515_ = 0usize;
    v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_2507_,
        v_entries_2512_,
        v___f_2513_,
        v_sz_2514_,
        v___x_2515_,
        v_b_2510_,
    );
    return v___x_2516_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg(
    mut v_inst_2517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2518_ = leanh::lean_alloc_closure(
        l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2518_, 0, v_inst_2517_);
    return v___f_2518_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instForInProdOfMonad(
    mut v_00_u03b1_2519_: *mut leanh::LeanObject,
    mut v_00_u03b2_2520_: *mut leanh::LeanObject,
    mut v_inst_2521_: *mut leanh::LeanObject,
    mut v_inst_2522_: *mut leanh::LeanObject,
    mut v_m_2523_: *mut leanh::LeanObject,
    mut v_inst_2524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2525_ = leanh::lean_alloc_closure(
        l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2525_, 0, v_inst_2524_);
    return v___f_2525_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_instForInProdOfMonad___boxed(
    mut v_00_u03b1_2526_: *mut leanh::LeanObject,
    mut v_00_u03b2_2527_: *mut leanh::LeanObject,
    mut v_inst_2528_: *mut leanh::LeanObject,
    mut v_inst_2529_: *mut leanh::LeanObject,
    mut v_m_2530_: *mut leanh::LeanObject,
    mut v_inst_2531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2532_ = l_Std_Internal_IndexMultiMap_instForInProdOfMonad(
        v_00_u03b1_2526_,
        v_00_u03b2_2527_,
        v_inst_2528_,
        v_inst_2529_,
        v_m_2530_,
        v_inst_2531_,
    );
    leanh::lean_dec_ref(v_inst_2529_);
    leanh::lean_dec_ref(v_inst_2528_);
    return v_res_2532_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Internal_IndexMultiMap(
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
    res = runtime_initialize_Init_Data_Int_OfNat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Internal_IndexMultiMap(
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
pub unsafe fn initialize_Std_Http_Internal_IndexMultiMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
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
    res = initialize_Init_Data_Int_OfNat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal_IndexMultiMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Internal_IndexMultiMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Internal_IndexMultiMap(builtin);
}