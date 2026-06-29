// Lean compiler output
// Module: Lean.Data.PersistentHashMap
// Imports: Init.Data.Array.BasicAux Init.Data.UInt.Basic Init.Control.Except Init.Data.Array.Basic Init.Data.String.Defs Init.Data.ToString.Macro
use crate::r#gen::Init::Control::Except::{
    initialize_Init_Control_Except, l_ExceptT_bind, l_ExceptT_instMonad___redArg___lam__1,
    l_ExceptT_instMonad___redArg___lam__4, l_ExceptT_instMonad___redArg___lam__7,
    l_ExceptT_instMonad___redArg___lam__9, l_ExceptT_map, l_ExceptT_pure,
    runtime_initialize_Init_Control_Except,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_eraseIdx___redArg,
    l_Array_finIdxOf_x3f___redArg, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::BasicAux::{
    initialize_Init_Data_Array_BasicAux, l_Array_mapM_x27___redArg,
    runtime_initialize_Init_Data_Array_BasicAux,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, runtime_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Data::UInt::Basic::{
    initialize_Init_Data_UInt_Basic, runtime_initialize_Init_Data_UInt_Basic,
};
use crate::r#gen::Init::Prelude::l_panic___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_mk_array,
};
use crate::ffi::{lean_array_fset, lean_array_set};
use crate::ffi::lean_string_append;
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_usize_dec_eq,
};
pub static l_Lean_PersistentHashMap_instInhabitedNode___closed__0_value:
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
static mut l_Lean_PersistentHashMap_instInhabitedNode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_instInhabitedNode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_instInhabitedNode___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_PersistentHashMap_instInhabitedNode___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_PersistentHashMap_instInhabitedNode___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_instInhabitedNode___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_PersistentHashMap_shift: usize = 0;
pub static mut l_Lean_PersistentHashMap_branching: usize = 0;
pub static mut l_Lean_PersistentHashMap_maxDepth: usize = 0;
pub static mut l_Lean_PersistentHashMap_maxCollisions: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PersistentHashMap_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PersistentHashMap_empty___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PersistentHashMap_insertAux___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PersistentHashMap_insertAux___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PersistentHashMap_insertAux___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PersistentHashMap_find_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116,
        72, 97, 115, 104, 77, 97, 112, 0,
    ],
};
static mut l_Lean_PersistentHashMap_find_x21___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_find_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_find_x21___redArg___closed__1_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116, 72, 97, 115, 104,
        77, 97, 112, 46, 102, 105, 110, 100, 33, 0,
    ],
};
static mut l_Lean_PersistentHashMap_find_x21___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_find_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_find_x21___redArg___closed__2_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 109,
        97, 112, 0,
    ],
};
static mut l_Lean_PersistentHashMap_find_x21___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_find_x21___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PersistentHashMap_find_x21___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PersistentHashMap_foldl___redArg___closed__0_value:
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
static mut l_Lean_PersistentHashMap_foldl___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_foldl___redArg___closed__1_value:
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
static mut l_Lean_PersistentHashMap_foldl___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_foldl___redArg___closed__2_value:
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
static mut l_Lean_PersistentHashMap_foldl___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_foldl___redArg___closed__3_value:
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
static mut l_Lean_PersistentHashMap_foldl___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_foldl___redArg___closed__4_value:
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
static mut l_Lean_PersistentHashMap_foldl___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_foldl___redArg___closed__5_value:
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
static mut l_Lean_PersistentHashMap_foldl___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_foldl___redArg___closed__6_value:
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
static mut l_Lean_PersistentHashMap_foldl___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_foldl___redArg___closed__7_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_PersistentHashMap_foldl___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_foldl___redArg___closed__8_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_PersistentHashMap_foldl___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_foldl___redArg___closed__9_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_PersistentHashMap_foldl___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_foldl___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_forIn___redArg___closed__0_value:
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
    m_fun: l_Lean_PersistentHashMap_forIn___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentHashMap_forIn___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_forIn___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_toList___redArg___closed__0_value:
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
    m_fun: l_Lean_PersistentHashMap_toList___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentHashMap_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_toArray___redArg___closed__0_value:
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
    m_fun: l_Lean_PersistentHashMap_toArray___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentHashMap_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_toArray___redArg___closed__1_value:
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
static mut l_Lean_PersistentHashMap_toArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_toArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_stats___redArg___closed__0_value: crate::leanh::LeanCtorObject<
    4,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_PersistentHashMap_stats___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_stats___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_Stats_toString___closed__0_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [123, 32, 110, 111, 100, 101, 115, 32, 58, 61, 32, 0],
};
static mut l_Lean_PersistentHashMap_Stats_toString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_Stats_toString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_Stats_toString___closed__1_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [44, 32, 110, 117, 108, 108, 32, 58, 61, 32, 0],
};
static mut l_Lean_PersistentHashMap_Stats_toString___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_Stats_toString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_Stats_toString___closed__2_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        44, 32, 99, 111, 108, 108, 105, 115, 105, 111, 110, 115, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_PersistentHashMap_Stats_toString___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_Stats_toString___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_Stats_toString___closed__3_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [44, 32, 100, 101, 112, 116, 104, 32, 58, 61, 32, 0],
};
static mut l_Lean_PersistentHashMap_Stats_toString___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_Stats_toString___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_Stats_toString___closed__4_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [125, 0],
};
static mut l_Lean_PersistentHashMap_Stats_toString___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_Stats_toString___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_instToStringStats___closed__0_value:
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
    m_fun: l_Lean_PersistentHashMap_Stats_toString as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentHashMap_instToStringStats___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_instToStringStats___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_PersistentHashMap_instToStringStats: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_instToStringStats___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_PersistentHashMap_Entry_ctorIdx___redArg(
    mut v_x_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1929_) {
        0 => {
            let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1930_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1930_;
        }
        1 => {
            let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1931_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1931_;
        }
        _ => {
            let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1932_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1932_;
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_ctorIdx___redArg___boxed(
    mut v_x_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ = l_Lean_PersistentHashMap_Entry_ctorIdx___redArg(v_x_1933_);
    crate::leanh::lean_dec(v_x_1933_);
    return v_res_1934_;
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_ctorIdx(
    mut v_00_u03b1_1935_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1936_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1937_: *mut crate::leanh::LeanObject,
    mut v_x_1938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1939_ = l_Lean_PersistentHashMap_Entry_ctorIdx___redArg(v_x_1938_);
    return v___x_1939_;
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_ctorIdx___boxed(
    mut v_00_u03b1_1940_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1941_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1942_: *mut crate::leanh::LeanObject,
    mut v_x_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1944_ = l_Lean_PersistentHashMap_Entry_ctorIdx(
        v_00_u03b1_1940_,
        v_00_u03b2_1941_,
        v_00_u03c3_1942_,
        v_x_1943_,
    );
    crate::leanh::lean_dec(v_x_1943_);
    return v_res_1944_;
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_ctorElim___redArg(
    mut v_t_1945_: *mut crate::leanh::LeanObject,
    mut v_k_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_1945_) {
        0 => {
            let mut v_key_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_key_1947_ = crate::leanh::lean_ctor_get(v_t_1945_, 0);
            crate::leanh::lean_inc(v_key_1947_);
            v_val_1948_ = crate::leanh::lean_ctor_get(v_t_1945_, 1);
            crate::leanh::lean_inc(v_val_1948_);
            crate::leanh::lean_dec_ref_known(v_t_1945_, 2);
            v___x_1949_ = crate::leanh::lean_apply_2(v_k_1946_, v_key_1947_, v_val_1948_);
            return v___x_1949_;
        }
        1 => {
            let mut v_node_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_node_1950_ = crate::leanh::lean_ctor_get(v_t_1945_, 0);
            crate::leanh::lean_inc(v_node_1950_);
            crate::leanh::lean_dec_ref_known(v_t_1945_, 1);
            v___x_1951_ = crate::leanh::lean_apply_1(v_k_1946_, v_node_1950_);
            return v___x_1951_;
        }
        _ => {
            return v_k_1946_;
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_ctorElim(
    mut v_00_u03b1_1952_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1953_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1954_: *mut crate::leanh::LeanObject,
    mut v_motive_1955_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1956_: *mut crate::leanh::LeanObject,
    mut v_t_1957_: *mut crate::leanh::LeanObject,
    mut v_h_1958_: *mut crate::leanh::LeanObject,
    mut v_k_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_1957_, v_k_1959_);
    return v___x_1960_;
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_ctorElim___boxed(
    mut v_00_u03b1_1961_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1962_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1963_: *mut crate::leanh::LeanObject,
    mut v_motive_1964_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1965_: *mut crate::leanh::LeanObject,
    mut v_t_1966_: *mut crate::leanh::LeanObject,
    mut v_h_1967_: *mut crate::leanh::LeanObject,
    mut v_k_1968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1969_ = l_Lean_PersistentHashMap_Entry_ctorElim(
        v_00_u03b1_1961_,
        v_00_u03b2_1962_,
        v_00_u03c3_1963_,
        v_motive_1964_,
        v_ctorIdx_1965_,
        v_t_1966_,
        v_h_1967_,
        v_k_1968_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1965_);
    return v_res_1969_;
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_entry_elim___redArg(
    mut v_t_1970_: *mut crate::leanh::LeanObject,
    mut v_entry_1971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1972_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_1970_, v_entry_1971_);
    return v___x_1972_;
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_entry_elim(
    mut v_00_u03b1_1973_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1974_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1975_: *mut crate::leanh::LeanObject,
    mut v_motive_1976_: *mut crate::leanh::LeanObject,
    mut v_t_1977_: *mut crate::leanh::LeanObject,
    mut v_h_1978_: *mut crate::leanh::LeanObject,
    mut v_entry_1979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1980_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_1977_, v_entry_1979_);
    return v___x_1980_;
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_ref_elim___redArg(
    mut v_t_1981_: *mut crate::leanh::LeanObject,
    mut v_ref_1982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1983_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_1981_, v_ref_1982_);
    return v___x_1983_;
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_ref_elim(
    mut v_00_u03b1_1984_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1985_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1986_: *mut crate::leanh::LeanObject,
    mut v_motive_1987_: *mut crate::leanh::LeanObject,
    mut v_t_1988_: *mut crate::leanh::LeanObject,
    mut v_h_1989_: *mut crate::leanh::LeanObject,
    mut v_ref_1990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1991_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_1988_, v_ref_1990_);
    return v___x_1991_;
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_null_elim___redArg(
    mut v_t_1992_: *mut crate::leanh::LeanObject,
    mut v_null_1993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1994_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_1992_, v_null_1993_);
    return v___x_1994_;
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_null_elim(
    mut v_00_u03b1_1995_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1996_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1997_: *mut crate::leanh::LeanObject,
    mut v_motive_1998_: *mut crate::leanh::LeanObject,
    mut v_t_1999_: *mut crate::leanh::LeanObject,
    mut v_h_2000_: *mut crate::leanh::LeanObject,
    mut v_null_2001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2002_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_1999_, v_null_2001_);
    return v___x_2002_;
}
pub unsafe fn l_Lean_PersistentHashMap_instInhabitedEntry(
    mut v_00_u03b1_2003_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2004_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2006_ = crate::leanh::lean_box(2);
    return v___x_2006_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_ctorIdx___redArg(
    mut v_x_2007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2007_) == 0 {
        let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2008_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2008_;
    } else {
        let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2009_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_2009_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Node_ctorIdx___redArg___boxed(
    mut v_x_2010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2011_ = l_Lean_PersistentHashMap_Node_ctorIdx___redArg(v_x_2010_);
    crate::leanh::lean_dec_ref(v_x_2010_);
    return v_res_2011_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_ctorIdx(
    mut v_00_u03b1_2012_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2013_: *mut crate::leanh::LeanObject,
    mut v_x_2014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2015_ = l_Lean_PersistentHashMap_Node_ctorIdx___redArg(v_x_2014_);
    return v___x_2015_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_ctorIdx___boxed(
    mut v_00_u03b1_2016_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2017_: *mut crate::leanh::LeanObject,
    mut v_x_2018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2019_ =
        l_Lean_PersistentHashMap_Node_ctorIdx(v_00_u03b1_2016_, v_00_u03b2_2017_, v_x_2018_);
    crate::leanh::lean_dec_ref(v_x_2018_);
    return v_res_2019_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_ctorElim___redArg(
    mut v_t_2020_: *mut crate::leanh::LeanObject,
    mut v_k_2021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2020_) == 0 {
        let mut v_es_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_es_2022_ = crate::leanh::lean_ctor_get(v_t_2020_, 0);
        crate::leanh::lean_inc_ref(v_es_2022_);
        crate::leanh::lean_dec_ref_known(v_t_2020_, 1);
        v___x_2023_ = crate::leanh::lean_apply_1(v_k_2021_, v_es_2022_);
        return v___x_2023_;
    } else {
        let mut v_ks_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ks_2024_ = crate::leanh::lean_ctor_get(v_t_2020_, 0);
        crate::leanh::lean_inc_ref(v_ks_2024_);
        v_vs_2025_ = crate::leanh::lean_ctor_get(v_t_2020_, 1);
        crate::leanh::lean_inc_ref(v_vs_2025_);
        crate::leanh::lean_dec_ref_known(v_t_2020_, 2);
        v___x_2026_ = crate::leanh::lean_apply_3(
            v_k_2021_,
            v_ks_2024_,
            v_vs_2025_,
            crate::leanh::lean_box(0),
        );
        return v___x_2026_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Node_ctorElim(
    mut v_00_u03b1_2027_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2028_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2029_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2030_: *mut crate::leanh::LeanObject,
    mut v_t_2031_: *mut crate::leanh::LeanObject,
    mut v_h_2032_: *mut crate::leanh::LeanObject,
    mut v_k_2033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_2031_, v_k_2033_);
    return v___x_2034_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_ctorElim___boxed(
    mut v_00_u03b1_2035_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2036_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2037_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2038_: *mut crate::leanh::LeanObject,
    mut v_t_2039_: *mut crate::leanh::LeanObject,
    mut v_h_2040_: *mut crate::leanh::LeanObject,
    mut v_k_2041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2042_ = l_Lean_PersistentHashMap_Node_ctorElim(
        v_00_u03b1_2035_,
        v_00_u03b2_2036_,
        v_motive__1_2037_,
        v_ctorIdx_2038_,
        v_t_2039_,
        v_h_2040_,
        v_k_2041_,
    );
    crate::leanh::lean_dec(v_ctorIdx_2038_);
    return v_res_2042_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_entries_elim___redArg(
    mut v_t_2043_: *mut crate::leanh::LeanObject,
    mut v_entries_2044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2045_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_2043_, v_entries_2044_);
    return v___x_2045_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_entries_elim(
    mut v_00_u03b1_2046_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2047_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2048_: *mut crate::leanh::LeanObject,
    mut v_t_2049_: *mut crate::leanh::LeanObject,
    mut v_h_2050_: *mut crate::leanh::LeanObject,
    mut v_entries_2051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2052_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_2049_, v_entries_2051_);
    return v___x_2052_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_collision_elim___redArg(
    mut v_t_2053_: *mut crate::leanh::LeanObject,
    mut v_collision_2054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2055_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_2053_, v_collision_2054_);
    return v___x_2055_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_collision_elim(
    mut v_00_u03b1_2056_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2057_: *mut crate::leanh::LeanObject,
    mut v_motive__1_2058_: *mut crate::leanh::LeanObject,
    mut v_t_2059_: *mut crate::leanh::LeanObject,
    mut v_h_2060_: *mut crate::leanh::LeanObject,
    mut v_collision_2061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2062_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_2059_, v_collision_2061_);
    return v___x_2062_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(
    mut v_as_2063_: *mut crate::leanh::LeanObject,
    mut v_i_2064_: usize,
    mut v_stop_2065_: usize,
) -> u8 {
    let mut v___x_2066_: u8 = 0;
    let mut v___x_2067_: u8 = 0;
    let mut v___y_2069_: u8 = 0;
    let mut v___x_2070_: usize = 0;
    let mut v___x_2071_: usize = 0;
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: u8 = 0;
    let mut v___x_2076_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2066_ = lean_usize_dec_eq(v_i_2064_, v_stop_2065_);
                if v___x_2066_ == 0 {
                    v___x_2067_ = 1;
                    v___x_2073_ = lean_array_uget_borrowed(v_as_2063_, v_i_2064_);
                    match crate::leanh::lean_obj_tag(v___x_2073_) {
                        0 => {
                            return v___x_2067_;
                        }
                        1 => {
                            v_node_2074_ = crate::leanh::lean_ctor_get(v___x_2073_, 0);
                            v___x_2075_ =
                                l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_node_2074_);
                            if v___x_2075_ == 0 {
                                return v___x_2067_;
                            } else {
                                v___y_2069_ = v___x_2066_;
                                state = 1;
                                continue;
                            }
                        }
                        _ => {
                            v___y_2069_ = v___x_2066_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_2076_ = 0;
                    return v___x_2076_;
                }
            }
            1 => {
                if v___y_2069_ == 0 {
                    v___x_2070_ = 1usize;
                    v___x_2071_ = lean_usize_add(v_i_2064_, v___x_2070_);
                    v_i_2064_ = v___x_2071_;
                    state = 0;
                    continue;
                } else {
                    return v___x_2067_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Node_isEmpty___redArg(
    mut v_x_2077_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2077_) == 0 {
        let mut v_es_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2081_: u8 = 0;
        v_es_2078_ = crate::leanh::lean_ctor_get(v_x_2077_, 0);
        v___x_2079_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2080_ = lean_array_get_size(v_es_2078_);
        v___x_2081_ = lean_nat_dec_lt(v___x_2079_, v___x_2080_);
        if v___x_2081_ == 0 {
            let mut v___x_2082_: u8 = 0;
            v___x_2082_ = 1;
            return v___x_2082_;
        } else {
            if v___x_2081_ == 0 {
                return v___x_2081_;
            } else {
                let mut v___x_2083_: usize = 0;
                let mut v___x_2084_: usize = 0;
                let mut v___x_2085_: u8 = 0;
                v___x_2083_ = 0usize;
                v___x_2084_ = lean_usize_of_nat(v___x_2080_);
                v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_es_2078_, v___x_2083_, v___x_2084_);
                if v___x_2085_ == 0 {
                    return v___x_2081_;
                } else {
                    let mut v___x_2086_: u8 = 0;
                    v___x_2086_ = 0;
                    return v___x_2086_;
                }
            }
        }
    } else {
        let mut v___x_2087_: u8 = 0;
        v___x_2087_ = 0;
        return v___x_2087_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Node_isEmpty___redArg___boxed(
    mut v_x_2088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2089_: u8 = 0;
    let mut v_r_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2089_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2088_);
    crate::leanh::lean_dec_ref(v_x_2088_);
    v_r_2090_ = crate::leanh::lean_box((v_res_2089_) as usize);
    return v_r_2090_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg___boxed(
    mut v_as_2091_: *mut crate::leanh::LeanObject,
    mut v_i_2092_: *mut crate::leanh::LeanObject,
    mut v_stop_2093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2094_: usize = 0;
    let mut v_stop_boxed_2095_: usize = 0;
    let mut v_res_2096_: u8 = 0;
    let mut v_r_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2094_ = crate::leanh::lean_unbox_usize(v_i_2092_);
    crate::leanh::lean_dec(v_i_2092_);
    v_stop_boxed_2095_ = crate::leanh::lean_unbox_usize(v_stop_2093_);
    crate::leanh::lean_dec(v_stop_2093_);
    v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_as_2091_, v_i_boxed_2094_, v_stop_boxed_2095_);
    crate::leanh::lean_dec_ref(v_as_2091_);
    v_r_2097_ = crate::leanh::lean_box((v_res_2096_) as usize);
    return v_r_2097_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_isEmpty(
    mut v_00_u03b1_2098_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2099_: *mut crate::leanh::LeanObject,
    mut v_x_2100_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2101_: u8 = 0;
    v___x_2101_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2100_);
    return v___x_2101_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_isEmpty___boxed(
    mut v_00_u03b1_2102_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2103_: *mut crate::leanh::LeanObject,
    mut v_x_2104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2105_: u8 = 0;
    let mut v_r_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2105_ =
        l_Lean_PersistentHashMap_Node_isEmpty(v_00_u03b1_2102_, v_00_u03b2_2103_, v_x_2104_);
    crate::leanh::lean_dec_ref(v_x_2104_);
    v_r_2106_ = crate::leanh::lean_box((v_res_2105_) as usize);
    return v_r_2106_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0(
    mut v_00_u03b1_2107_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2108_: *mut crate::leanh::LeanObject,
    mut v_as_2109_: *mut crate::leanh::LeanObject,
    mut v_i_2110_: usize,
    mut v_stop_2111_: usize,
) -> u8 {
    let mut v___x_2112_: u8 = 0;
    v___x_2112_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_as_2109_, v_i_2110_, v_stop_2111_);
    return v___x_2112_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___boxed(
    mut v_00_u03b1_2113_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2114_: *mut crate::leanh::LeanObject,
    mut v_as_2115_: *mut crate::leanh::LeanObject,
    mut v_i_2116_: *mut crate::leanh::LeanObject,
    mut v_stop_2117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2118_: usize = 0;
    let mut v_stop_boxed_2119_: usize = 0;
    let mut v_res_2120_: u8 = 0;
    let mut v_r_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2118_ = crate::leanh::lean_unbox_usize(v_i_2116_);
    crate::leanh::lean_dec(v_i_2116_);
    v_stop_boxed_2119_ = crate::leanh::lean_unbox_usize(v_stop_2117_);
    crate::leanh::lean_dec(v_stop_2117_);
    v_res_2120_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0(v_00_u03b1_2113_, v_00_u03b2_2114_, v_as_2115_, v_i_boxed_2118_, v_stop_boxed_2119_);
    crate::leanh::lean_dec_ref(v_as_2115_);
    v_r_2121_ = crate::leanh::lean_box((v_res_2120_) as usize);
    return v_r_2121_;
}
pub unsafe fn l_Lean_PersistentHashMap_instInhabitedNode(
    mut v_00_u03b1_2126_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2128_ = l_Lean_PersistentHashMap_instInhabitedNode___closed__1;
    return v___x_2128_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_shift() -> usize {
    let mut v___x_2129_: usize = 0;
    v___x_2129_ = 5usize;
    return v___x_2129_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_branching() -> usize {
    let mut v___x_2130_: usize = 0;
    v___x_2130_ = 32usize;
    return v___x_2130_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_maxDepth() -> usize {
    let mut v___x_2131_: usize = 0;
    v___x_2131_ = 7usize;
    return v___x_2131_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_maxCollisions() -> *mut crate::leanh::LeanObject {
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2132_ = crate::leanh::lean_unsigned_to_nat(4);
    return v___x_2132_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2133_ = crate::leanh::lean_box(2);
    v___x_2134_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2135_ = lean_mk_array(v___x_2134_, v___x_2133_);
    return v___x_2135_;
}
pub unsafe fn l_Lean_PersistentHashMap_mkEmptyEntriesArray(
    mut v_00_u03b1_2136_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2138_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0),
        core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0_once),
        _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0,
    );
    return v___x_2138_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2139_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2139_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2140_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___closed__0),
        core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___closed__0_once),
        _init_l_Lean_PersistentHashMap_empty___closed__0,
    );
    v___x_2141_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2141_, 0, v___x_2140_);
    return v___x_2141_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty(
    mut v_00_u03b1_2142_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2143_: *mut crate::leanh::LeanObject,
    mut v_inst_2144_: *mut crate::leanh::LeanObject,
    mut v_inst_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___closed__1_once),
        _init_l_Lean_PersistentHashMap_empty___closed__1,
    );
    return v___x_2146_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___boxed(
    mut v_00_u03b1_2147_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2148_: *mut crate::leanh::LeanObject,
    mut v_inst_2149_: *mut crate::leanh::LeanObject,
    mut v_inst_2150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2151_ = l_Lean_PersistentHashMap_empty(
        v_00_u03b1_2147_,
        v_00_u03b2_2148_,
        v_inst_2149_,
        v_inst_2150_,
    );
    crate::leanh::lean_dec_ref(v_inst_2150_);
    crate::leanh::lean_dec_ref(v_inst_2149_);
    return v_res_2151_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___redArg(
    mut v_x_2152_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2153_: u8 = 0;
    v___x_2153_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2152_);
    return v___x_2153_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___redArg___boxed(
    mut v_x_2154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2155_: u8 = 0;
    let mut v_r_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2155_ = l_Lean_PersistentHashMap_isEmpty___redArg(v_x_2154_);
    crate::leanh::lean_dec_ref(v_x_2154_);
    v_r_2156_ = crate::leanh::lean_box((v_res_2155_) as usize);
    return v_r_2156_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty(
    mut v_00_u03b1_2157_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2158_: *mut crate::leanh::LeanObject,
    mut v_x_2159_: *mut crate::leanh::LeanObject,
    mut v_x_2160_: *mut crate::leanh::LeanObject,
    mut v_x_2161_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2162_: u8 = 0;
    v___x_2162_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2161_);
    return v___x_2162_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___boxed(
    mut v_00_u03b1_2163_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2164_: *mut crate::leanh::LeanObject,
    mut v_x_2165_: *mut crate::leanh::LeanObject,
    mut v_x_2166_: *mut crate::leanh::LeanObject,
    mut v_x_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2168_: u8 = 0;
    let mut v_r_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2168_ = l_Lean_PersistentHashMap_isEmpty(
        v_00_u03b1_2163_,
        v_00_u03b2_2164_,
        v_x_2165_,
        v_x_2166_,
        v_x_2167_,
    );
    crate::leanh::lean_dec_ref(v_x_2167_);
    crate::leanh::lean_dec_ref(v_x_2166_);
    crate::leanh::lean_dec_ref(v_x_2165_);
    v_r_2169_ = crate::leanh::lean_box((v_res_2168_) as usize);
    return v_r_2169_;
}
pub unsafe fn l_Lean_PersistentHashMap_instInhabited(
    mut v_00_u03b1_2170_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2171_: *mut crate::leanh::LeanObject,
    mut v_inst_2172_: *mut crate::leanh::LeanObject,
    mut v_inst_2173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2174_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___closed__1_once),
        _init_l_Lean_PersistentHashMap_empty___closed__1,
    );
    return v___x_2174_;
}
pub unsafe fn l_Lean_PersistentHashMap_instInhabited___boxed(
    mut v_00_u03b1_2175_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2176_: *mut crate::leanh::LeanObject,
    mut v_inst_2177_: *mut crate::leanh::LeanObject,
    mut v_inst_2178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2179_ = l_Lean_PersistentHashMap_instInhabited(
        v_00_u03b1_2175_,
        v_00_u03b2_2176_,
        v_inst_2177_,
        v_inst_2178_,
    );
    crate::leanh::lean_dec_ref(v_inst_2178_);
    crate::leanh::lean_dec_ref(v_inst_2177_);
    return v_res_2179_;
}
pub unsafe fn l_Lean_PersistentHashMap_mkEmptyEntries(
    mut v_00_u03b1_2180_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2182_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___closed__1_once),
        _init_l_Lean_PersistentHashMap_empty___closed__1,
    );
    return v___x_2182_;
}
pub unsafe fn l_Lean_PersistentHashMap_mul2Shift(
    mut v_i_2183_: usize,
    mut v_shift_2184_: usize,
) -> usize {
    let mut v___x_2185_: usize = 0;
    v___x_2185_ = lean_usize_shift_left(v_i_2183_, v_shift_2184_);
    return v___x_2185_;
}
pub unsafe fn l_Lean_PersistentHashMap_mul2Shift___boxed(
    mut v_i_2186_: *mut crate::leanh::LeanObject,
    mut v_shift_2187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2188_: usize = 0;
    let mut v_shift_boxed_2189_: usize = 0;
    let mut v_res_2190_: usize = 0;
    let mut v_r_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2188_ = crate::leanh::lean_unbox_usize(v_i_2186_);
    crate::leanh::lean_dec(v_i_2186_);
    v_shift_boxed_2189_ = crate::leanh::lean_unbox_usize(v_shift_2187_);
    crate::leanh::lean_dec(v_shift_2187_);
    v_res_2190_ = l_Lean_PersistentHashMap_mul2Shift(v_i_boxed_2188_, v_shift_boxed_2189_);
    v_r_2191_ = crate::leanh::lean_box_usize(v_res_2190_);
    return v_r_2191_;
}
pub unsafe fn l_Lean_PersistentHashMap_div2Shift(
    mut v_i_2192_: usize,
    mut v_shift_2193_: usize,
) -> usize {
    let mut v___x_2194_: usize = 0;
    v___x_2194_ = lean_usize_shift_right(v_i_2192_, v_shift_2193_);
    return v___x_2194_;
}
pub unsafe fn l_Lean_PersistentHashMap_div2Shift___boxed(
    mut v_i_2195_: *mut crate::leanh::LeanObject,
    mut v_shift_2196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2197_: usize = 0;
    let mut v_shift_boxed_2198_: usize = 0;
    let mut v_res_2199_: usize = 0;
    let mut v_r_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2197_ = crate::leanh::lean_unbox_usize(v_i_2195_);
    crate::leanh::lean_dec(v_i_2195_);
    v_shift_boxed_2198_ = crate::leanh::lean_unbox_usize(v_shift_2196_);
    crate::leanh::lean_dec(v_shift_2196_);
    v_res_2199_ = l_Lean_PersistentHashMap_div2Shift(v_i_boxed_2197_, v_shift_boxed_2198_);
    v_r_2200_ = crate::leanh::lean_box_usize(v_res_2199_);
    return v_r_2200_;
}
pub unsafe fn l_Lean_PersistentHashMap_mod2Shift(
    mut v_i_2201_: usize,
    mut v_shift_2202_: usize,
) -> usize {
    let mut v___x_2203_: usize = 0;
    let mut v___x_2204_: usize = 0;
    let mut v___x_2205_: usize = 0;
    let mut v___x_2206_: usize = 0;
    v___x_2203_ = 1usize;
    v___x_2204_ = lean_usize_shift_left(v___x_2203_, v_shift_2202_);
    v___x_2205_ = lean_usize_sub(v___x_2204_, v___x_2203_);
    v___x_2206_ = lean_usize_land(v_i_2201_, v___x_2205_);
    return v___x_2206_;
}
pub unsafe fn l_Lean_PersistentHashMap_mod2Shift___boxed(
    mut v_i_2207_: *mut crate::leanh::LeanObject,
    mut v_shift_2208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2209_: usize = 0;
    let mut v_shift_boxed_2210_: usize = 0;
    let mut v_res_2211_: usize = 0;
    let mut v_r_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2209_ = crate::leanh::lean_unbox_usize(v_i_2207_);
    crate::leanh::lean_dec(v_i_2207_);
    v_shift_boxed_2210_ = crate::leanh::lean_unbox_usize(v_shift_2208_);
    crate::leanh::lean_dec(v_shift_2208_);
    v_res_2211_ = l_Lean_PersistentHashMap_mod2Shift(v_i_boxed_2209_, v_shift_boxed_2210_);
    v_r_2212_ = crate::leanh::lean_box_usize(v_res_2211_);
    return v_r_2212_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(
    mut v_inst_2213_: *mut crate::leanh::LeanObject,
    mut v_x_2214_: *mut crate::leanh::LeanObject,
    mut v_x_2215_: *mut crate::leanh::LeanObject,
    mut v_x_2216_: *mut crate::leanh::LeanObject,
    mut v_x_2217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2222_: u8 = 0;
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: u8 = 0;
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2218_ = crate::leanh::lean_ctor_get(v_x_2214_, 0);
                v_vs_2219_ = crate::leanh::lean_ctor_get(v_x_2214_, 1);
                v_isSharedCheck_2244_ = (!crate::leanh::lean_is_exclusive(v_x_2214_)) as u8;
                if v_isSharedCheck_2244_ == 0 {
                    v___x_2221_ = v_x_2214_;
                    v_isShared_2222_ = v_isSharedCheck_2244_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2219_);
                    crate::leanh::lean_inc(v_ks_2218_);
                    crate::leanh::lean_dec(v_x_2214_);
                    v___x_2221_ = crate::leanh::lean_box(0);
                    v_isShared_2222_ = v_isSharedCheck_2244_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2223_ = lean_array_get_size(v_ks_2218_);
                v___x_2224_ = lean_nat_dec_lt(v_x_2215_, v___x_2223_);
                if v___x_2224_ == 0 {
                    crate::leanh::lean_dec(v_x_2215_);
                    crate::leanh::lean_dec_ref(v_inst_2213_);
                    v___x_2225_ = lean_array_push(v_ks_2218_, v_x_2216_);
                    v___x_2226_ = lean_array_push(v_vs_2219_, v_x_2217_);
                    if v_isShared_2222_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2221_, 1, v___x_2226_);
                        crate::leanh::lean_ctor_set(v___x_2221_, 0, v___x_2225_);
                        v___x_2228_ = v___x_2221_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2229_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2225_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2229_, 1, v___x_2226_);
                        v___x_2228_ = v_reuseFailAlloc_2229_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2230_ = lean_array_fget_borrowed(v_ks_2218_, v_x_2215_);
                    crate::leanh::lean_inc_ref(v_inst_2213_);
                    crate::leanh::lean_inc(v_k_x27_2230_);
                    crate::leanh::lean_inc(v_x_2216_);
                    v___x_2231_ =
                        crate::leanh::lean_apply_2(v_inst_2213_, v_x_2216_, v_k_x27_2230_);
                    v___x_2232_ = (crate::leanh::lean_unbox(v___x_2231_) as u8);
                    if v___x_2232_ == 0 {
                        if v_isShared_2222_ == 0 {
                            v___x_2234_ = v___x_2221_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2238_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_ks_2218_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_vs_2219_);
                            v___x_2234_ = v_reuseFailAlloc_2238_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_inst_2213_);
                        v___x_2239_ = lean_array_fset(v_ks_2218_, v_x_2215_, v_x_2216_);
                        v___x_2240_ = lean_array_fset(v_vs_2219_, v_x_2215_, v_x_2217_);
                        crate::leanh::lean_dec(v_x_2215_);
                        if v_isShared_2222_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2221_, 1, v___x_2240_);
                            crate::leanh::lean_ctor_set(v___x_2221_, 0, v___x_2239_);
                            v___x_2242_ = v___x_2221_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2243_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2239_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 1, v___x_2240_);
                            v___x_2242_ = v_reuseFailAlloc_2243_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2228_;
            }
            3 => {
                v___x_2235_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2236_ = lean_nat_add(v_x_2215_, v___x_2235_);
                crate::leanh::lean_dec(v_x_2215_);
                v_x_2214_ = v___x_2234_;
                v_x_2215_ = v___x_2236_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux(
    mut v_00_u03b1_2245_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2246_: *mut crate::leanh::LeanObject,
    mut v_inst_2247_: *mut crate::leanh::LeanObject,
    mut v_x_2248_: *mut crate::leanh::LeanObject,
    mut v_x_2249_: *mut crate::leanh::LeanObject,
    mut v_x_2250_: *mut crate::leanh::LeanObject,
    mut v_x_2251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2252_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(
        v_inst_2247_,
        v_x_2248_,
        v_x_2249_,
        v_x_2250_,
        v_x_2251_,
    );
    return v___x_2252_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(
    mut v_inst_2253_: *mut crate::leanh::LeanObject,
    mut v_n_2254_: *mut crate::leanh::LeanObject,
    mut v_k_2255_: *mut crate::leanh::LeanObject,
    mut v_v_2256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2257_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2258_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(
        v_inst_2253_,
        v_n_2254_,
        v___x_2257_,
        v_k_2255_,
        v_v_2256_,
    );
    return v___x_2258_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode(
    mut v_00_u03b1_2259_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2260_: *mut crate::leanh::LeanObject,
    mut v_inst_2261_: *mut crate::leanh::LeanObject,
    mut v_n_2262_: *mut crate::leanh::LeanObject,
    mut v_k_2263_: *mut crate::leanh::LeanObject,
    mut v_v_2264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2265_ = l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(
        v_inst_2261_,
        v_n_2262_,
        v_k_2263_,
        v_v_2264_,
    );
    return v___x_2265_;
}
pub unsafe fn l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(
    mut v_x_2266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ks_2267_ = crate::leanh::lean_ctor_get(v_x_2266_, 0);
    v___x_2268_ = lean_array_get_size(v_ks_2267_);
    return v___x_2268_;
}
pub unsafe fn l_Lean_PersistentHashMap_getCollisionNodeSize___redArg___boxed(
    mut v_x_2269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2270_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_x_2269_);
    crate::leanh::lean_dec_ref(v_x_2269_);
    return v_res_2270_;
}
pub unsafe fn l_Lean_PersistentHashMap_getCollisionNodeSize(
    mut v_00_u03b1_2271_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2272_: *mut crate::leanh::LeanObject,
    mut v_x_2273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2274_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_x_2273_);
    return v___x_2274_;
}
pub unsafe fn l_Lean_PersistentHashMap_getCollisionNodeSize___boxed(
    mut v_00_u03b1_2275_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2276_: *mut crate::leanh::LeanObject,
    mut v_x_2277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2278_ = l_Lean_PersistentHashMap_getCollisionNodeSize(
        v_00_u03b1_2275_,
        v_00_u03b2_2276_,
        v_x_2277_,
    );
    crate::leanh::lean_dec_ref(v_x_2277_);
    return v_res_2278_;
}
pub unsafe fn l_Lean_PersistentHashMap_mkCollisionNode___redArg(
    mut v_k_u2081_2279_: *mut crate::leanh::LeanObject,
    mut v_v_u2081_2280_: *mut crate::leanh::LeanObject,
    mut v_k_u2082_2281_: *mut crate::leanh::LeanObject,
    mut v_v_u2082_2282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2283_ = crate::leanh::lean_unsigned_to_nat(4);
    v_ks_2284_ = lean_mk_empty_array_with_capacity(v___x_2283_);
    crate::leanh::lean_inc_ref(v_ks_2284_);
    v___x_2285_ = lean_array_push(v_ks_2284_, v_k_u2081_2279_);
    v_ks_2286_ = lean_array_push(v___x_2285_, v_k_u2082_2281_);
    v___x_2287_ = lean_array_push(v_ks_2284_, v_v_u2081_2280_);
    v_vs_2288_ = lean_array_push(v___x_2287_, v_v_u2082_2282_);
    v___x_2289_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2289_, 0, v_ks_2286_);
    crate::leanh::lean_ctor_set(v___x_2289_, 1, v_vs_2288_);
    return v___x_2289_;
}
pub unsafe fn l_Lean_PersistentHashMap_mkCollisionNode(
    mut v_00_u03b1_2290_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2291_: *mut crate::leanh::LeanObject,
    mut v_k_u2081_2292_: *mut crate::leanh::LeanObject,
    mut v_v_u2081_2293_: *mut crate::leanh::LeanObject,
    mut v_k_u2082_2294_: *mut crate::leanh::LeanObject,
    mut v_v_u2082_2295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2296_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
        v_k_u2081_2292_,
        v_v_u2081_2293_,
        v_k_u2082_2294_,
        v_v_u2082_2295_,
    );
    return v___x_2296_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__0() -> usize {
    let mut v___x_2297_: usize = 0;
    let mut v___x_2298_: usize = 0;
    let mut v___x_2299_: usize = 0;
    v___x_2297_ = 5usize;
    v___x_2298_ = 1usize;
    v___x_2299_ = lean_usize_shift_left(v___x_2298_, v___x_2297_);
    return v___x_2299_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1() -> usize {
    let mut v___x_2300_: usize = 0;
    let mut v___x_2301_: usize = 0;
    let mut v___x_2302_: usize = 0;
    v___x_2300_ = 1usize;
    v___x_2301_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___redArg___closed__0_once),
        _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__0,
    );
    v___x_2302_ = lean_usize_sub(v___x_2301_, v___x_2300_);
    return v___x_2302_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2303_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2303_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___redArg(
    mut v_inst_2304_: *mut crate::leanh::LeanObject,
    mut v_inst_2305_: *mut crate::leanh::LeanObject,
    mut v_x_2306_: *mut crate::leanh::LeanObject,
    mut v_x_2307_: usize,
    mut v_x_2308_: usize,
    mut v_x_2309_: *mut crate::leanh::LeanObject,
    mut v_x_2310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: usize = 0;
    let mut v___x_2313_: usize = 0;
    let mut v___x_2314_: usize = 0;
    let mut v___x_2315_: usize = 0;
    let mut v_j_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2321_: u8 = 0;
    let mut v_v_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2335_: u8 = 0;
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: u8 = 0;
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2343_: u8 = 0;
    let mut v_node_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2347_: u8 = 0;
    let mut v___x_2348_: usize = 0;
    let mut v___x_2349_: usize = 0;
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2354_: u8 = 0;
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2356_: u8 = 0;
    let mut v_unused_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2362_: u8 = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2367_: u8 = 0;
    let mut v_ks_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: usize = 0;
    let mut v___x_2374_: u8 = 0;
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut v_reuseFailAlloc_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2306_) == 0 {
                    v_es_2311_ = crate::leanh::lean_ctor_get(v_x_2306_, 0);
                    v___x_2312_ = 5usize;
                    v___x_2313_ = 1usize;
                    v___x_2314_ = crate::leanh::lean_usize_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentHashMap_insertAux___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once
                        ),
                        _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1,
                    );
                    v___x_2315_ = lean_usize_land(v_x_2307_, v___x_2314_);
                    v_j_2316_ = lean_usize_to_nat(v___x_2315_);
                    v___x_2317_ = lean_array_get_size(v_es_2311_);
                    v___x_2318_ = lean_nat_dec_lt(v_j_2316_, v___x_2317_);
                    if v___x_2318_ == 0 {
                        crate::leanh::lean_dec(v_j_2316_);
                        crate::leanh::lean_dec(v_x_2310_);
                        crate::leanh::lean_dec(v_x_2309_);
                        crate::leanh::lean_dec_ref(v_inst_2305_);
                        crate::leanh::lean_dec_ref(v_inst_2304_);
                        return v_x_2306_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2311_);
                        v_isSharedCheck_2356_ = (!crate::leanh::lean_is_exclusive(v_x_2306_)) as u8;
                        if v_isSharedCheck_2356_ == 0 {
                            v_unused_2357_ = crate::leanh::lean_ctor_get(v_x_2306_, 0);
                            crate::leanh::lean_dec(v_unused_2357_);
                            v___x_2320_ = v_x_2306_;
                            v_isShared_2321_ = v_isSharedCheck_2356_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2306_);
                            v___x_2320_ = crate::leanh::lean_box(0);
                            v_isShared_2321_ = v_isSharedCheck_2356_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2358_ = crate::leanh::lean_ctor_get(v_x_2306_, 0);
                    v_vs_2359_ = crate::leanh::lean_ctor_get(v_x_2306_, 1);
                    v_isSharedCheck_2379_ = (!crate::leanh::lean_is_exclusive(v_x_2306_)) as u8;
                    if v_isSharedCheck_2379_ == 0 {
                        v___x_2361_ = v_x_2306_;
                        v_isShared_2362_ = v_isSharedCheck_2379_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2359_);
                        crate::leanh::lean_inc(v_ks_2358_);
                        crate::leanh::lean_dec(v_x_2306_);
                        v___x_2361_ = crate::leanh::lean_box(0);
                        v_isShared_2362_ = v_isSharedCheck_2379_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2322_ = lean_array_fget(v_es_2311_, v_j_2316_);
                v___x_2323_ = crate::leanh::lean_box(0);
                v_xs_x27_2324_ = lean_array_fset(v_es_2311_, v_j_2316_, v___x_2323_);
                match crate::leanh::lean_obj_tag(v_v_2322_) {
                    0 => {
                        crate::leanh::lean_dec_ref(v_inst_2305_);
                        v_key_2331_ = crate::leanh::lean_ctor_get(v_v_2322_, 0);
                        v_val_2332_ = crate::leanh::lean_ctor_get(v_v_2322_, 1);
                        v_isSharedCheck_2343_ = (!crate::leanh::lean_is_exclusive(v_v_2322_)) as u8;
                        if v_isSharedCheck_2343_ == 0 {
                            v___x_2334_ = v_v_2322_;
                            v_isShared_2335_ = v_isSharedCheck_2343_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2332_);
                            crate::leanh::lean_inc(v_key_2331_);
                            crate::leanh::lean_dec(v_v_2322_);
                            v___x_2334_ = crate::leanh::lean_box(0);
                            v_isShared_2335_ = v_isSharedCheck_2343_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2344_ = crate::leanh::lean_ctor_get(v_v_2322_, 0);
                        v_isSharedCheck_2354_ = (!crate::leanh::lean_is_exclusive(v_v_2322_)) as u8;
                        if v_isSharedCheck_2354_ == 0 {
                            v___x_2346_ = v_v_2322_;
                            v_isShared_2347_ = v_isSharedCheck_2354_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2344_);
                            crate::leanh::lean_dec(v_v_2322_);
                            v___x_2346_ = crate::leanh::lean_box(0);
                            v_isShared_2347_ = v_isSharedCheck_2354_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v_inst_2305_);
                        crate::leanh::lean_dec_ref(v_inst_2304_);
                        v___x_2355_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2355_, 0, v_x_2309_);
                        crate::leanh::lean_ctor_set(v___x_2355_, 1, v_x_2310_);
                        v___y_2326_ = v___x_2355_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2327_ = lean_array_fset(v_xs_x27_2324_, v_j_2316_, v___y_2326_);
                crate::leanh::lean_dec(v_j_2316_);
                if v_isShared_2321_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2320_, 0, v___x_2327_);
                    v___x_2329_ = v___x_2320_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
                    v___x_2329_ = v_reuseFailAlloc_2330_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2329_;
            }
            4 => {
                crate::leanh::lean_inc(v_key_2331_);
                crate::leanh::lean_inc(v_x_2309_);
                v___x_2336_ = crate::leanh::lean_apply_2(v_inst_2304_, v_x_2309_, v_key_2331_);
                v___x_2337_ = (crate::leanh::lean_unbox(v___x_2336_) as u8);
                if v___x_2337_ == 0 {
                    crate::leanh::lean_del_object(v___x_2334_);
                    v___x_2338_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2331_,
                        v_val_2332_,
                        v_x_2309_,
                        v_x_2310_,
                    );
                    v___x_2339_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2339_, 0, v___x_2338_);
                    v___y_2326_ = v___x_2339_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2332_);
                    crate::leanh::lean_dec(v_key_2331_);
                    if v_isShared_2335_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2334_, 1, v_x_2310_);
                        crate::leanh::lean_ctor_set(v___x_2334_, 0, v_x_2309_);
                        v___x_2341_ = v___x_2334_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2342_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_x_2309_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_x_2310_);
                        v___x_2341_ = v_reuseFailAlloc_2342_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2326_ = v___x_2341_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2348_ = lean_usize_shift_right(v_x_2307_, v___x_2312_);
                v___x_2349_ = lean_usize_add(v_x_2308_, v___x_2313_);
                v___x_2350_ = l_Lean_PersistentHashMap_insertAux___redArg(
                    v_inst_2304_,
                    v_inst_2305_,
                    v_node_2344_,
                    v___x_2348_,
                    v___x_2349_,
                    v_x_2309_,
                    v_x_2310_,
                );
                if v_isShared_2347_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2346_, 0, v___x_2350_);
                    v___x_2352_ = v___x_2346_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
                    v___x_2352_ = v_reuseFailAlloc_2353_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2326_ = v___x_2352_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2362_ == 0 {
                    v___x_2364_ = v___x_2361_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2378_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_ks_2358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2378_, 1, v_vs_2359_);
                    v___x_2364_ = v_reuseFailAlloc_2378_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_inc_ref(v_inst_2304_);
                v_newNode_2365_ = l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(
                    v_inst_2304_,
                    v___x_2364_,
                    v_x_2309_,
                    v_x_2310_,
                );
                v___x_2373_ = 7usize;
                v___x_2374_ = lean_usize_dec_le(v___x_2373_, v_x_2308_);
                if v___x_2374_ == 0 {
                    v___x_2375_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2365_);
                    v___x_2376_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2377_ = lean_nat_dec_lt(v___x_2375_, v___x_2376_);
                    crate::leanh::lean_dec(v___x_2375_);
                    v___y_2367_ = v___x_2377_;
                    state = 10;
                    continue;
                } else {
                    v___y_2367_ = v___x_2374_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2367_ == 0 {
                    v_ks_2368_ = crate::leanh::lean_ctor_get(v_newNode_2365_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2368_);
                    v_vs_2369_ = crate::leanh::lean_ctor_get(v_newNode_2365_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2369_);
                    crate::leanh::lean_dec_ref(v_newNode_2365_);
                    v___x_2370_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2371_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentHashMap_insertAux___redArg___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentHashMap_insertAux___redArg___closed__2_once
                        ),
                        _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__2,
                    );
                    v___x_2372_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_2304_, v_inst_2305_, v_x_2308_, v_ks_2368_, v_vs_2369_, v___x_2370_, v___x_2371_);
                    crate::leanh::lean_dec_ref(v_vs_2369_);
                    crate::leanh::lean_dec_ref(v_ks_2368_);
                    return v___x_2372_;
                } else {
                    crate::leanh::lean_dec_ref(v_inst_2305_);
                    crate::leanh::lean_dec_ref(v_inst_2304_);
                    return v_newNode_2365_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(
    mut v_inst_2380_: *mut crate::leanh::LeanObject,
    mut v_inst_2381_: *mut crate::leanh::LeanObject,
    mut v_depth_2382_: usize,
    mut v_keys_2383_: *mut crate::leanh::LeanObject,
    mut v_vals_2384_: *mut crate::leanh::LeanObject,
    mut v_i_2385_: *mut crate::leanh::LeanObject,
    mut v_entries_2386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: u8 = 0;
    let mut v_k_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: u64 = 0;
    let mut v_h_2393_: usize = 0;
    let mut v___x_2394_: usize = 0;
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: usize = 0;
    let mut v___x_2397_: usize = 0;
    let mut v___x_2398_: usize = 0;
    let mut v_h_2399_: usize = 0;
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2387_ = lean_array_get_size(v_keys_2383_);
                v___x_2388_ = lean_nat_dec_lt(v_i_2385_, v___x_2387_);
                if v___x_2388_ == 0 {
                    crate::leanh::lean_dec(v_i_2385_);
                    crate::leanh::lean_dec_ref(v_inst_2381_);
                    crate::leanh::lean_dec_ref(v_inst_2380_);
                    return v_entries_2386_;
                } else {
                    v_k_2389_ = lean_array_fget_borrowed(v_keys_2383_, v_i_2385_);
                    v_v_2390_ = lean_array_fget_borrowed(v_vals_2384_, v_i_2385_);
                    crate::leanh::lean_inc_ref_n(v_inst_2381_, 2);
                    crate::leanh::lean_inc_n(v_k_2389_, 2);
                    v___x_2391_ = crate::leanh::lean_apply_1(v_inst_2381_, v_k_2389_);
                    v___x_2392_ = crate::leanh::lean_unbox_uint64(v___x_2391_);
                    crate::leanh::lean_dec_ref(v___x_2391_);
                    v_h_2393_ = lean_uint64_to_usize(v___x_2392_);
                    v___x_2394_ = 5usize;
                    v___x_2395_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2396_ = 1usize;
                    v___x_2397_ = lean_usize_sub(v_depth_2382_, v___x_2396_);
                    v___x_2398_ = lean_usize_mul(v___x_2394_, v___x_2397_);
                    v_h_2399_ = lean_usize_shift_right(v_h_2393_, v___x_2398_);
                    v___x_2400_ = lean_nat_add(v_i_2385_, v___x_2395_);
                    crate::leanh::lean_dec(v_i_2385_);
                    crate::leanh::lean_inc(v_v_2390_);
                    crate::leanh::lean_inc_ref(v_inst_2380_);
                    v___x_2401_ = l_Lean_PersistentHashMap_insertAux___redArg(
                        v_inst_2380_,
                        v_inst_2381_,
                        v_entries_2386_,
                        v_h_2399_,
                        v_depth_2382_,
                        v_k_2389_,
                        v_v_2390_,
                    );
                    v_i_2385_ = v___x_2400_;
                    v_entries_2386_ = v___x_2401_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg___boxed(
    mut v_inst_2403_: *mut crate::leanh::LeanObject,
    mut v_inst_2404_: *mut crate::leanh::LeanObject,
    mut v_depth_2405_: *mut crate::leanh::LeanObject,
    mut v_keys_2406_: *mut crate::leanh::LeanObject,
    mut v_vals_2407_: *mut crate::leanh::LeanObject,
    mut v_i_2408_: *mut crate::leanh::LeanObject,
    mut v_entries_2409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2410_: usize = 0;
    let mut v_res_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2410_ = crate::leanh::lean_unbox_usize(v_depth_2405_);
    crate::leanh::lean_dec(v_depth_2405_);
    v_res_2411_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_2403_, v_inst_2404_, v_depth_boxed_2410_, v_keys_2406_, v_vals_2407_, v_i_2408_, v_entries_2409_);
    crate::leanh::lean_dec_ref(v_vals_2407_);
    crate::leanh::lean_dec_ref(v_keys_2406_);
    return v_res_2411_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___redArg___boxed(
    mut v_inst_2412_: *mut crate::leanh::LeanObject,
    mut v_inst_2413_: *mut crate::leanh::LeanObject,
    mut v_x_2414_: *mut crate::leanh::LeanObject,
    mut v_x_2415_: *mut crate::leanh::LeanObject,
    mut v_x_2416_: *mut crate::leanh::LeanObject,
    mut v_x_2417_: *mut crate::leanh::LeanObject,
    mut v_x_2418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_475__boxed_2419_: usize = 0;
    let mut v_x_476__boxed_2420_: usize = 0;
    let mut v_res_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_475__boxed_2419_ = crate::leanh::lean_unbox_usize(v_x_2415_);
    crate::leanh::lean_dec(v_x_2415_);
    v_x_476__boxed_2420_ = crate::leanh::lean_unbox_usize(v_x_2416_);
    crate::leanh::lean_dec(v_x_2416_);
    v_res_2421_ = l_Lean_PersistentHashMap_insertAux___redArg(
        v_inst_2412_,
        v_inst_2413_,
        v_x_2414_,
        v_x_475__boxed_2419_,
        v_x_476__boxed_2420_,
        v_x_2417_,
        v_x_2418_,
    );
    return v_res_2421_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(
    mut v_00_u03b1_2422_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2423_: *mut crate::leanh::LeanObject,
    mut v_inst_2424_: *mut crate::leanh::LeanObject,
    mut v_inst_2425_: *mut crate::leanh::LeanObject,
    mut v_depth_2426_: usize,
    mut v_keys_2427_: *mut crate::leanh::LeanObject,
    mut v_vals_2428_: *mut crate::leanh::LeanObject,
    mut v_heq_2429_: *mut crate::leanh::LeanObject,
    mut v_i_2430_: *mut crate::leanh::LeanObject,
    mut v_entries_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2432_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_2424_, v_inst_2425_, v_depth_2426_, v_keys_2427_, v_vals_2428_, v_i_2430_, v_entries_2431_);
    return v___x_2432_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___boxed(
    mut v_00_u03b1_2433_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2434_: *mut crate::leanh::LeanObject,
    mut v_inst_2435_: *mut crate::leanh::LeanObject,
    mut v_inst_2436_: *mut crate::leanh::LeanObject,
    mut v_depth_2437_: *mut crate::leanh::LeanObject,
    mut v_keys_2438_: *mut crate::leanh::LeanObject,
    mut v_vals_2439_: *mut crate::leanh::LeanObject,
    mut v_heq_2440_: *mut crate::leanh::LeanObject,
    mut v_i_2441_: *mut crate::leanh::LeanObject,
    mut v_entries_2442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2443_: usize = 0;
    let mut v_res_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2443_ = crate::leanh::lean_unbox_usize(v_depth_2437_);
    crate::leanh::lean_dec(v_depth_2437_);
    v_res_2444_ =
        l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(
            v_00_u03b1_2433_,
            v_00_u03b2_2434_,
            v_inst_2435_,
            v_inst_2436_,
            v_depth_boxed_2443_,
            v_keys_2438_,
            v_vals_2439_,
            v_heq_2440_,
            v_i_2441_,
            v_entries_2442_,
        );
    crate::leanh::lean_dec_ref(v_vals_2439_);
    crate::leanh::lean_dec_ref(v_keys_2438_);
    return v_res_2444_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux(
    mut v_00_u03b1_2445_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2446_: *mut crate::leanh::LeanObject,
    mut v_inst_2447_: *mut crate::leanh::LeanObject,
    mut v_inst_2448_: *mut crate::leanh::LeanObject,
    mut v_x_2449_: *mut crate::leanh::LeanObject,
    mut v_x_2450_: usize,
    mut v_x_2451_: usize,
    mut v_x_2452_: *mut crate::leanh::LeanObject,
    mut v_x_2453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2454_ = l_Lean_PersistentHashMap_insertAux___redArg(
        v_inst_2447_,
        v_inst_2448_,
        v_x_2449_,
        v_x_2450_,
        v_x_2451_,
        v_x_2452_,
        v_x_2453_,
    );
    return v___x_2454_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___boxed(
    mut v_00_u03b1_2455_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2456_: *mut crate::leanh::LeanObject,
    mut v_inst_2457_: *mut crate::leanh::LeanObject,
    mut v_inst_2458_: *mut crate::leanh::LeanObject,
    mut v_x_2459_: *mut crate::leanh::LeanObject,
    mut v_x_2460_: *mut crate::leanh::LeanObject,
    mut v_x_2461_: *mut crate::leanh::LeanObject,
    mut v_x_2462_: *mut crate::leanh::LeanObject,
    mut v_x_2463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_659__boxed_2464_: usize = 0;
    let mut v_x_660__boxed_2465_: usize = 0;
    let mut v_res_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_659__boxed_2464_ = crate::leanh::lean_unbox_usize(v_x_2460_);
    crate::leanh::lean_dec(v_x_2460_);
    v_x_660__boxed_2465_ = crate::leanh::lean_unbox_usize(v_x_2461_);
    crate::leanh::lean_dec(v_x_2461_);
    v_res_2466_ = l_Lean_PersistentHashMap_insertAux(
        v_00_u03b1_2455_,
        v_00_u03b2_2456_,
        v_inst_2457_,
        v_inst_2458_,
        v_x_2459_,
        v_x_659__boxed_2464_,
        v_x_660__boxed_2465_,
        v_x_2462_,
        v_x_2463_,
    );
    return v_res_2466_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___redArg(
    mut v_x_2467_: *mut crate::leanh::LeanObject,
    mut v_x_2468_: *mut crate::leanh::LeanObject,
    mut v_x_2469_: *mut crate::leanh::LeanObject,
    mut v_x_2470_: *mut crate::leanh::LeanObject,
    mut v_x_2471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: u64 = 0;
    let mut v___x_2474_: usize = 0;
    let mut v___x_2475_: usize = 0;
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_x_2468_);
    crate::leanh::lean_inc(v_x_2470_);
    v___x_2472_ = crate::leanh::lean_apply_1(v_x_2468_, v_x_2470_);
    v___x_2473_ = crate::leanh::lean_unbox_uint64(v___x_2472_);
    crate::leanh::lean_dec_ref(v___x_2472_);
    v___x_2474_ = lean_uint64_to_usize(v___x_2473_);
    v___x_2475_ = 1usize;
    v___x_2476_ = l_Lean_PersistentHashMap_insertAux___redArg(
        v_x_2467_,
        v_x_2468_,
        v_x_2469_,
        v___x_2474_,
        v___x_2475_,
        v_x_2470_,
        v_x_2471_,
    );
    return v___x_2476_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert(
    mut v_00_u03b1_2477_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2478_: *mut crate::leanh::LeanObject,
    mut v_x_2479_: *mut crate::leanh::LeanObject,
    mut v_x_2480_: *mut crate::leanh::LeanObject,
    mut v_x_2481_: *mut crate::leanh::LeanObject,
    mut v_x_2482_: *mut crate::leanh::LeanObject,
    mut v_x_2483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2484_ = l_Lean_PersistentHashMap_insert___redArg(
        v_x_2479_, v_x_2480_, v_x_2481_, v_x_2482_, v_x_2483_,
    );
    return v___x_2484_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___redArg(
    mut v_inst_2485_: *mut crate::leanh::LeanObject,
    mut v_keys_2486_: *mut crate::leanh::LeanObject,
    mut v_vals_2487_: *mut crate::leanh::LeanObject,
    mut v_i_2488_: *mut crate::leanh::LeanObject,
    mut v_k_2489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: u8 = 0;
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2490_ = lean_array_get_size(v_keys_2486_);
                v___x_2491_ = lean_nat_dec_lt(v_i_2488_, v___x_2490_);
                if v___x_2491_ == 0 {
                    crate::leanh::lean_dec(v_k_2489_);
                    crate::leanh::lean_dec(v_i_2488_);
                    crate::leanh::lean_dec_ref(v_inst_2485_);
                    v___x_2492_ = crate::leanh::lean_box(0);
                    return v___x_2492_;
                } else {
                    v_k_x27_2493_ = lean_array_fget_borrowed(v_keys_2486_, v_i_2488_);
                    crate::leanh::lean_inc_ref(v_inst_2485_);
                    crate::leanh::lean_inc(v_k_x27_2493_);
                    crate::leanh::lean_inc(v_k_2489_);
                    v___x_2494_ =
                        crate::leanh::lean_apply_2(v_inst_2485_, v_k_2489_, v_k_x27_2493_);
                    v___x_2495_ = (crate::leanh::lean_unbox(v___x_2494_) as u8);
                    if v___x_2495_ == 0 {
                        v___x_2496_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2497_ = lean_nat_add(v_i_2488_, v___x_2496_);
                        crate::leanh::lean_dec(v_i_2488_);
                        v_i_2488_ = v___x_2497_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_k_2489_);
                        crate::leanh::lean_dec_ref(v_inst_2485_);
                        v___x_2499_ = lean_array_fget_borrowed(v_vals_2487_, v_i_2488_);
                        crate::leanh::lean_dec(v_i_2488_);
                        crate::leanh::lean_inc(v___x_2499_);
                        v___x_2500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2500_, 0, v___x_2499_);
                        return v___x_2500_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___redArg___boxed(
    mut v_inst_2501_: *mut crate::leanh::LeanObject,
    mut v_keys_2502_: *mut crate::leanh::LeanObject,
    mut v_vals_2503_: *mut crate::leanh::LeanObject,
    mut v_i_2504_: *mut crate::leanh::LeanObject,
    mut v_k_2505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2506_ = l_Lean_PersistentHashMap_findAtAux___redArg(
        v_inst_2501_,
        v_keys_2502_,
        v_vals_2503_,
        v_i_2504_,
        v_k_2505_,
    );
    crate::leanh::lean_dec_ref(v_vals_2503_);
    crate::leanh::lean_dec_ref(v_keys_2502_);
    return v_res_2506_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux(
    mut v_00_u03b1_2507_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2508_: *mut crate::leanh::LeanObject,
    mut v_inst_2509_: *mut crate::leanh::LeanObject,
    mut v_keys_2510_: *mut crate::leanh::LeanObject,
    mut v_vals_2511_: *mut crate::leanh::LeanObject,
    mut v_heq_2512_: *mut crate::leanh::LeanObject,
    mut v_i_2513_: *mut crate::leanh::LeanObject,
    mut v_k_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2515_ = l_Lean_PersistentHashMap_findAtAux___redArg(
        v_inst_2509_,
        v_keys_2510_,
        v_vals_2511_,
        v_i_2513_,
        v_k_2514_,
    );
    return v___x_2515_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___boxed(
    mut v_00_u03b1_2516_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2517_: *mut crate::leanh::LeanObject,
    mut v_inst_2518_: *mut crate::leanh::LeanObject,
    mut v_keys_2519_: *mut crate::leanh::LeanObject,
    mut v_vals_2520_: *mut crate::leanh::LeanObject,
    mut v_heq_2521_: *mut crate::leanh::LeanObject,
    mut v_i_2522_: *mut crate::leanh::LeanObject,
    mut v_k_2523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2524_ = l_Lean_PersistentHashMap_findAtAux(
        v_00_u03b1_2516_,
        v_00_u03b2_2517_,
        v_inst_2518_,
        v_keys_2519_,
        v_vals_2520_,
        v_heq_2521_,
        v_i_2522_,
        v_k_2523_,
    );
    crate::leanh::lean_dec_ref(v_vals_2520_);
    crate::leanh::lean_dec_ref(v_keys_2519_);
    return v_res_2524_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___redArg(
    mut v_inst_2525_: *mut crate::leanh::LeanObject,
    mut v_x_2526_: *mut crate::leanh::LeanObject,
    mut v_x_2527_: usize,
    mut v_x_2528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: usize = 0;
    let mut v___x_2532_: usize = 0;
    let mut v___x_2533_: usize = 0;
    let mut v_j_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: usize = 0;
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2526_) == 0 {
                    v_es_2529_ = crate::leanh::lean_ctor_get(v_x_2526_, 0);
                    crate::leanh::lean_inc_ref(v_es_2529_);
                    crate::leanh::lean_dec_ref_known(v_x_2526_, 1);
                    v___x_2530_ = crate::leanh::lean_box(2);
                    v___x_2531_ = 5usize;
                    v___x_2532_ = crate::leanh::lean_usize_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentHashMap_insertAux___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once
                        ),
                        _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1,
                    );
                    v___x_2533_ = lean_usize_land(v_x_2527_, v___x_2532_);
                    v_j_2534_ = lean_usize_to_nat(v___x_2533_);
                    v___x_2535_ = lean_array_get(v___x_2530_, v_es_2529_, v_j_2534_);
                    crate::leanh::lean_dec(v_j_2534_);
                    crate::leanh::lean_dec_ref(v_es_2529_);
                    match crate::leanh::lean_obj_tag(v___x_2535_) {
                        0 => {
                            v_key_2536_ = crate::leanh::lean_ctor_get(v___x_2535_, 0);
                            crate::leanh::lean_inc(v_key_2536_);
                            v_val_2537_ = crate::leanh::lean_ctor_get(v___x_2535_, 1);
                            crate::leanh::lean_inc(v_val_2537_);
                            crate::leanh::lean_dec_ref_known(v___x_2535_, 2);
                            v___x_2538_ =
                                crate::leanh::lean_apply_2(v_inst_2525_, v_x_2528_, v_key_2536_);
                            v___x_2539_ = (crate::leanh::lean_unbox(v___x_2538_) as u8);
                            if v___x_2539_ == 0 {
                                crate::leanh::lean_dec(v_val_2537_);
                                v___x_2540_ = crate::leanh::lean_box(0);
                                return v___x_2540_;
                            } else {
                                v___x_2541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2541_, 0, v_val_2537_);
                                return v___x_2541_;
                            }
                        }
                        1 => {
                            v_node_2542_ = crate::leanh::lean_ctor_get(v___x_2535_, 0);
                            crate::leanh::lean_inc(v_node_2542_);
                            crate::leanh::lean_dec_ref_known(v___x_2535_, 1);
                            v___x_2543_ = lean_usize_shift_right(v_x_2527_, v___x_2531_);
                            v_x_2526_ = v_node_2542_;
                            v_x_2527_ = v___x_2543_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_x_2528_);
                            crate::leanh::lean_dec_ref(v_inst_2525_);
                            v___x_2545_ = crate::leanh::lean_box(0);
                            return v___x_2545_;
                        }
                    }
                } else {
                    v_ks_2546_ = crate::leanh::lean_ctor_get(v_x_2526_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2546_);
                    v_vs_2547_ = crate::leanh::lean_ctor_get(v_x_2526_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2547_);
                    crate::leanh::lean_dec_ref_known(v_x_2526_, 2);
                    v___x_2548_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2549_ = l_Lean_PersistentHashMap_findAtAux___redArg(
                        v_inst_2525_,
                        v_ks_2546_,
                        v_vs_2547_,
                        v___x_2548_,
                        v_x_2528_,
                    );
                    crate::leanh::lean_dec_ref(v_vs_2547_);
                    crate::leanh::lean_dec_ref(v_ks_2546_);
                    return v___x_2549_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___redArg___boxed(
    mut v_inst_2550_: *mut crate::leanh::LeanObject,
    mut v_x_2551_: *mut crate::leanh::LeanObject,
    mut v_x_2552_: *mut crate::leanh::LeanObject,
    mut v_x_2553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_151__boxed_2554_: usize = 0;
    let mut v_res_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_151__boxed_2554_ = crate::leanh::lean_unbox_usize(v_x_2552_);
    crate::leanh::lean_dec(v_x_2552_);
    v_res_2555_ = l_Lean_PersistentHashMap_findAux___redArg(
        v_inst_2550_,
        v_x_2551_,
        v_x_151__boxed_2554_,
        v_x_2553_,
    );
    return v_res_2555_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux(
    mut v_00_u03b1_2556_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2557_: *mut crate::leanh::LeanObject,
    mut v_inst_2558_: *mut crate::leanh::LeanObject,
    mut v_x_2559_: *mut crate::leanh::LeanObject,
    mut v_x_2560_: usize,
    mut v_x_2561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_x_2559_);
    v___x_2562_ =
        l_Lean_PersistentHashMap_findAux___redArg(v_inst_2558_, v_x_2559_, v_x_2560_, v_x_2561_);
    return v___x_2562_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___boxed(
    mut v_00_u03b1_2563_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2564_: *mut crate::leanh::LeanObject,
    mut v_inst_2565_: *mut crate::leanh::LeanObject,
    mut v_x_2566_: *mut crate::leanh::LeanObject,
    mut v_x_2567_: *mut crate::leanh::LeanObject,
    mut v_x_2568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_205__boxed_2569_: usize = 0;
    let mut v_res_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_205__boxed_2569_ = crate::leanh::lean_unbox_usize(v_x_2567_);
    crate::leanh::lean_dec(v_x_2567_);
    v_res_2570_ = l_Lean_PersistentHashMap_findAux(
        v_00_u03b1_2563_,
        v_00_u03b2_2564_,
        v_inst_2565_,
        v_x_2566_,
        v_x_205__boxed_2569_,
        v_x_2568_,
    );
    crate::leanh::lean_dec_ref(v_x_2566_);
    return v_res_2570_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___redArg(
    mut v_x_2571_: *mut crate::leanh::LeanObject,
    mut v_x_2572_: *mut crate::leanh::LeanObject,
    mut v_x_2573_: *mut crate::leanh::LeanObject,
    mut v_x_2574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: u64 = 0;
    let mut v___x_2577_: usize = 0;
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_x_2574_);
    v___x_2575_ = crate::leanh::lean_apply_1(v_x_2572_, v_x_2574_);
    v___x_2576_ = crate::leanh::lean_unbox_uint64(v___x_2575_);
    crate::leanh::lean_dec_ref(v___x_2575_);
    v___x_2577_ = lean_uint64_to_usize(v___x_2576_);
    crate::leanh::lean_inc_ref(v_x_2573_);
    v___x_2578_ =
        l_Lean_PersistentHashMap_findAux___redArg(v_x_2571_, v_x_2573_, v___x_2577_, v_x_2574_);
    return v___x_2578_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___redArg___boxed(
    mut v_x_2579_: *mut crate::leanh::LeanObject,
    mut v_x_2580_: *mut crate::leanh::LeanObject,
    mut v_x_2581_: *mut crate::leanh::LeanObject,
    mut v_x_2582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2583_ =
        l_Lean_PersistentHashMap_find_x3f___redArg(v_x_2579_, v_x_2580_, v_x_2581_, v_x_2582_);
    crate::leanh::lean_dec_ref(v_x_2581_);
    return v_res_2583_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f(
    mut v_00_u03b1_2584_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2585_: *mut crate::leanh::LeanObject,
    mut v_x_2586_: *mut crate::leanh::LeanObject,
    mut v_x_2587_: *mut crate::leanh::LeanObject,
    mut v_x_2588_: *mut crate::leanh::LeanObject,
    mut v_x_2589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2590_ =
        l_Lean_PersistentHashMap_find_x3f___redArg(v_x_2586_, v_x_2587_, v_x_2588_, v_x_2589_);
    return v___x_2590_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___boxed(
    mut v_00_u03b1_2591_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2592_: *mut crate::leanh::LeanObject,
    mut v_x_2593_: *mut crate::leanh::LeanObject,
    mut v_x_2594_: *mut crate::leanh::LeanObject,
    mut v_x_2595_: *mut crate::leanh::LeanObject,
    mut v_x_2596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2597_ = l_Lean_PersistentHashMap_find_x3f(
        v_00_u03b1_2591_,
        v_00_u03b2_2592_,
        v_x_2593_,
        v_x_2594_,
        v_x_2595_,
        v_x_2596_,
    );
    crate::leanh::lean_dec_ref(v_x_2595_);
    return v_res_2597_;
}
pub unsafe fn l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(
    mut v_x_2598_: *mut crate::leanh::LeanObject,
    mut v_x_2599_: *mut crate::leanh::LeanObject,
    mut v_m_2600_: *mut crate::leanh::LeanObject,
    mut v_i_2601_: *mut crate::leanh::LeanObject,
    mut v_x_2602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2603_ =
        l_Lean_PersistentHashMap_find_x3f___redArg(v_x_2598_, v_x_2599_, v_m_2600_, v_i_2601_);
    return v___x_2603_;
}
pub unsafe fn l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed(
    mut v_x_2604_: *mut crate::leanh::LeanObject,
    mut v_x_2605_: *mut crate::leanh::LeanObject,
    mut v_m_2606_: *mut crate::leanh::LeanObject,
    mut v_i_2607_: *mut crate::leanh::LeanObject,
    mut v_x_2608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2609_ = l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(
        v_x_2604_, v_x_2605_, v_m_2606_, v_i_2607_, v_x_2608_,
    );
    crate::leanh::lean_dec_ref(v_m_2606_);
    return v_res_2609_;
}
pub unsafe fn l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg(
    mut v_x_2610_: *mut crate::leanh::LeanObject,
    mut v_x_2611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2612_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2612_, 0, v_x_2610_);
    crate::leanh::lean_closure_set(v___f_2612_, 1, v_x_2611_);
    return v___f_2612_;
}
pub unsafe fn l_Lean_PersistentHashMap_instGetElemOptionTrue(
    mut v_00_u03b1_2613_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2614_: *mut crate::leanh::LeanObject,
    mut v_x_2615_: *mut crate::leanh::LeanObject,
    mut v_x_2616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2617_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2617_, 0, v_x_2615_);
    crate::leanh::lean_closure_set(v___f_2617_, 1, v_x_2616_);
    return v___f_2617_;
}
pub unsafe fn l_Lean_PersistentHashMap_findD___redArg(
    mut v_x_2618_: *mut crate::leanh::LeanObject,
    mut v_x_2619_: *mut crate::leanh::LeanObject,
    mut v_m_2620_: *mut crate::leanh::LeanObject,
    mut v_a_2621_: *mut crate::leanh::LeanObject,
    mut v_b_u2080_2622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2623_ =
        l_Lean_PersistentHashMap_find_x3f___redArg(v_x_2618_, v_x_2619_, v_m_2620_, v_a_2621_);
    if crate::leanh::lean_obj_tag(v___x_2623_) == 0 {
        crate::leanh::lean_inc(v_b_u2080_2622_);
        return v_b_u2080_2622_;
    } else {
        let mut v_val_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2624_ = crate::leanh::lean_ctor_get(v___x_2623_, 0);
        crate::leanh::lean_inc(v_val_2624_);
        crate::leanh::lean_dec_ref_known(v___x_2623_, 1);
        return v_val_2624_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findD___redArg___boxed(
    mut v_x_2625_: *mut crate::leanh::LeanObject,
    mut v_x_2626_: *mut crate::leanh::LeanObject,
    mut v_m_2627_: *mut crate::leanh::LeanObject,
    mut v_a_2628_: *mut crate::leanh::LeanObject,
    mut v_b_u2080_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2630_ = l_Lean_PersistentHashMap_findD___redArg(
        v_x_2625_,
        v_x_2626_,
        v_m_2627_,
        v_a_2628_,
        v_b_u2080_2629_,
    );
    crate::leanh::lean_dec(v_b_u2080_2629_);
    crate::leanh::lean_dec_ref(v_m_2627_);
    return v_res_2630_;
}
pub unsafe fn l_Lean_PersistentHashMap_findD(
    mut v_00_u03b1_2631_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2632_: *mut crate::leanh::LeanObject,
    mut v_x_2633_: *mut crate::leanh::LeanObject,
    mut v_x_2634_: *mut crate::leanh::LeanObject,
    mut v_m_2635_: *mut crate::leanh::LeanObject,
    mut v_a_2636_: *mut crate::leanh::LeanObject,
    mut v_b_u2080_2637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2638_ =
        l_Lean_PersistentHashMap_find_x3f___redArg(v_x_2633_, v_x_2634_, v_m_2635_, v_a_2636_);
    if crate::leanh::lean_obj_tag(v___x_2638_) == 0 {
        crate::leanh::lean_inc(v_b_u2080_2637_);
        return v_b_u2080_2637_;
    } else {
        let mut v_val_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2639_ = crate::leanh::lean_ctor_get(v___x_2638_, 0);
        crate::leanh::lean_inc(v_val_2639_);
        crate::leanh::lean_dec_ref_known(v___x_2638_, 1);
        return v_val_2639_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findD___boxed(
    mut v_00_u03b1_2640_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2641_: *mut crate::leanh::LeanObject,
    mut v_x_2642_: *mut crate::leanh::LeanObject,
    mut v_x_2643_: *mut crate::leanh::LeanObject,
    mut v_m_2644_: *mut crate::leanh::LeanObject,
    mut v_a_2645_: *mut crate::leanh::LeanObject,
    mut v_b_u2080_2646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2647_ = l_Lean_PersistentHashMap_findD(
        v_00_u03b1_2640_,
        v_00_u03b2_2641_,
        v_x_2642_,
        v_x_2643_,
        v_m_2644_,
        v_a_2645_,
        v_b_u2080_2646_,
    );
    crate::leanh::lean_dec(v_b_u2080_2646_);
    crate::leanh::lean_dec_ref(v_m_2644_);
    return v_res_2647_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2651_ = l_Lean_PersistentHashMap_find_x21___redArg___closed__2;
    v___x_2652_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_2653_ = crate::leanh::lean_unsigned_to_nat(177);
    v___x_2654_ = l_Lean_PersistentHashMap_find_x21___redArg___closed__1;
    v___x_2655_ = l_Lean_PersistentHashMap_find_x21___redArg___closed__0;
    v___x_2656_ = l_mkPanicMessageWithDecl(
        v___x_2655_,
        v___x_2654_,
        v___x_2653_,
        v___x_2652_,
        v___x_2651_,
    );
    return v___x_2656_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x21___redArg(
    mut v_x_2657_: *mut crate::leanh::LeanObject,
    mut v_x_2658_: *mut crate::leanh::LeanObject,
    mut v_inst_2659_: *mut crate::leanh::LeanObject,
    mut v_m_2660_: *mut crate::leanh::LeanObject,
    mut v_a_2661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2662_ =
        l_Lean_PersistentHashMap_find_x3f___redArg(v_x_2657_, v_x_2658_, v_m_2660_, v_a_2661_);
    if crate::leanh::lean_obj_tag(v___x_2662_) == 0 {
        let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2663_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once),
            _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3,
        );
        v___x_2664_ = l_panic___redArg(v_inst_2659_, v___x_2663_);
        return v___x_2664_;
    } else {
        let mut v_val_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2665_ = crate::leanh::lean_ctor_get(v___x_2662_, 0);
        crate::leanh::lean_inc(v_val_2665_);
        crate::leanh::lean_dec_ref_known(v___x_2662_, 1);
        return v_val_2665_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x21___redArg___boxed(
    mut v_x_2666_: *mut crate::leanh::LeanObject,
    mut v_x_2667_: *mut crate::leanh::LeanObject,
    mut v_inst_2668_: *mut crate::leanh::LeanObject,
    mut v_m_2669_: *mut crate::leanh::LeanObject,
    mut v_a_2670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2671_ = l_Lean_PersistentHashMap_find_x21___redArg(
        v_x_2666_,
        v_x_2667_,
        v_inst_2668_,
        v_m_2669_,
        v_a_2670_,
    );
    crate::leanh::lean_dec_ref(v_m_2669_);
    crate::leanh::lean_dec(v_inst_2668_);
    return v_res_2671_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x21(
    mut v_00_u03b1_2672_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2673_: *mut crate::leanh::LeanObject,
    mut v_x_2674_: *mut crate::leanh::LeanObject,
    mut v_x_2675_: *mut crate::leanh::LeanObject,
    mut v_inst_2676_: *mut crate::leanh::LeanObject,
    mut v_m_2677_: *mut crate::leanh::LeanObject,
    mut v_a_2678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2679_ =
        l_Lean_PersistentHashMap_find_x3f___redArg(v_x_2674_, v_x_2675_, v_m_2677_, v_a_2678_);
    if crate::leanh::lean_obj_tag(v___x_2679_) == 0 {
        let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2680_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once),
            _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3,
        );
        v___x_2681_ = l_panic___redArg(v_inst_2676_, v___x_2680_);
        return v___x_2681_;
    } else {
        let mut v_val_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2682_ = crate::leanh::lean_ctor_get(v___x_2679_, 0);
        crate::leanh::lean_inc(v_val_2682_);
        crate::leanh::lean_dec_ref_known(v___x_2679_, 1);
        return v_val_2682_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x21___boxed(
    mut v_00_u03b1_2683_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2684_: *mut crate::leanh::LeanObject,
    mut v_x_2685_: *mut crate::leanh::LeanObject,
    mut v_x_2686_: *mut crate::leanh::LeanObject,
    mut v_inst_2687_: *mut crate::leanh::LeanObject,
    mut v_m_2688_: *mut crate::leanh::LeanObject,
    mut v_a_2689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2690_ = l_Lean_PersistentHashMap_find_x21(
        v_00_u03b1_2683_,
        v_00_u03b2_2684_,
        v_x_2685_,
        v_x_2686_,
        v_inst_2687_,
        v_m_2688_,
        v_a_2689_,
    );
    crate::leanh::lean_dec_ref(v_m_2688_);
    crate::leanh::lean_dec(v_inst_2687_);
    return v_res_2690_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___redArg(
    mut v_inst_2691_: *mut crate::leanh::LeanObject,
    mut v_keys_2692_: *mut crate::leanh::LeanObject,
    mut v_vals_2693_: *mut crate::leanh::LeanObject,
    mut v_i_2694_: *mut crate::leanh::LeanObject,
    mut v_k_2695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: u8 = 0;
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: u8 = 0;
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2696_ = lean_array_get_size(v_keys_2692_);
                v___x_2697_ = lean_nat_dec_lt(v_i_2694_, v___x_2696_);
                if v___x_2697_ == 0 {
                    crate::leanh::lean_dec(v_k_2695_);
                    crate::leanh::lean_dec(v_i_2694_);
                    crate::leanh::lean_dec_ref(v_inst_2691_);
                    v___x_2698_ = crate::leanh::lean_box(0);
                    return v___x_2698_;
                } else {
                    v_k_x27_2699_ = lean_array_fget_borrowed(v_keys_2692_, v_i_2694_);
                    crate::leanh::lean_inc_ref(v_inst_2691_);
                    crate::leanh::lean_inc(v_k_x27_2699_);
                    crate::leanh::lean_inc(v_k_2695_);
                    v___x_2700_ =
                        crate::leanh::lean_apply_2(v_inst_2691_, v_k_2695_, v_k_x27_2699_);
                    v___x_2701_ = (crate::leanh::lean_unbox(v___x_2700_) as u8);
                    if v___x_2701_ == 0 {
                        v___x_2702_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2703_ = lean_nat_add(v_i_2694_, v___x_2702_);
                        crate::leanh::lean_dec(v_i_2694_);
                        v_i_2694_ = v___x_2703_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_k_2695_);
                        crate::leanh::lean_dec_ref(v_inst_2691_);
                        v___x_2705_ = lean_array_fget_borrowed(v_vals_2693_, v_i_2694_);
                        crate::leanh::lean_dec(v_i_2694_);
                        crate::leanh::lean_inc(v___x_2705_);
                        crate::leanh::lean_inc(v_k_x27_2699_);
                        v___x_2706_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2706_, 0, v_k_x27_2699_);
                        crate::leanh::lean_ctor_set(v___x_2706_, 1, v___x_2705_);
                        v___x_2707_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2707_, 0, v___x_2706_);
                        return v___x_2707_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___redArg___boxed(
    mut v_inst_2708_: *mut crate::leanh::LeanObject,
    mut v_keys_2709_: *mut crate::leanh::LeanObject,
    mut v_vals_2710_: *mut crate::leanh::LeanObject,
    mut v_i_2711_: *mut crate::leanh::LeanObject,
    mut v_k_2712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2713_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(
        v_inst_2708_,
        v_keys_2709_,
        v_vals_2710_,
        v_i_2711_,
        v_k_2712_,
    );
    crate::leanh::lean_dec_ref(v_vals_2710_);
    crate::leanh::lean_dec_ref(v_keys_2709_);
    return v_res_2713_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux(
    mut v_00_u03b1_2714_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2715_: *mut crate::leanh::LeanObject,
    mut v_inst_2716_: *mut crate::leanh::LeanObject,
    mut v_keys_2717_: *mut crate::leanh::LeanObject,
    mut v_vals_2718_: *mut crate::leanh::LeanObject,
    mut v_heq_2719_: *mut crate::leanh::LeanObject,
    mut v_i_2720_: *mut crate::leanh::LeanObject,
    mut v_k_2721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2722_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(
        v_inst_2716_,
        v_keys_2717_,
        v_vals_2718_,
        v_i_2720_,
        v_k_2721_,
    );
    return v___x_2722_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___boxed(
    mut v_00_u03b1_2723_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2724_: *mut crate::leanh::LeanObject,
    mut v_inst_2725_: *mut crate::leanh::LeanObject,
    mut v_keys_2726_: *mut crate::leanh::LeanObject,
    mut v_vals_2727_: *mut crate::leanh::LeanObject,
    mut v_heq_2728_: *mut crate::leanh::LeanObject,
    mut v_i_2729_: *mut crate::leanh::LeanObject,
    mut v_k_2730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2731_ = l_Lean_PersistentHashMap_findEntryAtAux(
        v_00_u03b1_2723_,
        v_00_u03b2_2724_,
        v_inst_2725_,
        v_keys_2726_,
        v_vals_2727_,
        v_heq_2728_,
        v_i_2729_,
        v_k_2730_,
    );
    crate::leanh::lean_dec_ref(v_vals_2727_);
    crate::leanh::lean_dec_ref(v_keys_2726_);
    return v_res_2731_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___redArg(
    mut v_inst_2732_: *mut crate::leanh::LeanObject,
    mut v_x_2733_: *mut crate::leanh::LeanObject,
    mut v_x_2734_: usize,
    mut v_x_2735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: usize = 0;
    let mut v___x_2739_: usize = 0;
    let mut v___x_2740_: usize = 0;
    let mut v_j_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: u8 = 0;
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: usize = 0;
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2733_) == 0 {
                    v_es_2736_ = crate::leanh::lean_ctor_get(v_x_2733_, 0);
                    crate::leanh::lean_inc_ref(v_es_2736_);
                    crate::leanh::lean_dec_ref_known(v_x_2733_, 1);
                    v___x_2737_ = crate::leanh::lean_box(2);
                    v___x_2738_ = 5usize;
                    v___x_2739_ = crate::leanh::lean_usize_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentHashMap_insertAux___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once
                        ),
                        _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1,
                    );
                    v___x_2740_ = lean_usize_land(v_x_2734_, v___x_2739_);
                    v_j_2741_ = lean_usize_to_nat(v___x_2740_);
                    v___x_2742_ = lean_array_get(v___x_2737_, v_es_2736_, v_j_2741_);
                    crate::leanh::lean_dec(v_j_2741_);
                    crate::leanh::lean_dec_ref(v_es_2736_);
                    match crate::leanh::lean_obj_tag(v___x_2742_) {
                        0 => {
                            v_key_2743_ = crate::leanh::lean_ctor_get(v___x_2742_, 0);
                            crate::leanh::lean_inc_n(v_key_2743_, 2);
                            v_val_2744_ = crate::leanh::lean_ctor_get(v___x_2742_, 1);
                            crate::leanh::lean_inc(v_val_2744_);
                            crate::leanh::lean_dec_ref_known(v___x_2742_, 2);
                            v___x_2745_ =
                                crate::leanh::lean_apply_2(v_inst_2732_, v_x_2735_, v_key_2743_);
                            v___x_2746_ = (crate::leanh::lean_unbox(v___x_2745_) as u8);
                            if v___x_2746_ == 0 {
                                crate::leanh::lean_dec(v_val_2744_);
                                crate::leanh::lean_dec(v_key_2743_);
                                v___x_2747_ = crate::leanh::lean_box(0);
                                return v___x_2747_;
                            } else {
                                v___x_2748_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2748_, 0, v_key_2743_);
                                crate::leanh::lean_ctor_set(v___x_2748_, 1, v_val_2744_);
                                v___x_2749_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2749_, 0, v___x_2748_);
                                return v___x_2749_;
                            }
                        }
                        1 => {
                            v_node_2750_ = crate::leanh::lean_ctor_get(v___x_2742_, 0);
                            crate::leanh::lean_inc(v_node_2750_);
                            crate::leanh::lean_dec_ref_known(v___x_2742_, 1);
                            v___x_2751_ = lean_usize_shift_right(v_x_2734_, v___x_2738_);
                            v_x_2733_ = v_node_2750_;
                            v_x_2734_ = v___x_2751_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_x_2735_);
                            crate::leanh::lean_dec_ref(v_inst_2732_);
                            v___x_2753_ = crate::leanh::lean_box(0);
                            return v___x_2753_;
                        }
                    }
                } else {
                    v_ks_2754_ = crate::leanh::lean_ctor_get(v_x_2733_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2754_);
                    v_vs_2755_ = crate::leanh::lean_ctor_get(v_x_2733_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2755_);
                    crate::leanh::lean_dec_ref_known(v_x_2733_, 2);
                    v___x_2756_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2757_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(
                        v_inst_2732_,
                        v_ks_2754_,
                        v_vs_2755_,
                        v___x_2756_,
                        v_x_2735_,
                    );
                    crate::leanh::lean_dec_ref(v_vs_2755_);
                    crate::leanh::lean_dec_ref(v_ks_2754_);
                    return v___x_2757_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___redArg___boxed(
    mut v_inst_2758_: *mut crate::leanh::LeanObject,
    mut v_x_2759_: *mut crate::leanh::LeanObject,
    mut v_x_2760_: *mut crate::leanh::LeanObject,
    mut v_x_2761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_155__boxed_2762_: usize = 0;
    let mut v_res_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_155__boxed_2762_ = crate::leanh::lean_unbox_usize(v_x_2760_);
    crate::leanh::lean_dec(v_x_2760_);
    v_res_2763_ = l_Lean_PersistentHashMap_findEntryAux___redArg(
        v_inst_2758_,
        v_x_2759_,
        v_x_155__boxed_2762_,
        v_x_2761_,
    );
    return v_res_2763_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux(
    mut v_00_u03b1_2764_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2765_: *mut crate::leanh::LeanObject,
    mut v_inst_2766_: *mut crate::leanh::LeanObject,
    mut v_x_2767_: *mut crate::leanh::LeanObject,
    mut v_x_2768_: usize,
    mut v_x_2769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_x_2767_);
    v___x_2770_ = l_Lean_PersistentHashMap_findEntryAux___redArg(
        v_inst_2766_,
        v_x_2767_,
        v_x_2768_,
        v_x_2769_,
    );
    return v___x_2770_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___boxed(
    mut v_00_u03b1_2771_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2772_: *mut crate::leanh::LeanObject,
    mut v_inst_2773_: *mut crate::leanh::LeanObject,
    mut v_x_2774_: *mut crate::leanh::LeanObject,
    mut v_x_2775_: *mut crate::leanh::LeanObject,
    mut v_x_2776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_211__boxed_2777_: usize = 0;
    let mut v_res_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_211__boxed_2777_ = crate::leanh::lean_unbox_usize(v_x_2775_);
    crate::leanh::lean_dec(v_x_2775_);
    v_res_2778_ = l_Lean_PersistentHashMap_findEntryAux(
        v_00_u03b1_2771_,
        v_00_u03b2_2772_,
        v_inst_2773_,
        v_x_2774_,
        v_x_211__boxed_2777_,
        v_x_2776_,
    );
    crate::leanh::lean_dec_ref(v_x_2774_);
    return v_res_2778_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___redArg(
    mut v_x_2779_: *mut crate::leanh::LeanObject,
    mut v_x_2780_: *mut crate::leanh::LeanObject,
    mut v_x_2781_: *mut crate::leanh::LeanObject,
    mut v_x_2782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: u64 = 0;
    let mut v___x_2785_: usize = 0;
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_x_2782_);
    v___x_2783_ = crate::leanh::lean_apply_1(v_x_2780_, v_x_2782_);
    v___x_2784_ = crate::leanh::lean_unbox_uint64(v___x_2783_);
    crate::leanh::lean_dec_ref(v___x_2783_);
    v___x_2785_ = lean_uint64_to_usize(v___x_2784_);
    crate::leanh::lean_inc_ref(v_x_2781_);
    v___x_2786_ = l_Lean_PersistentHashMap_findEntryAux___redArg(
        v_x_2779_,
        v_x_2781_,
        v___x_2785_,
        v_x_2782_,
    );
    return v___x_2786_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___redArg___boxed(
    mut v_x_2787_: *mut crate::leanh::LeanObject,
    mut v_x_2788_: *mut crate::leanh::LeanObject,
    mut v_x_2789_: *mut crate::leanh::LeanObject,
    mut v_x_2790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2791_ =
        l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_2787_, v_x_2788_, v_x_2789_, v_x_2790_);
    crate::leanh::lean_dec_ref(v_x_2789_);
    return v_res_2791_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f(
    mut v_00_u03b1_2792_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2793_: *mut crate::leanh::LeanObject,
    mut v_x_2794_: *mut crate::leanh::LeanObject,
    mut v_x_2795_: *mut crate::leanh::LeanObject,
    mut v_x_2796_: *mut crate::leanh::LeanObject,
    mut v_x_2797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2798_ =
        l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_2794_, v_x_2795_, v_x_2796_, v_x_2797_);
    return v___x_2798_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___boxed(
    mut v_00_u03b1_2799_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2800_: *mut crate::leanh::LeanObject,
    mut v_x_2801_: *mut crate::leanh::LeanObject,
    mut v_x_2802_: *mut crate::leanh::LeanObject,
    mut v_x_2803_: *mut crate::leanh::LeanObject,
    mut v_x_2804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2805_ = l_Lean_PersistentHashMap_findEntry_x3f(
        v_00_u03b1_2799_,
        v_00_u03b2_2800_,
        v_x_2801_,
        v_x_2802_,
        v_x_2803_,
        v_x_2804_,
    );
    crate::leanh::lean_dec_ref(v_x_2803_);
    return v_res_2805_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___redArg(
    mut v_inst_2806_: *mut crate::leanh::LeanObject,
    mut v_keys_2807_: *mut crate::leanh::LeanObject,
    mut v_i_2808_: *mut crate::leanh::LeanObject,
    mut v_k_2809_: *mut crate::leanh::LeanObject,
    mut v_k_u2080_2810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: u8 = 0;
    let mut v_k_x27_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2811_ = lean_array_get_size(v_keys_2807_);
                v___x_2812_ = lean_nat_dec_lt(v_i_2808_, v___x_2811_);
                if v___x_2812_ == 0 {
                    crate::leanh::lean_dec(v_k_2809_);
                    crate::leanh::lean_dec(v_i_2808_);
                    crate::leanh::lean_dec_ref(v_inst_2806_);
                    crate::leanh::lean_inc(v_k_u2080_2810_);
                    return v_k_u2080_2810_;
                } else {
                    v_k_x27_2813_ = lean_array_fget_borrowed(v_keys_2807_, v_i_2808_);
                    crate::leanh::lean_inc_ref(v_inst_2806_);
                    crate::leanh::lean_inc(v_k_x27_2813_);
                    crate::leanh::lean_inc(v_k_2809_);
                    v___x_2814_ =
                        crate::leanh::lean_apply_2(v_inst_2806_, v_k_2809_, v_k_x27_2813_);
                    v___x_2815_ = (crate::leanh::lean_unbox(v___x_2814_) as u8);
                    if v___x_2815_ == 0 {
                        v___x_2816_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2817_ = lean_nat_add(v_i_2808_, v___x_2816_);
                        crate::leanh::lean_dec(v_i_2808_);
                        v_i_2808_ = v___x_2817_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_k_2809_);
                        crate::leanh::lean_dec(v_i_2808_);
                        crate::leanh::lean_dec_ref(v_inst_2806_);
                        crate::leanh::lean_inc(v_k_x27_2813_);
                        return v_k_x27_2813_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___redArg___boxed(
    mut v_inst_2819_: *mut crate::leanh::LeanObject,
    mut v_keys_2820_: *mut crate::leanh::LeanObject,
    mut v_i_2821_: *mut crate::leanh::LeanObject,
    mut v_k_2822_: *mut crate::leanh::LeanObject,
    mut v_k_u2080_2823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2824_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(
        v_inst_2819_,
        v_keys_2820_,
        v_i_2821_,
        v_k_2822_,
        v_k_u2080_2823_,
    );
    crate::leanh::lean_dec(v_k_u2080_2823_);
    crate::leanh::lean_dec_ref(v_keys_2820_);
    return v_res_2824_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux(
    mut v_00_u03b1_2825_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2826_: *mut crate::leanh::LeanObject,
    mut v_inst_2827_: *mut crate::leanh::LeanObject,
    mut v_keys_2828_: *mut crate::leanh::LeanObject,
    mut v_vals_2829_: *mut crate::leanh::LeanObject,
    mut v_heq_2830_: *mut crate::leanh::LeanObject,
    mut v_i_2831_: *mut crate::leanh::LeanObject,
    mut v_k_2832_: *mut crate::leanh::LeanObject,
    mut v_k_u2080_2833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2834_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(
        v_inst_2827_,
        v_keys_2828_,
        v_i_2831_,
        v_k_2832_,
        v_k_u2080_2833_,
    );
    return v___x_2834_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___boxed(
    mut v_00_u03b1_2835_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2836_: *mut crate::leanh::LeanObject,
    mut v_inst_2837_: *mut crate::leanh::LeanObject,
    mut v_keys_2838_: *mut crate::leanh::LeanObject,
    mut v_vals_2839_: *mut crate::leanh::LeanObject,
    mut v_heq_2840_: *mut crate::leanh::LeanObject,
    mut v_i_2841_: *mut crate::leanh::LeanObject,
    mut v_k_2842_: *mut crate::leanh::LeanObject,
    mut v_k_u2080_2843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2844_ = l_Lean_PersistentHashMap_findKeyDAtAux(
        v_00_u03b1_2835_,
        v_00_u03b2_2836_,
        v_inst_2837_,
        v_keys_2838_,
        v_vals_2839_,
        v_heq_2840_,
        v_i_2841_,
        v_k_2842_,
        v_k_u2080_2843_,
    );
    crate::leanh::lean_dec(v_k_u2080_2843_);
    crate::leanh::lean_dec_ref(v_vals_2839_);
    crate::leanh::lean_dec_ref(v_keys_2838_);
    return v_res_2844_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___redArg(
    mut v_inst_2845_: *mut crate::leanh::LeanObject,
    mut v_x_2846_: *mut crate::leanh::LeanObject,
    mut v_x_2847_: usize,
    mut v_x_2848_: *mut crate::leanh::LeanObject,
    mut v_x_2849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: usize = 0;
    let mut v___x_2853_: usize = 0;
    let mut v___x_2854_: usize = 0;
    let mut v_j_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: u8 = 0;
    let mut v_node_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: usize = 0;
    let mut v_ks_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2846_) == 0 {
                    v_es_2850_ = crate::leanh::lean_ctor_get(v_x_2846_, 0);
                    crate::leanh::lean_inc_ref(v_es_2850_);
                    crate::leanh::lean_dec_ref_known(v_x_2846_, 1);
                    v___x_2851_ = crate::leanh::lean_box(2);
                    v___x_2852_ = 5usize;
                    v___x_2853_ = crate::leanh::lean_usize_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentHashMap_insertAux___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once
                        ),
                        _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1,
                    );
                    v___x_2854_ = lean_usize_land(v_x_2847_, v___x_2853_);
                    v_j_2855_ = lean_usize_to_nat(v___x_2854_);
                    v___x_2856_ = lean_array_get(v___x_2851_, v_es_2850_, v_j_2855_);
                    crate::leanh::lean_dec(v_j_2855_);
                    crate::leanh::lean_dec_ref(v_es_2850_);
                    match crate::leanh::lean_obj_tag(v___x_2856_) {
                        0 => {
                            v_key_2857_ = crate::leanh::lean_ctor_get(v___x_2856_, 0);
                            crate::leanh::lean_inc_n(v_key_2857_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_2856_, 2);
                            v___x_2858_ =
                                crate::leanh::lean_apply_2(v_inst_2845_, v_x_2848_, v_key_2857_);
                            v___x_2859_ = (crate::leanh::lean_unbox(v___x_2858_) as u8);
                            if v___x_2859_ == 0 {
                                crate::leanh::lean_dec(v_key_2857_);
                                crate::leanh::lean_inc(v_x_2849_);
                                return v_x_2849_;
                            } else {
                                return v_key_2857_;
                            }
                        }
                        1 => {
                            v_node_2860_ = crate::leanh::lean_ctor_get(v___x_2856_, 0);
                            crate::leanh::lean_inc(v_node_2860_);
                            crate::leanh::lean_dec_ref_known(v___x_2856_, 1);
                            v___x_2861_ = lean_usize_shift_right(v_x_2847_, v___x_2852_);
                            v_x_2846_ = v_node_2860_;
                            v_x_2847_ = v___x_2861_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_x_2848_);
                            crate::leanh::lean_dec_ref(v_inst_2845_);
                            crate::leanh::lean_inc(v_x_2849_);
                            return v_x_2849_;
                        }
                    }
                } else {
                    v_ks_2863_ = crate::leanh::lean_ctor_get(v_x_2846_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2863_);
                    crate::leanh::lean_dec_ref_known(v_x_2846_, 2);
                    v___x_2864_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2865_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(
                        v_inst_2845_,
                        v_ks_2863_,
                        v___x_2864_,
                        v_x_2848_,
                        v_x_2849_,
                    );
                    crate::leanh::lean_dec_ref(v_ks_2863_);
                    return v___x_2865_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___redArg___boxed(
    mut v_inst_2866_: *mut crate::leanh::LeanObject,
    mut v_x_2867_: *mut crate::leanh::LeanObject,
    mut v_x_2868_: *mut crate::leanh::LeanObject,
    mut v_x_2869_: *mut crate::leanh::LeanObject,
    mut v_x_2870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_140__boxed_2871_: usize = 0;
    let mut v_res_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_140__boxed_2871_ = crate::leanh::lean_unbox_usize(v_x_2868_);
    crate::leanh::lean_dec(v_x_2868_);
    v_res_2872_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(
        v_inst_2866_,
        v_x_2867_,
        v_x_140__boxed_2871_,
        v_x_2869_,
        v_x_2870_,
    );
    crate::leanh::lean_dec(v_x_2870_);
    return v_res_2872_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux(
    mut v_00_u03b1_2873_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2874_: *mut crate::leanh::LeanObject,
    mut v_inst_2875_: *mut crate::leanh::LeanObject,
    mut v_x_2876_: *mut crate::leanh::LeanObject,
    mut v_x_2877_: usize,
    mut v_x_2878_: *mut crate::leanh::LeanObject,
    mut v_x_2879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2880_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(
        v_inst_2875_,
        v_x_2876_,
        v_x_2877_,
        v_x_2878_,
        v_x_2879_,
    );
    return v___x_2880_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___boxed(
    mut v_00_u03b1_2881_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2882_: *mut crate::leanh::LeanObject,
    mut v_inst_2883_: *mut crate::leanh::LeanObject,
    mut v_x_2884_: *mut crate::leanh::LeanObject,
    mut v_x_2885_: *mut crate::leanh::LeanObject,
    mut v_x_2886_: *mut crate::leanh::LeanObject,
    mut v_x_2887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_189__boxed_2888_: usize = 0;
    let mut v_res_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_189__boxed_2888_ = crate::leanh::lean_unbox_usize(v_x_2885_);
    crate::leanh::lean_dec(v_x_2885_);
    v_res_2889_ = l_Lean_PersistentHashMap_findKeyDAux(
        v_00_u03b1_2881_,
        v_00_u03b2_2882_,
        v_inst_2883_,
        v_x_2884_,
        v_x_189__boxed_2888_,
        v_x_2886_,
        v_x_2887_,
    );
    crate::leanh::lean_dec(v_x_2887_);
    return v_res_2889_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyD___redArg(
    mut v_x_2890_: *mut crate::leanh::LeanObject,
    mut v_x_2891_: *mut crate::leanh::LeanObject,
    mut v_m_2892_: *mut crate::leanh::LeanObject,
    mut v_a_2893_: *mut crate::leanh::LeanObject,
    mut v_a_u2080_2894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: u64 = 0;
    let mut v___x_2897_: usize = 0;
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2893_);
    v___x_2895_ = crate::leanh::lean_apply_1(v_x_2891_, v_a_2893_);
    v___x_2896_ = crate::leanh::lean_unbox_uint64(v___x_2895_);
    crate::leanh::lean_dec_ref(v___x_2895_);
    v___x_2897_ = lean_uint64_to_usize(v___x_2896_);
    v___x_2898_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(
        v_x_2890_,
        v_m_2892_,
        v___x_2897_,
        v_a_2893_,
        v_a_u2080_2894_,
    );
    return v___x_2898_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyD___redArg___boxed(
    mut v_x_2899_: *mut crate::leanh::LeanObject,
    mut v_x_2900_: *mut crate::leanh::LeanObject,
    mut v_m_2901_: *mut crate::leanh::LeanObject,
    mut v_a_2902_: *mut crate::leanh::LeanObject,
    mut v_a_u2080_2903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2904_ = l_Lean_PersistentHashMap_findKeyD___redArg(
        v_x_2899_,
        v_x_2900_,
        v_m_2901_,
        v_a_2902_,
        v_a_u2080_2903_,
    );
    crate::leanh::lean_dec(v_a_u2080_2903_);
    return v_res_2904_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyD(
    mut v_00_u03b1_2905_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2906_: *mut crate::leanh::LeanObject,
    mut v_x_2907_: *mut crate::leanh::LeanObject,
    mut v_x_2908_: *mut crate::leanh::LeanObject,
    mut v_m_2909_: *mut crate::leanh::LeanObject,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
    mut v_a_u2080_2911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: u64 = 0;
    let mut v___x_2914_: usize = 0;
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2910_);
    v___x_2912_ = crate::leanh::lean_apply_1(v_x_2908_, v_a_2910_);
    v___x_2913_ = crate::leanh::lean_unbox_uint64(v___x_2912_);
    crate::leanh::lean_dec_ref(v___x_2912_);
    v___x_2914_ = lean_uint64_to_usize(v___x_2913_);
    v___x_2915_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(
        v_x_2907_,
        v_m_2909_,
        v___x_2914_,
        v_a_2910_,
        v_a_u2080_2911_,
    );
    return v___x_2915_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyD___boxed(
    mut v_00_u03b1_2916_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2917_: *mut crate::leanh::LeanObject,
    mut v_x_2918_: *mut crate::leanh::LeanObject,
    mut v_x_2919_: *mut crate::leanh::LeanObject,
    mut v_m_2920_: *mut crate::leanh::LeanObject,
    mut v_a_2921_: *mut crate::leanh::LeanObject,
    mut v_a_u2080_2922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2923_ = l_Lean_PersistentHashMap_findKeyD(
        v_00_u03b1_2916_,
        v_00_u03b2_2917_,
        v_x_2918_,
        v_x_2919_,
        v_m_2920_,
        v_a_2921_,
        v_a_u2080_2922_,
    );
    crate::leanh::lean_dec(v_a_u2080_2922_);
    return v_res_2923_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___redArg(
    mut v_inst_2924_: *mut crate::leanh::LeanObject,
    mut v_keys_2925_: *mut crate::leanh::LeanObject,
    mut v_i_2926_: *mut crate::leanh::LeanObject,
    mut v_k_2927_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: u8 = 0;
    let mut v_k_x27_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: u8 = 0;
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2928_ = lean_array_get_size(v_keys_2925_);
                v___x_2929_ = lean_nat_dec_lt(v_i_2926_, v___x_2928_);
                if v___x_2929_ == 0 {
                    crate::leanh::lean_dec(v_k_2927_);
                    crate::leanh::lean_dec(v_i_2926_);
                    crate::leanh::lean_dec_ref(v_inst_2924_);
                    return v___x_2929_;
                } else {
                    v_k_x27_2930_ = lean_array_fget_borrowed(v_keys_2925_, v_i_2926_);
                    crate::leanh::lean_inc_ref(v_inst_2924_);
                    crate::leanh::lean_inc(v_k_x27_2930_);
                    crate::leanh::lean_inc(v_k_2927_);
                    v___x_2931_ =
                        crate::leanh::lean_apply_2(v_inst_2924_, v_k_2927_, v_k_x27_2930_);
                    v___x_2932_ = (crate::leanh::lean_unbox(v___x_2931_) as u8);
                    if v___x_2932_ == 0 {
                        v___x_2933_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2934_ = lean_nat_add(v_i_2926_, v___x_2933_);
                        crate::leanh::lean_dec(v_i_2926_);
                        v_i_2926_ = v___x_2934_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_k_2927_);
                        crate::leanh::lean_dec(v_i_2926_);
                        crate::leanh::lean_dec_ref(v_inst_2924_);
                        v___x_2936_ = (crate::leanh::lean_unbox(v___x_2931_) as u8);
                        return v___x_2936_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___redArg___boxed(
    mut v_inst_2937_: *mut crate::leanh::LeanObject,
    mut v_keys_2938_: *mut crate::leanh::LeanObject,
    mut v_i_2939_: *mut crate::leanh::LeanObject,
    mut v_k_2940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2941_: u8 = 0;
    let mut v_r_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2941_ = l_Lean_PersistentHashMap_containsAtAux___redArg(
        v_inst_2937_,
        v_keys_2938_,
        v_i_2939_,
        v_k_2940_,
    );
    crate::leanh::lean_dec_ref(v_keys_2938_);
    v_r_2942_ = crate::leanh::lean_box((v_res_2941_) as usize);
    return v_r_2942_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux(
    mut v_00_u03b1_2943_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2944_: *mut crate::leanh::LeanObject,
    mut v_inst_2945_: *mut crate::leanh::LeanObject,
    mut v_keys_2946_: *mut crate::leanh::LeanObject,
    mut v_vals_2947_: *mut crate::leanh::LeanObject,
    mut v_heq_2948_: *mut crate::leanh::LeanObject,
    mut v_i_2949_: *mut crate::leanh::LeanObject,
    mut v_k_2950_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2951_: u8 = 0;
    v___x_2951_ = l_Lean_PersistentHashMap_containsAtAux___redArg(
        v_inst_2945_,
        v_keys_2946_,
        v_i_2949_,
        v_k_2950_,
    );
    return v___x_2951_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___boxed(
    mut v_00_u03b1_2952_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2953_: *mut crate::leanh::LeanObject,
    mut v_inst_2954_: *mut crate::leanh::LeanObject,
    mut v_keys_2955_: *mut crate::leanh::LeanObject,
    mut v_vals_2956_: *mut crate::leanh::LeanObject,
    mut v_heq_2957_: *mut crate::leanh::LeanObject,
    mut v_i_2958_: *mut crate::leanh::LeanObject,
    mut v_k_2959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2960_: u8 = 0;
    let mut v_r_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2960_ = l_Lean_PersistentHashMap_containsAtAux(
        v_00_u03b1_2952_,
        v_00_u03b2_2953_,
        v_inst_2954_,
        v_keys_2955_,
        v_vals_2956_,
        v_heq_2957_,
        v_i_2958_,
        v_k_2959_,
    );
    crate::leanh::lean_dec_ref(v_vals_2956_);
    crate::leanh::lean_dec_ref(v_keys_2955_);
    v_r_2961_ = crate::leanh::lean_box((v_res_2960_) as usize);
    return v_r_2961_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___redArg(
    mut v_inst_2962_: *mut crate::leanh::LeanObject,
    mut v_x_2963_: *mut crate::leanh::LeanObject,
    mut v_x_2964_: usize,
    mut v_x_2965_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: usize = 0;
    let mut v___x_2969_: usize = 0;
    let mut v___x_2970_: usize = 0;
    let mut v_j_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: u8 = 0;
    let mut v_node_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: usize = 0;
    let mut v___x_2979_: u8 = 0;
    let mut v_ks_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2963_) == 0 {
                    v_es_2966_ = crate::leanh::lean_ctor_get(v_x_2963_, 0);
                    crate::leanh::lean_inc_ref(v_es_2966_);
                    crate::leanh::lean_dec_ref_known(v_x_2963_, 1);
                    v___x_2967_ = crate::leanh::lean_box(2);
                    v___x_2968_ = 5usize;
                    v___x_2969_ = crate::leanh::lean_usize_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentHashMap_insertAux___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once
                        ),
                        _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1,
                    );
                    v___x_2970_ = lean_usize_land(v_x_2964_, v___x_2969_);
                    v_j_2971_ = lean_usize_to_nat(v___x_2970_);
                    v___x_2972_ = lean_array_get(v___x_2967_, v_es_2966_, v_j_2971_);
                    crate::leanh::lean_dec(v_j_2971_);
                    crate::leanh::lean_dec_ref(v_es_2966_);
                    match crate::leanh::lean_obj_tag(v___x_2972_) {
                        0 => {
                            v_key_2973_ = crate::leanh::lean_ctor_get(v___x_2972_, 0);
                            crate::leanh::lean_inc(v_key_2973_);
                            crate::leanh::lean_dec_ref_known(v___x_2972_, 2);
                            v___x_2974_ =
                                crate::leanh::lean_apply_2(v_inst_2962_, v_x_2965_, v_key_2973_);
                            v___x_2975_ = (crate::leanh::lean_unbox(v___x_2974_) as u8);
                            return v___x_2975_;
                        }
                        1 => {
                            v_node_2976_ = crate::leanh::lean_ctor_get(v___x_2972_, 0);
                            crate::leanh::lean_inc(v_node_2976_);
                            crate::leanh::lean_dec_ref_known(v___x_2972_, 1);
                            v___x_2977_ = lean_usize_shift_right(v_x_2964_, v___x_2968_);
                            v_x_2963_ = v_node_2976_;
                            v_x_2964_ = v___x_2977_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_x_2965_);
                            crate::leanh::lean_dec_ref(v_inst_2962_);
                            v___x_2979_ = 0;
                            return v___x_2979_;
                        }
                    }
                } else {
                    v_ks_2980_ = crate::leanh::lean_ctor_get(v_x_2963_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2980_);
                    crate::leanh::lean_dec_ref_known(v_x_2963_, 2);
                    v___x_2981_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2982_ = l_Lean_PersistentHashMap_containsAtAux___redArg(
                        v_inst_2962_,
                        v_ks_2980_,
                        v___x_2981_,
                        v_x_2965_,
                    );
                    crate::leanh::lean_dec_ref(v_ks_2980_);
                    return v___x_2982_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___redArg___boxed(
    mut v_inst_2983_: *mut crate::leanh::LeanObject,
    mut v_x_2984_: *mut crate::leanh::LeanObject,
    mut v_x_2985_: *mut crate::leanh::LeanObject,
    mut v_x_2986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_110__boxed_2987_: usize = 0;
    let mut v_res_2988_: u8 = 0;
    let mut v_r_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_110__boxed_2987_ = crate::leanh::lean_unbox_usize(v_x_2985_);
    crate::leanh::lean_dec(v_x_2985_);
    v_res_2988_ = l_Lean_PersistentHashMap_containsAux___redArg(
        v_inst_2983_,
        v_x_2984_,
        v_x_110__boxed_2987_,
        v_x_2986_,
    );
    v_r_2989_ = crate::leanh::lean_box((v_res_2988_) as usize);
    return v_r_2989_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux(
    mut v_00_u03b1_2990_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2991_: *mut crate::leanh::LeanObject,
    mut v_inst_2992_: *mut crate::leanh::LeanObject,
    mut v_x_2993_: *mut crate::leanh::LeanObject,
    mut v_x_2994_: usize,
    mut v_x_2995_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2996_: u8 = 0;
    v___x_2996_ = l_Lean_PersistentHashMap_containsAux___redArg(
        v_inst_2992_,
        v_x_2993_,
        v_x_2994_,
        v_x_2995_,
    );
    return v___x_2996_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___boxed(
    mut v_00_u03b1_2997_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2998_: *mut crate::leanh::LeanObject,
    mut v_inst_2999_: *mut crate::leanh::LeanObject,
    mut v_x_3000_: *mut crate::leanh::LeanObject,
    mut v_x_3001_: *mut crate::leanh::LeanObject,
    mut v_x_3002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_158__boxed_3003_: usize = 0;
    let mut v_res_3004_: u8 = 0;
    let mut v_r_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_158__boxed_3003_ = crate::leanh::lean_unbox_usize(v_x_3001_);
    crate::leanh::lean_dec(v_x_3001_);
    v_res_3004_ = l_Lean_PersistentHashMap_containsAux(
        v_00_u03b1_2997_,
        v_00_u03b2_2998_,
        v_inst_2999_,
        v_x_3000_,
        v_x_158__boxed_3003_,
        v_x_3002_,
    );
    v_r_3005_ = crate::leanh::lean_box((v_res_3004_) as usize);
    return v_r_3005_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___redArg(
    mut v_inst_3006_: *mut crate::leanh::LeanObject,
    mut v_inst_3007_: *mut crate::leanh::LeanObject,
    mut v_x_3008_: *mut crate::leanh::LeanObject,
    mut v_x_3009_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: u64 = 0;
    let mut v___x_3012_: usize = 0;
    let mut v___x_3013_: u8 = 0;
    crate::leanh::lean_inc(v_x_3009_);
    v___x_3010_ = crate::leanh::lean_apply_1(v_inst_3007_, v_x_3009_);
    v___x_3011_ = crate::leanh::lean_unbox_uint64(v___x_3010_);
    crate::leanh::lean_dec_ref(v___x_3010_);
    v___x_3012_ = lean_uint64_to_usize(v___x_3011_);
    v___x_3013_ = l_Lean_PersistentHashMap_containsAux___redArg(
        v_inst_3006_,
        v_x_3008_,
        v___x_3012_,
        v_x_3009_,
    );
    return v___x_3013_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___redArg___boxed(
    mut v_inst_3014_: *mut crate::leanh::LeanObject,
    mut v_inst_3015_: *mut crate::leanh::LeanObject,
    mut v_x_3016_: *mut crate::leanh::LeanObject,
    mut v_x_3017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3018_: u8 = 0;
    let mut v_r_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3018_ = l_Lean_PersistentHashMap_contains___redArg(
        v_inst_3014_,
        v_inst_3015_,
        v_x_3016_,
        v_x_3017_,
    );
    v_r_3019_ = crate::leanh::lean_box((v_res_3018_) as usize);
    return v_r_3019_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains(
    mut v_00_u03b1_3020_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3021_: *mut crate::leanh::LeanObject,
    mut v_inst_3022_: *mut crate::leanh::LeanObject,
    mut v_inst_3023_: *mut crate::leanh::LeanObject,
    mut v_x_3024_: *mut crate::leanh::LeanObject,
    mut v_x_3025_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3026_: u8 = 0;
    v___x_3026_ = l_Lean_PersistentHashMap_contains___redArg(
        v_inst_3022_,
        v_inst_3023_,
        v_x_3024_,
        v_x_3025_,
    );
    return v___x_3026_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___boxed(
    mut v_00_u03b1_3027_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3028_: *mut crate::leanh::LeanObject,
    mut v_inst_3029_: *mut crate::leanh::LeanObject,
    mut v_inst_3030_: *mut crate::leanh::LeanObject,
    mut v_x_3031_: *mut crate::leanh::LeanObject,
    mut v_x_3032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3033_: u8 = 0;
    let mut v_r_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3033_ = l_Lean_PersistentHashMap_contains(
        v_00_u03b1_3027_,
        v_00_u03b2_3028_,
        v_inst_3029_,
        v_inst_3030_,
        v_x_3031_,
        v_x_3032_,
    );
    v_r_3034_ = crate::leanh::lean_box((v_res_3033_) as usize);
    return v_r_3034_;
}
pub unsafe fn l_Lean_PersistentHashMap_isUnaryEntries___redArg(
    mut v_a_3035_: *mut crate::leanh::LeanObject,
    mut v_i_3036_: *mut crate::leanh::LeanObject,
    mut v_acc_3037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3045_: u8 = 0;
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3053_: u8 = 0;
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3038_ = lean_array_get_size(v_a_3035_);
                v___x_3039_ = lean_nat_dec_lt(v_i_3036_, v___x_3038_);
                if v___x_3039_ == 0 {
                    crate::leanh::lean_dec(v_i_3036_);
                    return v_acc_3037_;
                } else {
                    v___x_3040_ = lean_array_fget(v_a_3035_, v_i_3036_);
                    match crate::leanh::lean_obj_tag(v___x_3040_) {
                        0 => {
                            if crate::leanh::lean_obj_tag(v_acc_3037_) == 0 {
                                v_key_3041_ = crate::leanh::lean_ctor_get(v___x_3040_, 0);
                                v_val_3042_ = crate::leanh::lean_ctor_get(v___x_3040_, 1);
                                v_isSharedCheck_3053_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3040_)) as u8;
                                if v_isSharedCheck_3053_ == 0 {
                                    v___x_3044_ = v___x_3040_;
                                    v_isShared_3045_ = v_isSharedCheck_3053_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_3042_);
                                    crate::leanh::lean_inc(v_key_3041_);
                                    crate::leanh::lean_dec(v___x_3040_);
                                    v___x_3044_ = crate::leanh::lean_box(0);
                                    v_isShared_3045_ = v_isSharedCheck_3053_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_acc_3037_, 1);
                                crate::leanh::lean_dec_ref_known(v___x_3040_, 2);
                                crate::leanh::lean_dec(v_i_3036_);
                                v___x_3054_ = crate::leanh::lean_box(0);
                                return v___x_3054_;
                            }
                        }
                        1 => {
                            crate::leanh::lean_dec_ref_known(v___x_3040_, 1);
                            crate::leanh::lean_dec(v_acc_3037_);
                            crate::leanh::lean_dec(v_i_3036_);
                            v___x_3055_ = crate::leanh::lean_box(0);
                            return v___x_3055_;
                        }
                        _ => {
                            v___x_3056_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_3057_ = lean_nat_add(v_i_3036_, v___x_3056_);
                            crate::leanh::lean_dec(v_i_3036_);
                            v_i_3036_ = v___x_3057_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3046_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3047_ = lean_nat_add(v_i_3036_, v___x_3046_);
                crate::leanh::lean_dec(v_i_3036_);
                if v_isShared_3045_ == 0 {
                    v___x_3049_ = v___x_3044_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3052_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_key_3041_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_val_3042_);
                    v___x_3049_ = v_reuseFailAlloc_3052_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3050_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3050_, 0, v___x_3049_);
                v_i_3036_ = v___x_3047_;
                v_acc_3037_ = v___x_3050_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_isUnaryEntries___redArg___boxed(
    mut v_a_3059_: *mut crate::leanh::LeanObject,
    mut v_i_3060_: *mut crate::leanh::LeanObject,
    mut v_acc_3061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3062_ =
        l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_3059_, v_i_3060_, v_acc_3061_);
    crate::leanh::lean_dec_ref(v_a_3059_);
    return v_res_3062_;
}
pub unsafe fn l_Lean_PersistentHashMap_isUnaryEntries(
    mut v_00_u03b1_3063_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3064_: *mut crate::leanh::LeanObject,
    mut v_a_3065_: *mut crate::leanh::LeanObject,
    mut v_i_3066_: *mut crate::leanh::LeanObject,
    mut v_acc_3067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3068_ =
        l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_3065_, v_i_3066_, v_acc_3067_);
    return v___x_3068_;
}
pub unsafe fn l_Lean_PersistentHashMap_isUnaryEntries___boxed(
    mut v_00_u03b1_3069_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3070_: *mut crate::leanh::LeanObject,
    mut v_a_3071_: *mut crate::leanh::LeanObject,
    mut v_i_3072_: *mut crate::leanh::LeanObject,
    mut v_acc_3073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3074_ = l_Lean_PersistentHashMap_isUnaryEntries(
        v_00_u03b1_3069_,
        v_00_u03b2_3070_,
        v_a_3071_,
        v_i_3072_,
        v_acc_3073_,
    );
    crate::leanh::lean_dec_ref(v_a_3071_);
    return v_res_3074_;
}
pub unsafe fn l_Lean_PersistentHashMap_isUnaryNode___redArg(
    mut v_x_3075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3084_: u8 = 0;
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: u8 = 0;
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3075_) == 0 {
                    v_es_3076_ = crate::leanh::lean_ctor_get(v_x_3075_, 0);
                    crate::leanh::lean_inc_ref(v_es_3076_);
                    crate::leanh::lean_dec_ref_known(v_x_3075_, 1);
                    v___x_3077_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3078_ = crate::leanh::lean_box(0);
                    v___x_3079_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(
                        v_es_3076_,
                        v___x_3077_,
                        v___x_3078_,
                    );
                    crate::leanh::lean_dec_ref(v_es_3076_);
                    return v___x_3079_;
                } else {
                    v_ks_3080_ = crate::leanh::lean_ctor_get(v_x_3075_, 0);
                    v_vs_3081_ = crate::leanh::lean_ctor_get(v_x_3075_, 1);
                    v_isSharedCheck_3096_ = (!crate::leanh::lean_is_exclusive(v_x_3075_)) as u8;
                    if v_isSharedCheck_3096_ == 0 {
                        v___x_3083_ = v_x_3075_;
                        v_isShared_3084_ = v_isSharedCheck_3096_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3081_);
                        crate::leanh::lean_inc(v_ks_3080_);
                        crate::leanh::lean_dec(v_x_3075_);
                        v___x_3083_ = crate::leanh::lean_box(0);
                        v_isShared_3084_ = v_isSharedCheck_3096_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3085_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3086_ = lean_array_get_size(v_ks_3080_);
                v___x_3087_ = lean_nat_dec_eq(v___x_3085_, v___x_3086_);
                if v___x_3087_ == 0 {
                    crate::leanh::lean_del_object(v___x_3083_);
                    crate::leanh::lean_dec_ref(v_vs_3081_);
                    crate::leanh::lean_dec_ref(v_ks_3080_);
                    v___x_3088_ = crate::leanh::lean_box(0);
                    return v___x_3088_;
                } else {
                    v___x_3089_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3090_ = lean_array_fget(v_ks_3080_, v___x_3089_);
                    crate::leanh::lean_dec_ref(v_ks_3080_);
                    v___x_3091_ = lean_array_fget(v_vs_3081_, v___x_3089_);
                    crate::leanh::lean_dec_ref(v_vs_3081_);
                    if v_isShared_3084_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3083_, 0);
                        crate::leanh::lean_ctor_set(v___x_3083_, 1, v___x_3091_);
                        crate::leanh::lean_ctor_set(v___x_3083_, 0, v___x_3090_);
                        v___x_3093_ = v___x_3083_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3095_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3090_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 1, v___x_3091_);
                        v___x_3093_ = v_reuseFailAlloc_3095_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3094_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3094_, 0, v___x_3093_);
                return v___x_3094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_isUnaryNode(
    mut v_00_u03b1_3097_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3098_: *mut crate::leanh::LeanObject,
    mut v_x_3099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3100_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_x_3099_);
    return v___x_3100_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___redArg(
    mut v_inst_3101_: *mut crate::leanh::LeanObject,
    mut v_x_3102_: *mut crate::leanh::LeanObject,
    mut v_x_3103_: usize,
    mut v_x_3104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: usize = 0;
    let mut v___x_3108_: usize = 0;
    let mut v___x_3109_: usize = 0;
    let mut v_j_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: u8 = 0;
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3117_: u8 = 0;
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3122_: u8 = 0;
    let mut v_unused_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3126_: u8 = 0;
    let mut v_node_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3130_: u8 = 0;
    let mut v_entries_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: usize = 0;
    let mut v_newNode_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3147_: u8 = 0;
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3155_: u8 = 0;
    let mut v_isSharedCheck_3156_: u8 = 0;
    let mut v_isSharedCheck_3157_: u8 = 0;
    let mut v_unused_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3163_: u8 = 0;
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_x27_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vals_x27_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3102_) == 0 {
                    v_es_3105_ = crate::leanh::lean_ctor_get(v_x_3102_, 0);
                    v___x_3106_ = crate::leanh::lean_box(2);
                    v___x_3107_ = 5usize;
                    v___x_3108_ = crate::leanh::lean_usize_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentHashMap_insertAux___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once
                        ),
                        _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1,
                    );
                    v___x_3109_ = lean_usize_land(v_x_3103_, v___x_3108_);
                    v_j_3110_ = lean_usize_to_nat(v___x_3109_);
                    v_entry_3111_ = lean_array_get(v___x_3106_, v_es_3105_, v_j_3110_);
                    match crate::leanh::lean_obj_tag(v_entry_3111_) {
                        0 => {
                            v_key_3112_ = crate::leanh::lean_ctor_get(v_entry_3111_, 0);
                            crate::leanh::lean_inc(v_key_3112_);
                            crate::leanh::lean_dec_ref_known(v_entry_3111_, 2);
                            v___x_3113_ =
                                crate::leanh::lean_apply_2(v_inst_3101_, v_x_3104_, v_key_3112_);
                            v___x_3114_ = (crate::leanh::lean_unbox(v___x_3113_) as u8);
                            if v___x_3114_ == 0 {
                                crate::leanh::lean_dec(v_j_3110_);
                                return v_x_3102_;
                            } else {
                                crate::leanh::lean_inc_ref(v_es_3105_);
                                v_isSharedCheck_3122_ =
                                    (!crate::leanh::lean_is_exclusive(v_x_3102_)) as u8;
                                if v_isSharedCheck_3122_ == 0 {
                                    v_unused_3123_ = crate::leanh::lean_ctor_get(v_x_3102_, 0);
                                    crate::leanh::lean_dec(v_unused_3123_);
                                    v___x_3116_ = v_x_3102_;
                                    v_isShared_3117_ = v_isSharedCheck_3122_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_x_3102_);
                                    v___x_3116_ = crate::leanh::lean_box(0);
                                    v_isShared_3117_ = v_isSharedCheck_3122_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            crate::leanh::lean_inc_ref(v_es_3105_);
                            v_isSharedCheck_3157_ =
                                (!crate::leanh::lean_is_exclusive(v_x_3102_)) as u8;
                            if v_isSharedCheck_3157_ == 0 {
                                v_unused_3158_ = crate::leanh::lean_ctor_get(v_x_3102_, 0);
                                crate::leanh::lean_dec(v_unused_3158_);
                                v___x_3125_ = v_x_3102_;
                                v_isShared_3126_ = v_isSharedCheck_3157_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_x_3102_);
                                v___x_3125_ = crate::leanh::lean_box(0);
                                v_isShared_3126_ = v_isSharedCheck_3157_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec(v_j_3110_);
                            crate::leanh::lean_dec(v_x_3104_);
                            crate::leanh::lean_dec_ref(v_inst_3101_);
                            return v_x_3102_;
                        }
                    }
                } else {
                    v_ks_3159_ = crate::leanh::lean_ctor_get(v_x_3102_, 0);
                    v_vs_3160_ = crate::leanh::lean_ctor_get(v_x_3102_, 1);
                    v_isSharedCheck_3174_ = (!crate::leanh::lean_is_exclusive(v_x_3102_)) as u8;
                    if v_isSharedCheck_3174_ == 0 {
                        v___x_3162_ = v_x_3102_;
                        v_isShared_3163_ = v_isSharedCheck_3174_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3160_);
                        crate::leanh::lean_inc(v_ks_3159_);
                        crate::leanh::lean_dec(v_x_3102_);
                        v___x_3162_ = crate::leanh::lean_box(0);
                        v_isShared_3163_ = v_isSharedCheck_3174_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3118_ = lean_array_set(v_es_3105_, v_j_3110_, v___x_3106_);
                crate::leanh::lean_dec(v_j_3110_);
                if v_isShared_3117_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3116_, 0, v___x_3118_);
                    v___x_3120_ = v___x_3116_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3121_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
                    v___x_3120_ = v_reuseFailAlloc_3121_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3120_;
            }
            3 => {
                v_node_3127_ = crate::leanh::lean_ctor_get(v_entry_3111_, 0);
                v_isSharedCheck_3156_ = (!crate::leanh::lean_is_exclusive(v_entry_3111_)) as u8;
                if v_isSharedCheck_3156_ == 0 {
                    v___x_3129_ = v_entry_3111_;
                    v_isShared_3130_ = v_isSharedCheck_3156_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_node_3127_);
                    crate::leanh::lean_dec(v_entry_3111_);
                    v___x_3129_ = crate::leanh::lean_box(0);
                    v_isShared_3130_ = v_isSharedCheck_3156_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_entries_3131_ = lean_array_set(v_es_3105_, v_j_3110_, v___x_3106_);
                v___x_3132_ = lean_usize_shift_right(v_x_3103_, v___x_3107_);
                v_newNode_3133_ = l_Lean_PersistentHashMap_eraseAux___redArg(
                    v_inst_3101_,
                    v_node_3127_,
                    v___x_3132_,
                    v_x_3104_,
                );
                crate::leanh::lean_inc_ref(v_newNode_3133_);
                v___x_3134_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_3133_);
                if crate::leanh::lean_obj_tag(v___x_3134_) == 0 {
                    if v_isShared_3130_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3129_, 0, v_newNode_3133_);
                        v___x_3136_ = v___x_3129_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3141_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_newNode_3133_);
                        v___x_3136_ = v_reuseFailAlloc_3141_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_newNode_3133_);
                    crate::leanh::lean_del_object(v___x_3129_);
                    v_val_3142_ = crate::leanh::lean_ctor_get(v___x_3134_, 0);
                    crate::leanh::lean_inc(v_val_3142_);
                    crate::leanh::lean_dec_ref_known(v___x_3134_, 1);
                    v_fst_3143_ = crate::leanh::lean_ctor_get(v_val_3142_, 0);
                    v_snd_3144_ = crate::leanh::lean_ctor_get(v_val_3142_, 1);
                    v_isSharedCheck_3155_ = (!crate::leanh::lean_is_exclusive(v_val_3142_)) as u8;
                    if v_isSharedCheck_3155_ == 0 {
                        v___x_3146_ = v_val_3142_;
                        v_isShared_3147_ = v_isSharedCheck_3155_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3144_);
                        crate::leanh::lean_inc(v_fst_3143_);
                        crate::leanh::lean_dec(v_val_3142_);
                        v___x_3146_ = crate::leanh::lean_box(0);
                        v_isShared_3147_ = v_isSharedCheck_3155_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3137_ = lean_array_set(v_entries_3131_, v_j_3110_, v___x_3136_);
                crate::leanh::lean_dec(v_j_3110_);
                if v_isShared_3126_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3125_, 0, v___x_3137_);
                    v___x_3139_ = v___x_3125_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3140_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3137_);
                    v___x_3139_ = v_reuseFailAlloc_3140_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3139_;
            }
            7 => {
                if v_isShared_3147_ == 0 {
                    v___x_3149_ = v___x_3146_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3154_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_fst_3143_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_snd_3144_);
                    v___x_3149_ = v_reuseFailAlloc_3154_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3150_ = lean_array_set(v_entries_3131_, v_j_3110_, v___x_3149_);
                crate::leanh::lean_dec(v_j_3110_);
                if v_isShared_3126_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3125_, 0, v___x_3150_);
                    v___x_3152_ = v___x_3125_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3153_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3150_);
                    v___x_3152_ = v_reuseFailAlloc_3153_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3152_;
            }
            10 => {
                v___x_3164_ = l_Array_finIdxOf_x3f___redArg(v_inst_3101_, v_ks_3159_, v_x_3104_);
                if crate::leanh::lean_obj_tag(v___x_3164_) == 0 {
                    if v_isShared_3163_ == 0 {
                        v___x_3166_ = v___x_3162_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3167_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_ks_3159_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3167_, 1, v_vs_3160_);
                        v___x_3166_ = v_reuseFailAlloc_3167_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_val_3168_ = crate::leanh::lean_ctor_get(v___x_3164_, 0);
                    crate::leanh::lean_inc_n(v_val_3168_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3164_, 1);
                    v_keys_x27_3169_ = l_Array_eraseIdx___redArg(v_ks_3159_, v_val_3168_);
                    v_vals_x27_3170_ = l_Array_eraseIdx___redArg(v_vs_3160_, v_val_3168_);
                    if v_isShared_3163_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3162_, 1, v_vals_x27_3170_);
                        crate::leanh::lean_ctor_set(v___x_3162_, 0, v_keys_x27_3169_);
                        v___x_3172_ = v___x_3162_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3173_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_keys_x27_3169_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3173_, 1, v_vals_x27_3170_);
                        v___x_3172_ = v_reuseFailAlloc_3173_;
                        state = 12;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_3166_;
            }
            12 => {
                return v___x_3172_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___redArg___boxed(
    mut v_inst_3175_: *mut crate::leanh::LeanObject,
    mut v_x_3176_: *mut crate::leanh::LeanObject,
    mut v_x_3177_: *mut crate::leanh::LeanObject,
    mut v_x_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_232__boxed_3179_: usize = 0;
    let mut v_res_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_232__boxed_3179_ = crate::leanh::lean_unbox_usize(v_x_3177_);
    crate::leanh::lean_dec(v_x_3177_);
    v_res_3180_ = l_Lean_PersistentHashMap_eraseAux___redArg(
        v_inst_3175_,
        v_x_3176_,
        v_x_232__boxed_3179_,
        v_x_3178_,
    );
    return v_res_3180_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux(
    mut v_00_u03b1_3181_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3182_: *mut crate::leanh::LeanObject,
    mut v_inst_3183_: *mut crate::leanh::LeanObject,
    mut v_x_3184_: *mut crate::leanh::LeanObject,
    mut v_x_3185_: usize,
    mut v_x_3186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3187_ =
        l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_3183_, v_x_3184_, v_x_3185_, v_x_3186_);
    return v___x_3187_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___boxed(
    mut v_00_u03b1_3188_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3189_: *mut crate::leanh::LeanObject,
    mut v_inst_3190_: *mut crate::leanh::LeanObject,
    mut v_x_3191_: *mut crate::leanh::LeanObject,
    mut v_x_3192_: *mut crate::leanh::LeanObject,
    mut v_x_3193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_375__boxed_3194_: usize = 0;
    let mut v_res_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_375__boxed_3194_ = crate::leanh::lean_unbox_usize(v_x_3192_);
    crate::leanh::lean_dec(v_x_3192_);
    v_res_3195_ = l_Lean_PersistentHashMap_eraseAux(
        v_00_u03b1_3188_,
        v_00_u03b2_3189_,
        v_inst_3190_,
        v_x_3191_,
        v_x_375__boxed_3194_,
        v_x_3193_,
    );
    return v_res_3195_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___redArg(
    mut v_x_3196_: *mut crate::leanh::LeanObject,
    mut v_x_3197_: *mut crate::leanh::LeanObject,
    mut v_x_3198_: *mut crate::leanh::LeanObject,
    mut v_x_3199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: u64 = 0;
    let mut v_h_3202_: usize = 0;
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_x_3199_);
    v___x_3200_ = crate::leanh::lean_apply_1(v_x_3197_, v_x_3199_);
    v___x_3201_ = crate::leanh::lean_unbox_uint64(v___x_3200_);
    crate::leanh::lean_dec_ref(v___x_3200_);
    v_h_3202_ = lean_uint64_to_usize(v___x_3201_);
    v___x_3203_ =
        l_Lean_PersistentHashMap_eraseAux___redArg(v_x_3196_, v_x_3198_, v_h_3202_, v_x_3199_);
    return v___x_3203_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase(
    mut v_00_u03b1_3204_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3205_: *mut crate::leanh::LeanObject,
    mut v_x_3206_: *mut crate::leanh::LeanObject,
    mut v_x_3207_: *mut crate::leanh::LeanObject,
    mut v_x_3208_: *mut crate::leanh::LeanObject,
    mut v_x_3209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3210_ =
        l_Lean_PersistentHashMap_erase___redArg(v_x_3206_, v_x_3207_, v_x_3208_, v_x_3209_);
    return v___x_3210_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed(
    mut v_i_3211_: *mut crate::leanh::LeanObject,
    mut v_inst_3212_: *mut crate::leanh::LeanObject,
    mut v_f_3213_: *mut crate::leanh::LeanObject,
    mut v_keys_3214_: *mut crate::leanh::LeanObject,
    mut v_vals_3215_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3217_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(v_i_3211_, v_inst_3212_, v_f_3213_, v_keys_3214_, v_vals_3215_, v_____do__lift_3216_);
    crate::leanh::lean_dec(v_i_3211_);
    return v_res_3217_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(
    mut v_inst_3218_: *mut crate::leanh::LeanObject,
    mut v_f_3219_: *mut crate::leanh::LeanObject,
    mut v_keys_3220_: *mut crate::leanh::LeanObject,
    mut v_vals_3221_: *mut crate::leanh::LeanObject,
    mut v_i_3222_: *mut crate::leanh::LeanObject,
    mut v_acc_3223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: u8 = 0;
    v___x_3224_ = lean_array_get_size(v_keys_3220_);
    v___x_3225_ = lean_nat_dec_lt(v_i_3222_, v___x_3224_);
    if v___x_3225_ == 0 {
        let mut v_toApplicative_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_i_3222_);
        crate::leanh::lean_dec_ref(v_vals_3221_);
        crate::leanh::lean_dec_ref(v_keys_3220_);
        crate::leanh::lean_dec(v_f_3219_);
        v_toApplicative_3226_ = crate::leanh::lean_ctor_get(v_inst_3218_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_3226_);
        crate::leanh::lean_dec_ref(v_inst_3218_);
        v_toPure_3227_ = crate::leanh::lean_ctor_get(v_toApplicative_3226_, 1);
        crate::leanh::lean_inc(v_toPure_3227_);
        crate::leanh::lean_dec_ref(v_toApplicative_3226_);
        v___x_3228_ =
            crate::leanh::lean_apply_2(v_toPure_3227_, crate::leanh::lean_box(0), v_acc_3223_);
        return v___x_3228_;
    } else {
        let mut v_toBind_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_3229_ = crate::leanh::lean_ctor_get(v_inst_3218_, 1);
        crate::leanh::lean_inc(v_toBind_3229_);
        crate::leanh::lean_inc_ref(v_vals_3221_);
        crate::leanh::lean_inc_ref(v_keys_3220_);
        crate::leanh::lean_inc(v_f_3219_);
        crate::leanh::lean_inc(v_i_3222_);
        v___f_3230_ = crate::leanh::lean_alloc_closure(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 5);
        crate::leanh::lean_closure_set(v___f_3230_, 0, v_i_3222_);
        crate::leanh::lean_closure_set(v___f_3230_, 1, v_inst_3218_);
        crate::leanh::lean_closure_set(v___f_3230_, 2, v_f_3219_);
        crate::leanh::lean_closure_set(v___f_3230_, 3, v_keys_3220_);
        crate::leanh::lean_closure_set(v___f_3230_, 4, v_vals_3221_);
        v_k_3231_ = lean_array_fget(v_keys_3220_, v_i_3222_);
        crate::leanh::lean_dec_ref(v_keys_3220_);
        v_v_3232_ = lean_array_fget(v_vals_3221_, v_i_3222_);
        crate::leanh::lean_dec(v_i_3222_);
        crate::leanh::lean_dec_ref(v_vals_3221_);
        v___x_3233_ = crate::leanh::lean_apply_3(v_f_3219_, v_acc_3223_, v_k_3231_, v_v_3232_);
        v___x_3234_ = crate::leanh::lean_apply_4(
            v_toBind_3229_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3233_,
            v___f_3230_,
        );
        return v___x_3234_;
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(
    mut v_i_3235_: *mut crate::leanh::LeanObject,
    mut v_inst_3236_: *mut crate::leanh::LeanObject,
    mut v_f_3237_: *mut crate::leanh::LeanObject,
    mut v_keys_3238_: *mut crate::leanh::LeanObject,
    mut v_vals_3239_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3241_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3242_ = lean_nat_add(v_i_3235_, v___x_3241_);
    v___x_3243_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_3236_, v_f_3237_, v_keys_3238_, v_vals_3239_, v___x_3242_, v_____do__lift_3240_);
    return v___x_3243_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse(
    mut v_m_3244_: *mut crate::leanh::LeanObject,
    mut v_inst_3245_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3246_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3247_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3248_: *mut crate::leanh::LeanObject,
    mut v_f_3249_: *mut crate::leanh::LeanObject,
    mut v_keys_3250_: *mut crate::leanh::LeanObject,
    mut v_vals_3251_: *mut crate::leanh::LeanObject,
    mut v_heq_3252_: *mut crate::leanh::LeanObject,
    mut v_i_3253_: *mut crate::leanh::LeanObject,
    mut v_acc_3254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3255_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_3245_, v_f_3249_, v_keys_3250_, v_vals_3251_, v_i_3253_, v_acc_3254_);
    return v___x_3255_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___redArg(
    mut v_inst_3256_: *mut crate::leanh::LeanObject,
    mut v_f_3257_: *mut crate::leanh::LeanObject,
    mut v_x_3258_: *mut crate::leanh::LeanObject,
    mut v_x_3259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3258_) == 0 {
        let mut v_toApplicative_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_es_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3265_: u8 = 0;
        v_toApplicative_3260_ = crate::leanh::lean_ctor_get(v_inst_3256_, 0);
        v_toPure_3261_ = crate::leanh::lean_ctor_get(v_toApplicative_3260_, 1);
        v_es_3262_ = crate::leanh::lean_ctor_get(v_x_3258_, 0);
        crate::leanh::lean_inc_ref(v_es_3262_);
        crate::leanh::lean_dec_ref_known(v_x_3258_, 1);
        v___x_3263_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3264_ = lean_array_get_size(v_es_3262_);
        v___x_3265_ = lean_nat_dec_lt(v___x_3263_, v___x_3264_);
        if v___x_3265_ == 0 {
            let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_toPure_3261_);
            crate::leanh::lean_dec_ref(v_es_3262_);
            crate::leanh::lean_dec(v_f_3257_);
            crate::leanh::lean_dec_ref(v_inst_3256_);
            v___x_3266_ =
                crate::leanh::lean_apply_2(v_toPure_3261_, crate::leanh::lean_box(0), v_x_3259_);
            return v___x_3266_;
        } else {
            let mut v___f_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3268_: u8 = 0;
            crate::leanh::lean_inc(v_toPure_3261_);
            crate::leanh::lean_inc_ref(v_inst_3256_);
            v___f_3267_ = crate::leanh::lean_alloc_closure(
                l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0 as *mut core::ffi::c_void,
                5,
                3,
            );
            crate::leanh::lean_closure_set(v___f_3267_, 0, v_f_3257_);
            crate::leanh::lean_closure_set(v___f_3267_, 1, v_inst_3256_);
            crate::leanh::lean_closure_set(v___f_3267_, 2, v_toPure_3261_);
            v___x_3268_ = lean_nat_dec_le(v___x_3264_, v___x_3264_);
            if v___x_3268_ == 0 {
                if v___x_3265_ == 0 {
                    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_inc(v_toPure_3261_);
                    crate::leanh::lean_dec_ref(v___f_3267_);
                    crate::leanh::lean_dec_ref(v_es_3262_);
                    crate::leanh::lean_dec_ref(v_inst_3256_);
                    v___x_3269_ = crate::leanh::lean_apply_2(
                        v_toPure_3261_,
                        crate::leanh::lean_box(0),
                        v_x_3259_,
                    );
                    return v___x_3269_;
                } else {
                    let mut v___x_3270_: usize = 0;
                    let mut v___x_3271_: usize = 0;
                    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_3270_ = 0usize;
                    v___x_3271_ = lean_usize_of_nat(v___x_3264_);
                    v___x_3272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_3256_,
                        v___f_3267_,
                        v_es_3262_,
                        v___x_3270_,
                        v___x_3271_,
                        v_x_3259_,
                    );
                    return v___x_3272_;
                }
            } else {
                let mut v___x_3273_: usize = 0;
                let mut v___x_3274_: usize = 0;
                let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3273_ = 0usize;
                v___x_3274_ = lean_usize_of_nat(v___x_3264_);
                v___x_3275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_3256_,
                    v___f_3267_,
                    v_es_3262_,
                    v___x_3273_,
                    v___x_3274_,
                    v_x_3259_,
                );
                return v___x_3275_;
            }
        }
    } else {
        let mut v_ks_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ks_3276_ = crate::leanh::lean_ctor_get(v_x_3258_, 0);
        crate::leanh::lean_inc_ref(v_ks_3276_);
        v_vs_3277_ = crate::leanh::lean_ctor_get(v_x_3258_, 1);
        crate::leanh::lean_inc_ref(v_vs_3277_);
        crate::leanh::lean_dec_ref_known(v_x_3258_, 2);
        v___x_3278_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3279_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_3256_, v_f_3257_, v_ks_3276_, v_vs_3277_, v___x_3278_, v_x_3259_);
        return v___x_3279_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0(
    mut v_f_3280_: *mut crate::leanh::LeanObject,
    mut v_inst_3281_: *mut crate::leanh::LeanObject,
    mut v_toPure_3282_: *mut crate::leanh::LeanObject,
    mut v_acc_3283_: *mut crate::leanh::LeanObject,
    mut v_entry_3284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_entry_3284_) {
        0 => {
            let mut v_key_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toPure_3282_);
            crate::leanh::lean_dec_ref(v_inst_3281_);
            v_key_3285_ = crate::leanh::lean_ctor_get(v_entry_3284_, 0);
            crate::leanh::lean_inc(v_key_3285_);
            v_val_3286_ = crate::leanh::lean_ctor_get(v_entry_3284_, 1);
            crate::leanh::lean_inc(v_val_3286_);
            crate::leanh::lean_dec_ref_known(v_entry_3284_, 2);
            v___x_3287_ =
                crate::leanh::lean_apply_3(v_f_3280_, v_acc_3283_, v_key_3285_, v_val_3286_);
            return v___x_3287_;
        }
        1 => {
            let mut v_node_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toPure_3282_);
            v_node_3288_ = crate::leanh::lean_ctor_get(v_entry_3284_, 0);
            crate::leanh::lean_inc(v_node_3288_);
            crate::leanh::lean_dec_ref_known(v_entry_3284_, 1);
            v___x_3289_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
                v_inst_3281_,
                v_f_3280_,
                v_node_3288_,
                v_acc_3283_,
            );
            return v___x_3289_;
        }
        _ => {
            let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_inst_3281_);
            crate::leanh::lean_dec(v_f_3280_);
            v___x_3290_ =
                crate::leanh::lean_apply_2(v_toPure_3282_, crate::leanh::lean_box(0), v_acc_3283_);
            return v___x_3290_;
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux(
    mut v_m_3291_: *mut crate::leanh::LeanObject,
    mut v_inst_3292_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3293_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3294_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3295_: *mut crate::leanh::LeanObject,
    mut v_f_3296_: *mut crate::leanh::LeanObject,
    mut v_x_3297_: *mut crate::leanh::LeanObject,
    mut v_x_3298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3299_ =
        l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_3292_, v_f_3296_, v_x_3297_, v_x_3298_);
    return v___x_3299_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___redArg(
    mut v_inst_3300_: *mut crate::leanh::LeanObject,
    mut v_map_3301_: *mut crate::leanh::LeanObject,
    mut v_f_3302_: *mut crate::leanh::LeanObject,
    mut v_init_3303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3304_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v_inst_3300_,
        v_f_3302_,
        v_map_3301_,
        v_init_3303_,
    );
    return v___x_3304_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM(
    mut v_m_3305_: *mut crate::leanh::LeanObject,
    mut v_inst_3306_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3307_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3308_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3309_: *mut crate::leanh::LeanObject,
    mut v_x_3310_: *mut crate::leanh::LeanObject,
    mut v_x_3311_: *mut crate::leanh::LeanObject,
    mut v_map_3312_: *mut crate::leanh::LeanObject,
    mut v_f_3313_: *mut crate::leanh::LeanObject,
    mut v_init_3314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3315_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v_inst_3306_,
        v_f_3313_,
        v_map_3312_,
        v_init_3314_,
    );
    return v___x_3315_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___boxed(
    mut v_m_3316_: *mut crate::leanh::LeanObject,
    mut v_inst_3317_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3318_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3319_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3320_: *mut crate::leanh::LeanObject,
    mut v_x_3321_: *mut crate::leanh::LeanObject,
    mut v_x_3322_: *mut crate::leanh::LeanObject,
    mut v_map_3323_: *mut crate::leanh::LeanObject,
    mut v_f_3324_: *mut crate::leanh::LeanObject,
    mut v_init_3325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3326_ = l_Lean_PersistentHashMap_foldlM(
        v_m_3316_,
        v_inst_3317_,
        v_00_u03c3_3318_,
        v_00_u03b1_3319_,
        v_00_u03b2_3320_,
        v_x_3321_,
        v_x_3322_,
        v_map_3323_,
        v_f_3324_,
        v_init_3325_,
    );
    crate::leanh::lean_dec_ref(v_x_3322_);
    crate::leanh::lean_dec_ref(v_x_3321_);
    return v_res_3326_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___redArg___lam__0(
    mut v_f_3327_: *mut crate::leanh::LeanObject,
    mut v_x_3328_: *mut crate::leanh::LeanObject,
    mut v___y_3329_: *mut crate::leanh::LeanObject,
    mut v___y_3330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3331_ = crate::leanh::lean_apply_2(v_f_3327_, v___y_3329_, v___y_3330_);
    return v___x_3331_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___redArg(
    mut v_inst_3332_: *mut crate::leanh::LeanObject,
    mut v_map_3333_: *mut crate::leanh::LeanObject,
    mut v_f_3334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3335_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3335_, 0, v_f_3334_);
    v___x_3336_ = crate::leanh::lean_box(0);
    v___x_3337_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v_inst_3332_,
        v___f_3335_,
        v_map_3333_,
        v___x_3336_,
    );
    return v___x_3337_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM(
    mut v_m_3338_: *mut crate::leanh::LeanObject,
    mut v_inst_3339_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3340_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3341_: *mut crate::leanh::LeanObject,
    mut v_x_3342_: *mut crate::leanh::LeanObject,
    mut v_x_3343_: *mut crate::leanh::LeanObject,
    mut v_map_3344_: *mut crate::leanh::LeanObject,
    mut v_f_3345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3346_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_3339_, v_map_3344_, v_f_3345_);
    return v___x_3346_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___boxed(
    mut v_m_3347_: *mut crate::leanh::LeanObject,
    mut v_inst_3348_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3349_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3350_: *mut crate::leanh::LeanObject,
    mut v_x_3351_: *mut crate::leanh::LeanObject,
    mut v_x_3352_: *mut crate::leanh::LeanObject,
    mut v_map_3353_: *mut crate::leanh::LeanObject,
    mut v_f_3354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3355_ = l_Lean_PersistentHashMap_forM(
        v_m_3347_,
        v_inst_3348_,
        v_00_u03b1_3349_,
        v_00_u03b2_3350_,
        v_x_3351_,
        v_x_3352_,
        v_map_3353_,
        v_f_3354_,
    );
    crate::leanh::lean_dec_ref(v_x_3352_);
    crate::leanh::lean_dec_ref(v_x_3351_);
    return v_res_3355_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___redArg___lam__0(
    mut v_f_3356_: *mut crate::leanh::LeanObject,
    mut v_x1_3357_: *mut crate::leanh::LeanObject,
    mut v_x2_3358_: *mut crate::leanh::LeanObject,
    mut v_x3_3359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3360_ = crate::leanh::lean_apply_3(v_f_3356_, v_x1_3357_, v_x2_3358_, v_x3_3359_);
    return v___x_3360_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___redArg(
    mut v_map_3380_: *mut crate::leanh::LeanObject,
    mut v_f_3381_: *mut crate::leanh::LeanObject,
    mut v_init_3382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3383_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashMap_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3383_, 0, v_f_3381_);
    v___x_3384_ = l_Lean_PersistentHashMap_foldl___redArg___closed__9;
    v___x_3385_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v___x_3384_,
        v___f_3383_,
        v_map_3380_,
        v_init_3382_,
    );
    return v___x_3385_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl(
    mut v_00_u03c3_3386_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3387_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3388_: *mut crate::leanh::LeanObject,
    mut v_x_3389_: *mut crate::leanh::LeanObject,
    mut v_x_3390_: *mut crate::leanh::LeanObject,
    mut v_map_3391_: *mut crate::leanh::LeanObject,
    mut v_f_3392_: *mut crate::leanh::LeanObject,
    mut v_init_3393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3394_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_3391_, v_f_3392_, v_init_3393_);
    return v___x_3394_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___boxed(
    mut v_00_u03c3_3395_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3396_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3397_: *mut crate::leanh::LeanObject,
    mut v_x_3398_: *mut crate::leanh::LeanObject,
    mut v_x_3399_: *mut crate::leanh::LeanObject,
    mut v_map_3400_: *mut crate::leanh::LeanObject,
    mut v_f_3401_: *mut crate::leanh::LeanObject,
    mut v_init_3402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3403_ = l_Lean_PersistentHashMap_foldl(
        v_00_u03c3_3395_,
        v_00_u03b1_3396_,
        v_00_u03b2_3397_,
        v_x_3398_,
        v_x_3399_,
        v_map_3400_,
        v_f_3401_,
        v_init_3402_,
    );
    crate::leanh::lean_dec_ref(v_x_3399_);
    crate::leanh::lean_dec_ref(v_x_3398_);
    return v_res_3403_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___redArg___lam__0(
    mut v_x_3404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3408_: u8 = 0;
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3412_: u8 = 0;
    let mut v_a_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3416_: u8 = 0;
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3404_) == 0 {
                    v_a_3405_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    v_isSharedCheck_3412_ = (!crate::leanh::lean_is_exclusive(v_x_3404_)) as u8;
                    if v_isSharedCheck_3412_ == 0 {
                        v___x_3407_ = v_x_3404_;
                        v_isShared_3408_ = v_isSharedCheck_3412_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3405_);
                        crate::leanh::lean_dec(v_x_3404_);
                        v___x_3407_ = crate::leanh::lean_box(0);
                        v_isShared_3408_ = v_isSharedCheck_3412_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3413_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    v_isSharedCheck_3420_ = (!crate::leanh::lean_is_exclusive(v_x_3404_)) as u8;
                    if v_isSharedCheck_3420_ == 0 {
                        v___x_3415_ = v_x_3404_;
                        v_isShared_3416_ = v_isSharedCheck_3420_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3413_);
                        crate::leanh::lean_dec(v_x_3404_);
                        v___x_3415_ = crate::leanh::lean_box(0);
                        v_isShared_3416_ = v_isSharedCheck_3420_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3408_ == 0 {
                    v___x_3410_ = v___x_3407_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3411_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
                    v___x_3410_ = v_reuseFailAlloc_3411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3410_;
            }
            3 => {
                if v_isShared_3416_ == 0 {
                    v___x_3418_ = v___x_3415_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3419_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
                    v___x_3418_ = v_reuseFailAlloc_3419_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___redArg___lam__1(
    mut v_toPure_3421_: *mut crate::leanh::LeanObject,
    mut v_result_3422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_3423_ = crate::leanh::lean_ctor_get(v_result_3422_, 0);
    crate::leanh::lean_inc(v_a_3423_);
    crate::leanh::lean_dec_ref(v_result_3422_);
    v___x_3424_ = crate::leanh::lean_apply_2(v_toPure_3421_, crate::leanh::lean_box(0), v_a_3423_);
    return v___x_3424_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___redArg___lam__2(
    mut v_toFunctor_3425_: *mut crate::leanh::LeanObject,
    mut v_f_3426_: *mut crate::leanh::LeanObject,
    mut v_intoError_3427_: *mut crate::leanh::LeanObject,
    mut v_s_3428_: *mut crate::leanh::LeanObject,
    mut v_a_3429_: *mut crate::leanh::LeanObject,
    mut v_b_3430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3434_: u8 = 0;
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3440_: u8 = 0;
    let mut v_unused_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3431_ = crate::leanh::lean_ctor_get(v_toFunctor_3425_, 0);
                v_isSharedCheck_3440_ = (!crate::leanh::lean_is_exclusive(v_toFunctor_3425_)) as u8;
                if v_isSharedCheck_3440_ == 0 {
                    v_unused_3441_ = crate::leanh::lean_ctor_get(v_toFunctor_3425_, 1);
                    crate::leanh::lean_dec(v_unused_3441_);
                    v___x_3433_ = v_toFunctor_3425_;
                    v_isShared_3434_ = v_isSharedCheck_3440_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_3431_);
                    crate::leanh::lean_dec(v_toFunctor_3425_);
                    v___x_3433_ = crate::leanh::lean_box(0);
                    v_isShared_3434_ = v_isSharedCheck_3440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3434_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3433_, 1, v_b_3430_);
                    crate::leanh::lean_ctor_set(v___x_3433_, 0, v_a_3429_);
                    v___x_3436_ = v___x_3433_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3439_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3429_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3439_, 1, v_b_3430_);
                    v___x_3436_ = v_reuseFailAlloc_3439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3437_ = crate::leanh::lean_apply_2(v_f_3426_, v___x_3436_, v_s_3428_);
                v___x_3438_ = crate::leanh::lean_apply_4(
                    v_map_3431_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_intoError_3427_,
                    v___x_3437_,
                );
                return v___x_3438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___redArg(
    mut v_inst_3443_: *mut crate::leanh::LeanObject,
    mut v_map_3444_: *mut crate::leanh::LeanObject,
    mut v_init_3445_: *mut crate::leanh::LeanObject,
    mut v_f_3446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intoError_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3447_ = crate::leanh::lean_ctor_get(v_inst_3443_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3447_);
    v_toBind_3448_ = crate::leanh::lean_ctor_get(v_inst_3443_, 1);
    crate::leanh::lean_inc(v_toBind_3448_);
    crate::leanh::lean_inc_ref_n(v_inst_3443_, 6);
    v___f_3449_ = crate::leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3449_, 0, v_inst_3443_);
    v___f_3450_ = crate::leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3450_, 0, v_inst_3443_);
    v___f_3451_ = crate::leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3451_, 0, v_inst_3443_);
    v___f_3452_ = crate::leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3452_, 0, v_inst_3443_);
    v___x_3453_ = crate::leanh::lean_alloc_closure(l_ExceptT_map as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___x_3453_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3453_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3453_, 2, v_inst_3443_);
    v___x_3454_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3454_, 0, v___x_3453_);
    crate::leanh::lean_ctor_set(v___x_3454_, 1, v___f_3449_);
    v___x_3455_ = crate::leanh::lean_alloc_closure(l_ExceptT_pure as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_3455_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3455_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3455_, 2, v_inst_3443_);
    v___x_3456_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3456_, 0, v___x_3454_);
    crate::leanh::lean_ctor_set(v___x_3456_, 1, v___x_3455_);
    crate::leanh::lean_ctor_set(v___x_3456_, 2, v___f_3450_);
    crate::leanh::lean_ctor_set(v___x_3456_, 3, v___f_3451_);
    crate::leanh::lean_ctor_set(v___x_3456_, 4, v___f_3452_);
    v___x_3457_ = crate::leanh::lean_alloc_closure(l_ExceptT_bind as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___x_3457_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3457_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3457_, 2, v_inst_3443_);
    v___x_3458_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3458_, 0, v___x_3456_);
    crate::leanh::lean_ctor_set(v___x_3458_, 1, v___x_3457_);
    v_toFunctor_3459_ = crate::leanh::lean_ctor_get(v_toApplicative_3447_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_3459_);
    v_toPure_3460_ = crate::leanh::lean_ctor_get(v_toApplicative_3447_, 1);
    crate::leanh::lean_inc(v_toPure_3460_);
    crate::leanh::lean_dec_ref(v_toApplicative_3447_);
    v_intoError_3461_ = l_Lean_PersistentHashMap_forIn___redArg___closed__0;
    v___f_3462_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashMap_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3462_, 0, v_toPure_3460_);
    v___f_3463_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashMap_forIn___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3463_, 0, v_toFunctor_3459_);
    crate::leanh::lean_closure_set(v___f_3463_, 1, v_f_3446_);
    crate::leanh::lean_closure_set(v___f_3463_, 2, v_intoError_3461_);
    crate::leanh::lean_inc_ref(v_map_3444_);
    v___x_3464_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v___x_3458_,
        v___f_3463_,
        v_map_3444_,
        v_init_3445_,
    );
    v___x_3465_ = crate::leanh::lean_apply_4(
        v_toBind_3448_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3464_,
        v___f_3462_,
    );
    return v___x_3465_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___redArg___boxed(
    mut v_inst_3466_: *mut crate::leanh::LeanObject,
    mut v_map_3467_: *mut crate::leanh::LeanObject,
    mut v_init_3468_: *mut crate::leanh::LeanObject,
    mut v_f_3469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3470_ =
        l_Lean_PersistentHashMap_forIn___redArg(v_inst_3466_, v_map_3467_, v_init_3468_, v_f_3469_);
    crate::leanh::lean_dec_ref(v_map_3467_);
    return v_res_3470_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn(
    mut v_m_3471_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3472_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3473_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3474_: *mut crate::leanh::LeanObject,
    mut v_x_3475_: *mut crate::leanh::LeanObject,
    mut v_x_3476_: *mut crate::leanh::LeanObject,
    mut v_inst_3477_: *mut crate::leanh::LeanObject,
    mut v_map_3478_: *mut crate::leanh::LeanObject,
    mut v_init_3479_: *mut crate::leanh::LeanObject,
    mut v_f_3480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3481_ =
        l_Lean_PersistentHashMap_forIn___redArg(v_inst_3477_, v_map_3478_, v_init_3479_, v_f_3480_);
    return v___x_3481_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___boxed(
    mut v_m_3482_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3483_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3484_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3485_: *mut crate::leanh::LeanObject,
    mut v_x_3486_: *mut crate::leanh::LeanObject,
    mut v_x_3487_: *mut crate::leanh::LeanObject,
    mut v_inst_3488_: *mut crate::leanh::LeanObject,
    mut v_map_3489_: *mut crate::leanh::LeanObject,
    mut v_init_3490_: *mut crate::leanh::LeanObject,
    mut v_f_3491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3492_ = l_Lean_PersistentHashMap_forIn(
        v_m_3482_,
        v_00_u03c3_3483_,
        v_00_u03b1_3484_,
        v_00_u03b2_3485_,
        v_x_3486_,
        v_x_3487_,
        v_inst_3488_,
        v_map_3489_,
        v_init_3490_,
        v_f_3491_,
    );
    crate::leanh::lean_dec_ref(v_map_3489_);
    crate::leanh::lean_dec_ref(v_x_3487_);
    crate::leanh::lean_dec_ref(v_x_3486_);
    return v_res_3492_;
}
pub unsafe fn l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(
    mut v_inst_3493_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3494_: *mut crate::leanh::LeanObject,
    mut v___y_3495_: *mut crate::leanh::LeanObject,
    mut v___y_3496_: *mut crate::leanh::LeanObject,
    mut v___y_3497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3498_ = l_Lean_PersistentHashMap_forIn___redArg(
        v_inst_3493_,
        v___y_3495_,
        v___y_3496_,
        v___y_3497_,
    );
    return v___x_3498_;
}
pub unsafe fn l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed(
    mut v_inst_3499_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3500_: *mut crate::leanh::LeanObject,
    mut v___y_3501_: *mut crate::leanh::LeanObject,
    mut v___y_3502_: *mut crate::leanh::LeanObject,
    mut v___y_3503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3504_ = l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(
        v_inst_3499_,
        v_00_u03b2_3500_,
        v___y_3501_,
        v___y_3502_,
        v___y_3503_,
    );
    crate::leanh::lean_dec_ref(v___y_3501_);
    return v_res_3504_;
}
pub unsafe fn l_Lean_PersistentHashMap_instForInProdOfMonad___redArg(
    mut v_inst_3505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3506_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3506_, 0, v_inst_3505_);
    return v___f_3506_;
}
pub unsafe fn l_Lean_PersistentHashMap_instForInProdOfMonad(
    mut v_m_3507_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3508_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3509_: *mut crate::leanh::LeanObject,
    mut v_x_3510_: *mut crate::leanh::LeanObject,
    mut v_x_3511_: *mut crate::leanh::LeanObject,
    mut v_inst_3512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3513_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3513_, 0, v_inst_3512_);
    return v___f_3513_;
}
pub unsafe fn l_Lean_PersistentHashMap_instForInProdOfMonad___boxed(
    mut v_m_3514_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3515_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3516_: *mut crate::leanh::LeanObject,
    mut v_x_3517_: *mut crate::leanh::LeanObject,
    mut v_x_3518_: *mut crate::leanh::LeanObject,
    mut v_inst_3519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3520_ = l_Lean_PersistentHashMap_instForInProdOfMonad(
        v_m_3514_,
        v_00_u03b1_3515_,
        v_00_u03b2_3516_,
        v_x_3517_,
        v_x_3518_,
        v_inst_3519_,
    );
    crate::leanh::lean_dec_ref(v_x_3518_);
    crate::leanh::lean_dec_ref(v_x_3517_);
    return v_res_3520_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapMAux___redArg___lam__0(
    mut v_toPure_3521_: *mut crate::leanh::LeanObject,
    mut v_entries_x27_3522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3523_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3523_, 0, v_entries_x27_3522_);
    v___x_3524_ =
        crate::leanh::lean_apply_2(v_toPure_3521_, crate::leanh::lean_box(0), v___x_3523_);
    return v___x_3524_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapMAux___redArg___lam__1(
    mut v_toPure_3525_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3527_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3527_, 0, v_____do__lift_3526_);
    v___x_3528_ =
        crate::leanh::lean_apply_2(v_toPure_3525_, crate::leanh::lean_box(0), v___x_3527_);
    return v___x_3528_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapMAux___redArg___lam__2(
    mut v_key_3529_: *mut crate::leanh::LeanObject,
    mut v_toPure_3530_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3532_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3532_, 0, v_key_3529_);
    crate::leanh::lean_ctor_set(v___x_3532_, 1, v_____do__lift_3531_);
    v___x_3533_ =
        crate::leanh::lean_apply_2(v_toPure_3530_, crate::leanh::lean_box(0), v___x_3532_);
    return v___x_3533_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapMAux___redArg___lam__4(
    mut v_ks_3534_: *mut crate::leanh::LeanObject,
    mut v_toPure_3535_: *mut crate::leanh::LeanObject,
    mut v_____x_3536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3537_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3537_, 0, v_ks_3534_);
    crate::leanh::lean_ctor_set(v___x_3537_, 1, v_____x_3536_);
    v___x_3538_ =
        crate::leanh::lean_apply_2(v_toPure_3535_, crate::leanh::lean_box(0), v___x_3537_);
    return v___x_3538_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapMAux___redArg(
    mut v_inst_3539_: *mut crate::leanh::LeanObject,
    mut v_f_3540_: *mut crate::leanh::LeanObject,
    mut v_n_3541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_n_3541_) == 0 {
        let mut v_toApplicative_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_es_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3549_: usize = 0;
        let mut v___x_3550_: usize = 0;
        let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_3542_ = crate::leanh::lean_ctor_get(v_inst_3539_, 0);
        v_toBind_3543_ = crate::leanh::lean_ctor_get(v_inst_3539_, 1);
        crate::leanh::lean_inc_n(v_toBind_3543_, 2);
        v_toPure_3544_ = crate::leanh::lean_ctor_get(v_toApplicative_3542_, 1);
        v_es_3545_ = crate::leanh::lean_ctor_get(v_n_3541_, 0);
        crate::leanh::lean_inc_ref(v_es_3545_);
        crate::leanh::lean_dec_ref_known(v_n_3541_, 1);
        crate::leanh::lean_inc_n(v_toPure_3544_, 3);
        v___f_3546_ = crate::leanh::lean_alloc_closure(
            l_Lean_PersistentHashMap_mapMAux___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_3546_, 0, v_toPure_3544_);
        v___f_3547_ = crate::leanh::lean_alloc_closure(
            l_Lean_PersistentHashMap_mapMAux___redArg___lam__1 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_3547_, 0, v_toPure_3544_);
        crate::leanh::lean_inc_ref(v_inst_3539_);
        v___f_3548_ = crate::leanh::lean_alloc_closure(
            l_Lean_PersistentHashMap_mapMAux___redArg___lam__3 as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_3548_, 0, v_toPure_3544_);
        crate::leanh::lean_closure_set(v___f_3548_, 1, v_f_3540_);
        crate::leanh::lean_closure_set(v___f_3548_, 2, v_toBind_3543_);
        crate::leanh::lean_closure_set(v___f_3548_, 3, v_inst_3539_);
        crate::leanh::lean_closure_set(v___f_3548_, 4, v___f_3547_);
        v_sz_3549_ = lean_array_size(v_es_3545_);
        v___x_3550_ = 0usize;
        v___x_3551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_inst_3539_,
            v___f_3548_,
            v_sz_3549_,
            v___x_3550_,
            v_es_3545_,
        );
        v___x_3552_ = crate::leanh::lean_apply_4(
            v_toBind_3543_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3551_,
            v___f_3546_,
        );
        return v___x_3552_;
    } else {
        let mut v_toApplicative_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ks_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_3553_ = crate::leanh::lean_ctor_get(v_inst_3539_, 0);
        v_toBind_3554_ = crate::leanh::lean_ctor_get(v_inst_3539_, 1);
        crate::leanh::lean_inc(v_toBind_3554_);
        v_toPure_3555_ = crate::leanh::lean_ctor_get(v_toApplicative_3553_, 1);
        v_ks_3556_ = crate::leanh::lean_ctor_get(v_n_3541_, 0);
        crate::leanh::lean_inc_ref(v_ks_3556_);
        v_vs_3557_ = crate::leanh::lean_ctor_get(v_n_3541_, 1);
        crate::leanh::lean_inc_ref(v_vs_3557_);
        crate::leanh::lean_dec_ref_known(v_n_3541_, 2);
        crate::leanh::lean_inc(v_toPure_3555_);
        v___f_3558_ = crate::leanh::lean_alloc_closure(
            l_Lean_PersistentHashMap_mapMAux___redArg___lam__4 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3558_, 0, v_ks_3556_);
        crate::leanh::lean_closure_set(v___f_3558_, 1, v_toPure_3555_);
        v___x_3559_ = l_Array_mapM_x27___redArg(v_inst_3539_, v_f_3540_, v_vs_3557_);
        v___x_3560_ = crate::leanh::lean_apply_4(
            v_toBind_3554_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3559_,
            v___f_3558_,
        );
        return v___x_3560_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_mapMAux___redArg___lam__3(
    mut v_toPure_3561_: *mut crate::leanh::LeanObject,
    mut v_f_3562_: *mut crate::leanh::LeanObject,
    mut v_toBind_3563_: *mut crate::leanh::LeanObject,
    mut v_inst_3564_: *mut crate::leanh::LeanObject,
    mut v___f_3565_: *mut crate::leanh::LeanObject,
    mut v_x_3566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3566_) {
        0 => {
            let mut v_key_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___f_3565_);
            crate::leanh::lean_dec_ref(v_inst_3564_);
            v_key_3567_ = crate::leanh::lean_ctor_get(v_x_3566_, 0);
            crate::leanh::lean_inc(v_key_3567_);
            v_val_3568_ = crate::leanh::lean_ctor_get(v_x_3566_, 1);
            crate::leanh::lean_inc(v_val_3568_);
            crate::leanh::lean_dec_ref_known(v_x_3566_, 2);
            v___f_3569_ = crate::leanh::lean_alloc_closure(
                l_Lean_PersistentHashMap_mapMAux___redArg___lam__2 as *mut core::ffi::c_void,
                3,
                2,
            );
            crate::leanh::lean_closure_set(v___f_3569_, 0, v_key_3567_);
            crate::leanh::lean_closure_set(v___f_3569_, 1, v_toPure_3561_);
            v___x_3570_ = crate::leanh::lean_apply_1(v_f_3562_, v_val_3568_);
            v___x_3571_ = crate::leanh::lean_apply_4(
                v_toBind_3563_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_3570_,
                v___f_3569_,
            );
            return v___x_3571_;
        }
        1 => {
            let mut v_node_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toPure_3561_);
            v_node_3572_ = crate::leanh::lean_ctor_get(v_x_3566_, 0);
            crate::leanh::lean_inc(v_node_3572_);
            crate::leanh::lean_dec_ref_known(v_x_3566_, 1);
            v___x_3573_ =
                l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_3564_, v_f_3562_, v_node_3572_);
            v___x_3574_ = crate::leanh::lean_apply_4(
                v_toBind_3563_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_3573_,
                v___f_3565_,
            );
            return v___x_3574_;
        }
        _ => {
            let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___f_3565_);
            crate::leanh::lean_dec_ref(v_inst_3564_);
            crate::leanh::lean_dec(v_toBind_3563_);
            crate::leanh::lean_dec(v_f_3562_);
            v___x_3575_ = crate::leanh::lean_box(2);
            v___x_3576_ =
                crate::leanh::lean_apply_2(v_toPure_3561_, crate::leanh::lean_box(0), v___x_3575_);
            return v___x_3576_;
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_mapMAux(
    mut v_00_u03b1_3577_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3578_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3579_: *mut crate::leanh::LeanObject,
    mut v_m_3580_: *mut crate::leanh::LeanObject,
    mut v_inst_3581_: *mut crate::leanh::LeanObject,
    mut v_f_3582_: *mut crate::leanh::LeanObject,
    mut v_n_3583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3584_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_3581_, v_f_3582_, v_n_3583_);
    return v___x_3584_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapM___redArg___lam__0(
    mut v_toPure_3585_: *mut crate::leanh::LeanObject,
    mut v_root_3586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3587_ =
        crate::leanh::lean_apply_2(v_toPure_3585_, crate::leanh::lean_box(0), v_root_3586_);
    return v___x_3587_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapM___redArg(
    mut v_inst_3588_: *mut crate::leanh::LeanObject,
    mut v_pm_3589_: *mut crate::leanh::LeanObject,
    mut v_f_3590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3591_ = crate::leanh::lean_ctor_get(v_inst_3588_, 0);
    v_toBind_3592_ = crate::leanh::lean_ctor_get(v_inst_3588_, 1);
    crate::leanh::lean_inc(v_toBind_3592_);
    v_toPure_3593_ = crate::leanh::lean_ctor_get(v_toApplicative_3591_, 1);
    crate::leanh::lean_inc(v_toPure_3593_);
    v___x_3594_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_3588_, v_f_3590_, v_pm_3589_);
    v___f_3595_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashMap_mapM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3595_, 0, v_toPure_3593_);
    v___x_3596_ = crate::leanh::lean_apply_4(
        v_toBind_3592_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3594_,
        v___f_3595_,
    );
    return v___x_3596_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapM(
    mut v_00_u03b1_3597_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3598_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3599_: *mut crate::leanh::LeanObject,
    mut v_m_3600_: *mut crate::leanh::LeanObject,
    mut v_inst_3601_: *mut crate::leanh::LeanObject,
    mut v_x_3602_: *mut crate::leanh::LeanObject,
    mut v_x_3603_: *mut crate::leanh::LeanObject,
    mut v_pm_3604_: *mut crate::leanh::LeanObject,
    mut v_f_3605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3606_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_3601_, v_pm_3604_, v_f_3605_);
    return v___x_3606_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapM___boxed(
    mut v_00_u03b1_3607_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3608_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3609_: *mut crate::leanh::LeanObject,
    mut v_m_3610_: *mut crate::leanh::LeanObject,
    mut v_inst_3611_: *mut crate::leanh::LeanObject,
    mut v_x_3612_: *mut crate::leanh::LeanObject,
    mut v_x_3613_: *mut crate::leanh::LeanObject,
    mut v_pm_3614_: *mut crate::leanh::LeanObject,
    mut v_f_3615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3616_ = l_Lean_PersistentHashMap_mapM(
        v_00_u03b1_3607_,
        v_00_u03b2_3608_,
        v_00_u03c3_3609_,
        v_m_3610_,
        v_inst_3611_,
        v_x_3612_,
        v_x_3613_,
        v_pm_3614_,
        v_f_3615_,
    );
    crate::leanh::lean_dec_ref(v_x_3613_);
    crate::leanh::lean_dec_ref(v_x_3612_);
    return v_res_3616_;
}
pub unsafe fn l_Lean_PersistentHashMap_map___redArg___lam__0(
    mut v_f_3617_: *mut crate::leanh::LeanObject,
    mut v_x_3618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3619_ = crate::leanh::lean_apply_1(v_f_3617_, v_x_3618_);
    return v___x_3619_;
}
pub unsafe fn l_Lean_PersistentHashMap_map___redArg(
    mut v_pm_3620_: *mut crate::leanh::LeanObject,
    mut v_f_3621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3622_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashMap_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3622_, 0, v_f_3621_);
    v___x_3623_ = l_Lean_PersistentHashMap_foldl___redArg___closed__9;
    v___x_3624_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_3623_, v_pm_3620_, v___f_3622_);
    return v___x_3624_;
}
pub unsafe fn l_Lean_PersistentHashMap_map(
    mut v_00_u03b1_3625_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3626_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3627_: *mut crate::leanh::LeanObject,
    mut v_x_3628_: *mut crate::leanh::LeanObject,
    mut v_x_3629_: *mut crate::leanh::LeanObject,
    mut v_pm_3630_: *mut crate::leanh::LeanObject,
    mut v_f_3631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3632_ = l_Lean_PersistentHashMap_map___redArg(v_pm_3630_, v_f_3631_);
    return v___x_3632_;
}
pub unsafe fn l_Lean_PersistentHashMap_map___boxed(
    mut v_00_u03b1_3633_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3634_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3635_: *mut crate::leanh::LeanObject,
    mut v_x_3636_: *mut crate::leanh::LeanObject,
    mut v_x_3637_: *mut crate::leanh::LeanObject,
    mut v_pm_3638_: *mut crate::leanh::LeanObject,
    mut v_f_3639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3640_ = l_Lean_PersistentHashMap_map(
        v_00_u03b1_3633_,
        v_00_u03b2_3634_,
        v_00_u03c3_3635_,
        v_x_3636_,
        v_x_3637_,
        v_pm_3638_,
        v_f_3639_,
    );
    crate::leanh::lean_dec_ref(v_x_3637_);
    crate::leanh::lean_dec_ref(v_x_3636_);
    return v_res_3640_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___redArg___lam__0(
    mut v_ps_3641_: *mut crate::leanh::LeanObject,
    mut v_k_3642_: *mut crate::leanh::LeanObject,
    mut v_v_3643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3644_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3644_, 0, v_k_3642_);
    crate::leanh::lean_ctor_set(v___x_3644_, 1, v_v_3643_);
    v___x_3645_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3645_, 0, v___x_3644_);
    crate::leanh::lean_ctor_set(v___x_3645_, 1, v_ps_3641_);
    return v___x_3645_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___redArg(
    mut v_m_3647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3648_ = l_Lean_PersistentHashMap_toList___redArg___closed__0;
    v___x_3649_ = crate::leanh::lean_box(0);
    v___x_3650_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_3647_, v___f_3648_, v___x_3649_);
    return v___x_3650_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList(
    mut v_00_u03b1_3651_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3652_: *mut crate::leanh::LeanObject,
    mut v_x_3653_: *mut crate::leanh::LeanObject,
    mut v_x_3654_: *mut crate::leanh::LeanObject,
    mut v_m_3655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3656_ = l_Lean_PersistentHashMap_toList___redArg(v_m_3655_);
    return v___x_3656_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___boxed(
    mut v_00_u03b1_3657_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3658_: *mut crate::leanh::LeanObject,
    mut v_x_3659_: *mut crate::leanh::LeanObject,
    mut v_x_3660_: *mut crate::leanh::LeanObject,
    mut v_m_3661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3662_ = l_Lean_PersistentHashMap_toList(
        v_00_u03b1_3657_,
        v_00_u03b2_3658_,
        v_x_3659_,
        v_x_3660_,
        v_m_3661_,
    );
    crate::leanh::lean_dec_ref(v_x_3660_);
    crate::leanh::lean_dec_ref(v_x_3659_);
    return v_res_3662_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___redArg___lam__0(
    mut v_ps_3663_: *mut crate::leanh::LeanObject,
    mut v_k_3664_: *mut crate::leanh::LeanObject,
    mut v_v_3665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3666_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3666_, 0, v_k_3664_);
    crate::leanh::lean_ctor_set(v___x_3666_, 1, v_v_3665_);
    v___x_3667_ = lean_array_push(v_ps_3663_, v___x_3666_);
    return v___x_3667_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___redArg(
    mut v_m_3671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3672_ = l_Lean_PersistentHashMap_toArray___redArg___closed__0;
    v___x_3673_ = l_Lean_PersistentHashMap_toArray___redArg___closed__1;
    v___x_3674_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_3671_, v___f_3672_, v___x_3673_);
    return v___x_3674_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray(
    mut v_00_u03b1_3675_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3676_: *mut crate::leanh::LeanObject,
    mut v_x_3677_: *mut crate::leanh::LeanObject,
    mut v_x_3678_: *mut crate::leanh::LeanObject,
    mut v_m_3679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3680_ = l_Lean_PersistentHashMap_toArray___redArg(v_m_3679_);
    return v___x_3680_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___boxed(
    mut v_00_u03b1_3681_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3682_: *mut crate::leanh::LeanObject,
    mut v_x_3683_: *mut crate::leanh::LeanObject,
    mut v_x_3684_: *mut crate::leanh::LeanObject,
    mut v_m_3685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3686_ = l_Lean_PersistentHashMap_toArray(
        v_00_u03b1_3681_,
        v_00_u03b2_3682_,
        v_x_3683_,
        v_x_3684_,
        v_m_3685_,
    );
    crate::leanh::lean_dec_ref(v_x_3684_);
    crate::leanh::lean_dec_ref(v_x_3683_);
    return v_res_3686_;
}
pub unsafe fn l_Lean_PersistentHashMap_collectStats___redArg(
    mut v_x_3687_: *mut crate::leanh::LeanObject,
    mut v_x_3688_: *mut crate::leanh::LeanObject,
    mut v_x_3689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNodes_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNull_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCollisions_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxDepth_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3697_: u8 = 0;
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stats_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: u8 = 0;
    let mut v___x_3707_: u8 = 0;
    let mut v___x_3708_: usize = 0;
    let mut v___x_3709_: usize = 0;
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: usize = 0;
    let mut v___x_3712_: usize = 0;
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: u8 = 0;
    let mut v_isSharedCheck_3716_: u8 = 0;
    let mut v_ks_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNodes_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNull_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCollisions_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxDepth_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: u8 = 0;
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3687_) == 0 {
                    v_es_3690_ = crate::leanh::lean_ctor_get(v_x_3687_, 0);
                    v_numNodes_3691_ = crate::leanh::lean_ctor_get(v_x_3688_, 0);
                    v_numNull_3692_ = crate::leanh::lean_ctor_get(v_x_3688_, 1);
                    v_numCollisions_3693_ = crate::leanh::lean_ctor_get(v_x_3688_, 2);
                    v_maxDepth_3694_ = crate::leanh::lean_ctor_get(v_x_3688_, 3);
                    v_isSharedCheck_3716_ = (!crate::leanh::lean_is_exclusive(v_x_3688_)) as u8;
                    if v_isSharedCheck_3716_ == 0 {
                        v___x_3696_ = v_x_3688_;
                        v_isShared_3697_ = v_isSharedCheck_3716_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_maxDepth_3694_);
                        crate::leanh::lean_inc(v_numCollisions_3693_);
                        crate::leanh::lean_inc(v_numNull_3692_);
                        crate::leanh::lean_inc(v_numNodes_3691_);
                        crate::leanh::lean_dec(v_x_3688_);
                        v___x_3696_ = crate::leanh::lean_box(0);
                        v_isShared_3697_ = v_isSharedCheck_3716_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_3717_ = crate::leanh::lean_ctor_get(v_x_3687_, 0);
                    v_numNodes_3718_ = crate::leanh::lean_ctor_get(v_x_3688_, 0);
                    v_numNull_3719_ = crate::leanh::lean_ctor_get(v_x_3688_, 1);
                    v_numCollisions_3720_ = crate::leanh::lean_ctor_get(v_x_3688_, 2);
                    v_maxDepth_3721_ = crate::leanh::lean_ctor_get(v_x_3688_, 3);
                    v_isSharedCheck_3737_ = (!crate::leanh::lean_is_exclusive(v_x_3688_)) as u8;
                    if v_isSharedCheck_3737_ == 0 {
                        v___x_3723_ = v_x_3688_;
                        v_isShared_3724_ = v_isSharedCheck_3737_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_maxDepth_3721_);
                        crate::leanh::lean_inc(v_numCollisions_3720_);
                        crate::leanh::lean_inc(v_numNull_3719_);
                        crate::leanh::lean_inc(v_numNodes_3718_);
                        crate::leanh::lean_dec(v_x_3688_);
                        v___x_3723_ = crate::leanh::lean_box(0);
                        v_isShared_3724_ = v_isSharedCheck_3737_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3698_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3699_ = lean_nat_add(v_numNodes_3691_, v___x_3698_);
                crate::leanh::lean_dec(v_numNodes_3691_);
                v___x_3715_ = lean_nat_dec_le(v_maxDepth_3694_, v_x_3689_);
                if v___x_3715_ == 0 {
                    v___y_3701_ = v_maxDepth_3694_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_maxDepth_3694_);
                    crate::leanh::lean_inc(v_x_3689_);
                    v___y_3701_ = v_x_3689_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3697_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3696_, 3, v___y_3701_);
                    crate::leanh::lean_ctor_set(v___x_3696_, 0, v___x_3699_);
                    v_stats_3703_ = v___x_3696_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3714_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3714_, 1, v_numNull_3692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3714_, 2, v_numCollisions_3693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3714_, 3, v___y_3701_);
                    v_stats_3703_ = v_reuseFailAlloc_3714_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3704_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3705_ = lean_array_get_size(v_es_3690_);
                v___x_3706_ = lean_nat_dec_lt(v___x_3704_, v___x_3705_);
                if v___x_3706_ == 0 {
                    crate::leanh::lean_dec(v_x_3689_);
                    return v_stats_3703_;
                } else {
                    v___x_3707_ = lean_nat_dec_le(v___x_3705_, v___x_3705_);
                    if v___x_3707_ == 0 {
                        if v___x_3706_ == 0 {
                            crate::leanh::lean_dec(v_x_3689_);
                            return v_stats_3703_;
                        } else {
                            v___x_3708_ = 0usize;
                            v___x_3709_ = lean_usize_of_nat(v___x_3705_);
                            v___x_3710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_3689_, v_es_3690_, v___x_3708_, v___x_3709_, v_stats_3703_);
                            crate::leanh::lean_dec(v_x_3689_);
                            return v___x_3710_;
                        }
                    } else {
                        v___x_3711_ = 0usize;
                        v___x_3712_ = lean_usize_of_nat(v___x_3705_);
                        v___x_3713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_3689_, v_es_3690_, v___x_3711_, v___x_3712_, v_stats_3703_);
                        crate::leanh::lean_dec(v_x_3689_);
                        return v___x_3713_;
                    }
                }
            }
            4 => {
                v___x_3725_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3726_ = lean_nat_add(v_numNodes_3718_, v___x_3725_);
                crate::leanh::lean_dec(v_numNodes_3718_);
                v___x_3727_ = lean_array_get_size(v_ks_3717_);
                v___x_3728_ = lean_nat_add(v_numCollisions_3720_, v___x_3727_);
                crate::leanh::lean_dec(v_numCollisions_3720_);
                v___x_3729_ = lean_nat_sub(v___x_3728_, v___x_3725_);
                crate::leanh::lean_dec(v___x_3728_);
                v___x_3730_ = lean_nat_dec_le(v_maxDepth_3721_, v_x_3689_);
                if v___x_3730_ == 0 {
                    crate::leanh::lean_dec(v_x_3689_);
                    if v_isShared_3724_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3723_, 2, v___x_3729_);
                        crate::leanh::lean_ctor_set(v___x_3723_, 0, v___x_3726_);
                        v___x_3732_ = v___x_3723_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3733_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3726_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_numNull_3719_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3733_, 2, v___x_3729_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3733_, 3, v_maxDepth_3721_);
                        v___x_3732_ = v_reuseFailAlloc_3733_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_maxDepth_3721_);
                    if v_isShared_3724_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3723_, 3, v_x_3689_);
                        crate::leanh::lean_ctor_set(v___x_3723_, 2, v___x_3729_);
                        crate::leanh::lean_ctor_set(v___x_3723_, 0, v___x_3726_);
                        v___x_3735_ = v___x_3723_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3736_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3726_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3736_, 1, v_numNull_3719_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3736_, 2, v___x_3729_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3736_, 3, v_x_3689_);
                        v___x_3735_ = v_reuseFailAlloc_3736_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_3732_;
            }
            6 => {
                return v___x_3735_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(
    mut v_x_3738_: *mut crate::leanh::LeanObject,
    mut v_as_3739_: *mut crate::leanh::LeanObject,
    mut v_i_3740_: usize,
    mut v_stop_3741_: usize,
    mut v_b_3742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: usize = 0;
    let mut v___x_3746_: usize = 0;
    let mut v___x_3748_: u8 = 0;
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNodes_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNull_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCollisions_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxDepth_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3760_: u8 = 0;
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3765_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3748_ = lean_usize_dec_eq(v_i_3740_, v_stop_3741_);
                if v___x_3748_ == 0 {
                    v___x_3749_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3750_ = lean_array_uget_borrowed(v_as_3739_, v_i_3740_);
                    match crate::leanh::lean_obj_tag(v___x_3750_) {
                        0 => {
                            v___y_3744_ = v_b_3742_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_3751_ = crate::leanh::lean_ctor_get(v___x_3750_, 0);
                            v___x_3752_ = lean_nat_add(v_x_3738_, v___x_3749_);
                            v___x_3753_ = l_Lean_PersistentHashMap_collectStats___redArg(
                                v_node_3751_,
                                v_b_3742_,
                                v___x_3752_,
                            );
                            v___y_3744_ = v___x_3753_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_numNodes_3754_ = crate::leanh::lean_ctor_get(v_b_3742_, 0);
                            v_numNull_3755_ = crate::leanh::lean_ctor_get(v_b_3742_, 1);
                            v_numCollisions_3756_ = crate::leanh::lean_ctor_get(v_b_3742_, 2);
                            v_maxDepth_3757_ = crate::leanh::lean_ctor_get(v_b_3742_, 3);
                            v_isSharedCheck_3765_ =
                                (!crate::leanh::lean_is_exclusive(v_b_3742_)) as u8;
                            if v_isSharedCheck_3765_ == 0 {
                                v___x_3759_ = v_b_3742_;
                                v_isShared_3760_ = v_isSharedCheck_3765_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_maxDepth_3757_);
                                crate::leanh::lean_inc(v_numCollisions_3756_);
                                crate::leanh::lean_inc(v_numNull_3755_);
                                crate::leanh::lean_inc(v_numNodes_3754_);
                                crate::leanh::lean_dec(v_b_3742_);
                                v___x_3759_ = crate::leanh::lean_box(0);
                                v_isShared_3760_ = v_isSharedCheck_3765_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    return v_b_3742_;
                }
            }
            1 => {
                v___x_3745_ = 1usize;
                v___x_3746_ = lean_usize_add(v_i_3740_, v___x_3745_);
                v_i_3740_ = v___x_3746_;
                v_b_3742_ = v___y_3744_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3761_ = lean_nat_add(v_numNull_3755_, v___x_3749_);
                crate::leanh::lean_dec(v_numNull_3755_);
                if v_isShared_3760_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3759_, 1, v___x_3761_);
                    v___x_3763_ = v___x_3759_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3764_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_numNodes_3754_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3764_, 1, v___x_3761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3764_, 2, v_numCollisions_3756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3764_, 3, v_maxDepth_3757_);
                    v___x_3763_ = v_reuseFailAlloc_3764_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_3744_ = v___x_3763_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg___boxed(
    mut v_x_3766_: *mut crate::leanh::LeanObject,
    mut v_as_3767_: *mut crate::leanh::LeanObject,
    mut v_i_3768_: *mut crate::leanh::LeanObject,
    mut v_stop_3769_: *mut crate::leanh::LeanObject,
    mut v_b_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3771_: usize = 0;
    let mut v_stop_boxed_3772_: usize = 0;
    let mut v_res_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3771_ = crate::leanh::lean_unbox_usize(v_i_3768_);
    crate::leanh::lean_dec(v_i_3768_);
    v_stop_boxed_3772_ = crate::leanh::lean_unbox_usize(v_stop_3769_);
    crate::leanh::lean_dec(v_stop_3769_);
    v_res_3773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_3766_, v_as_3767_, v_i_boxed_3771_, v_stop_boxed_3772_, v_b_3770_);
    crate::leanh::lean_dec_ref(v_as_3767_);
    crate::leanh::lean_dec(v_x_3766_);
    return v_res_3773_;
}
pub unsafe fn l_Lean_PersistentHashMap_collectStats___redArg___boxed(
    mut v_x_3774_: *mut crate::leanh::LeanObject,
    mut v_x_3775_: *mut crate::leanh::LeanObject,
    mut v_x_3776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3777_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_3774_, v_x_3775_, v_x_3776_);
    crate::leanh::lean_dec_ref(v_x_3774_);
    return v_res_3777_;
}
pub unsafe fn l_Lean_PersistentHashMap_collectStats(
    mut v_00_u03b1_3778_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3779_: *mut crate::leanh::LeanObject,
    mut v_x_3780_: *mut crate::leanh::LeanObject,
    mut v_x_3781_: *mut crate::leanh::LeanObject,
    mut v_x_3782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3783_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_3780_, v_x_3781_, v_x_3782_);
    return v___x_3783_;
}
pub unsafe fn l_Lean_PersistentHashMap_collectStats___boxed(
    mut v_00_u03b1_3784_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3785_: *mut crate::leanh::LeanObject,
    mut v_x_3786_: *mut crate::leanh::LeanObject,
    mut v_x_3787_: *mut crate::leanh::LeanObject,
    mut v_x_3788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3789_ = l_Lean_PersistentHashMap_collectStats(
        v_00_u03b1_3784_,
        v_00_u03b2_3785_,
        v_x_3786_,
        v_x_3787_,
        v_x_3788_,
    );
    crate::leanh::lean_dec_ref(v_x_3786_);
    return v_res_3789_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(
    mut v_00_u03b1_3790_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3791_: *mut crate::leanh::LeanObject,
    mut v_x_3792_: *mut crate::leanh::LeanObject,
    mut v_as_3793_: *mut crate::leanh::LeanObject,
    mut v_i_3794_: usize,
    mut v_stop_3795_: usize,
    mut v_b_3796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_3792_, v_as_3793_, v_i_3794_, v_stop_3795_, v_b_3796_);
    return v___x_3797_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___boxed(
    mut v_00_u03b1_3798_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3799_: *mut crate::leanh::LeanObject,
    mut v_x_3800_: *mut crate::leanh::LeanObject,
    mut v_as_3801_: *mut crate::leanh::LeanObject,
    mut v_i_3802_: *mut crate::leanh::LeanObject,
    mut v_stop_3803_: *mut crate::leanh::LeanObject,
    mut v_b_3804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3805_: usize = 0;
    let mut v_stop_boxed_3806_: usize = 0;
    let mut v_res_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3805_ = crate::leanh::lean_unbox_usize(v_i_3802_);
    crate::leanh::lean_dec(v_i_3802_);
    v_stop_boxed_3806_ = crate::leanh::lean_unbox_usize(v_stop_3803_);
    crate::leanh::lean_dec(v_stop_3803_);
    v_res_3807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(v_00_u03b1_3798_, v_00_u03b2_3799_, v_x_3800_, v_as_3801_, v_i_boxed_3805_, v_stop_boxed_3806_, v_b_3804_);
    crate::leanh::lean_dec_ref(v_as_3801_);
    crate::leanh::lean_dec(v_x_3800_);
    return v_res_3807_;
}
pub unsafe fn l_Lean_PersistentHashMap_stats___redArg(
    mut v_m_3810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3811_ = l_Lean_PersistentHashMap_stats___redArg___closed__0;
    v___x_3812_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3813_ =
        l_Lean_PersistentHashMap_collectStats___redArg(v_m_3810_, v___x_3811_, v___x_3812_);
    return v___x_3813_;
}
pub unsafe fn l_Lean_PersistentHashMap_stats___redArg___boxed(
    mut v_m_3814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3815_ = l_Lean_PersistentHashMap_stats___redArg(v_m_3814_);
    crate::leanh::lean_dec_ref(v_m_3814_);
    return v_res_3815_;
}
pub unsafe fn l_Lean_PersistentHashMap_stats(
    mut v_00_u03b1_3816_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3817_: *mut crate::leanh::LeanObject,
    mut v_x_3818_: *mut crate::leanh::LeanObject,
    mut v_x_3819_: *mut crate::leanh::LeanObject,
    mut v_m_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3821_ = l_Lean_PersistentHashMap_stats___redArg(v_m_3820_);
    return v___x_3821_;
}
pub unsafe fn l_Lean_PersistentHashMap_stats___boxed(
    mut v_00_u03b1_3822_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3823_: *mut crate::leanh::LeanObject,
    mut v_x_3824_: *mut crate::leanh::LeanObject,
    mut v_x_3825_: *mut crate::leanh::LeanObject,
    mut v_m_3826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3827_ = l_Lean_PersistentHashMap_stats(
        v_00_u03b1_3822_,
        v_00_u03b2_3823_,
        v_x_3824_,
        v_x_3825_,
        v_m_3826_,
    );
    crate::leanh::lean_dec_ref(v_m_3826_);
    crate::leanh::lean_dec_ref(v_x_3825_);
    crate::leanh::lean_dec_ref(v_x_3824_);
    return v_res_3827_;
}
pub unsafe fn l_Lean_PersistentHashMap_Stats_toString(
    mut v_s_3833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numNodes_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNull_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCollisions_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxDepth_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_numNodes_3834_ = crate::leanh::lean_ctor_get(v_s_3833_, 0);
    crate::leanh::lean_inc(v_numNodes_3834_);
    v_numNull_3835_ = crate::leanh::lean_ctor_get(v_s_3833_, 1);
    crate::leanh::lean_inc(v_numNull_3835_);
    v_numCollisions_3836_ = crate::leanh::lean_ctor_get(v_s_3833_, 2);
    crate::leanh::lean_inc(v_numCollisions_3836_);
    v_maxDepth_3837_ = crate::leanh::lean_ctor_get(v_s_3833_, 3);
    crate::leanh::lean_inc(v_maxDepth_3837_);
    crate::leanh::lean_dec_ref(v_s_3833_);
    v___x_3838_ = l_Lean_PersistentHashMap_Stats_toString___closed__0;
    v___x_3839_ = l_Nat_reprFast(v_numNodes_3834_);
    v___x_3840_ = lean_string_append(v___x_3838_, v___x_3839_);
    crate::leanh::lean_dec_ref(v___x_3839_);
    v___x_3841_ = l_Lean_PersistentHashMap_Stats_toString___closed__1;
    v___x_3842_ = lean_string_append(v___x_3840_, v___x_3841_);
    v___x_3843_ = l_Nat_reprFast(v_numNull_3835_);
    v___x_3844_ = lean_string_append(v___x_3842_, v___x_3843_);
    crate::leanh::lean_dec_ref(v___x_3843_);
    v___x_3845_ = l_Lean_PersistentHashMap_Stats_toString___closed__2;
    v___x_3846_ = lean_string_append(v___x_3844_, v___x_3845_);
    v___x_3847_ = l_Nat_reprFast(v_numCollisions_3836_);
    v___x_3848_ = lean_string_append(v___x_3846_, v___x_3847_);
    crate::leanh::lean_dec_ref(v___x_3847_);
    v___x_3849_ = l_Lean_PersistentHashMap_Stats_toString___closed__3;
    v___x_3850_ = lean_string_append(v___x_3848_, v___x_3849_);
    v___x_3851_ = l_Nat_reprFast(v_maxDepth_3837_);
    v___x_3852_ = lean_string_append(v___x_3850_, v___x_3851_);
    crate::leanh::lean_dec_ref(v___x_3851_);
    v___x_3853_ = l_Lean_PersistentHashMap_Stats_toString___closed__4;
    v___x_3854_ = lean_string_append(v___x_3852_, v___x_3853_);
    return v___x_3854_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_PersistentHashMap(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Except(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_PersistentHashMap_shift = _init_l_Lean_PersistentHashMap_shift();
    l_Lean_PersistentHashMap_branching = _init_l_Lean_PersistentHashMap_branching();
    l_Lean_PersistentHashMap_maxDepth = _init_l_Lean_PersistentHashMap_maxDepth();
    l_Lean_PersistentHashMap_maxCollisions = _init_l_Lean_PersistentHashMap_maxCollisions();
    crate::leanh::lean_mark_persistent(l_Lean_PersistentHashMap_maxCollisions);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_PersistentHashMap(
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
pub unsafe fn initialize_Lean_Data_PersistentHashMap(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Except(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentHashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_PersistentHashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_PersistentHashMap(builtin);
}
