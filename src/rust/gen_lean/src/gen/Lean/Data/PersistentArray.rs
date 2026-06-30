// Lean compiler output
// Module: Lean.Data.PersistentArray
// Imports: Init.Data.Nat.Fold Init.Data.UInt.Basic Init.Data.String.Defs Init.Data.ToString.Macro Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_pop, lean_array_push, lean_array_set,
    lean_array_size, lean_array_uget_borrowed, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_pow, lean_nat_shiftr, lean_nat_sub,
    lean_string_append, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land,
    lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any,
    l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find,
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Nat::Fold::{
    initialize_Init_Data_Nat_Fold, runtime_initialize_Init_Data_Nat_Fold,
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
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_System_Platform_numBits;
pub static l_Lean_instInhabitedPersistentArrayNode_default___closed__0_value:
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
static mut l_Lean_instInhabitedPersistentArrayNode_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPersistentArrayNode_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instInhabitedPersistentArrayNode_default___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instInhabitedPersistentArrayNode_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedPersistentArrayNode_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPersistentArrayNode_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instInhabitedPersistentArrayNode___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedPersistentArrayNode___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_PersistentArray_initShift: usize = 0;
pub static mut l_Lean_PersistentArray_branching: usize = 0;
static mut l_Lean_instInhabitedPersistentArray_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedPersistentArray_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedPersistentArray_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedPersistentArray_default___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedPersistentArray___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedPersistentArray___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentArray_mkNewPath___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PersistentArray_mkNewPath___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PersistentArray_mkNewTail___redArg___closed__0_value:
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
static mut l_Lean_PersistentArray_mkNewTail___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_mkNewTail___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PersistentArray_mkNewTail___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PersistentArray_mkNewTail___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentArray_tooBig___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PersistentArray_tooBig___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentArray_tooBig___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PersistentArray_tooBig___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_PersistentArray_tooBig: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentArray_popLeaf___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PersistentArray_popLeaf___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentArray_popLeaf___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PersistentArray_popLeaf___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PersistentArray_findSomeMAux___redArg___closed__0_value:
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
static mut l_Lean_PersistentArray_findSomeMAux___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__0_value:
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
static mut l_Lean_PersistentArray_foldl___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__1_value:
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
static mut l_Lean_PersistentArray_foldl___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__2_value:
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
static mut l_Lean_PersistentArray_foldl___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__3_value:
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
static mut l_Lean_PersistentArray_foldl___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__4_value:
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
static mut l_Lean_PersistentArray_foldl___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__5_value:
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
static mut l_Lean_PersistentArray_foldl___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__6_value:
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
static mut l_Lean_PersistentArray_foldl___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__7_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_PersistentArray_foldl___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__8_value: leanh::LeanCtorObject<
    5,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_PersistentArray_foldl___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__9_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_PersistentArray_foldl___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_instAppend___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PersistentArray_append___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_PersistentArray_instAppend___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_instAppend___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_mapMAux___redArg___closed__0_value:
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
    m_fun: l_Lean_PersistentArray_mapMAux___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentArray_mapMAux___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_mapMAux___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_mapMAux___redArg___closed__1_value:
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
    m_fun: l_Lean_PersistentArray_mapMAux___redArg___lam__2 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentArray_mapMAux___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_mapMAux___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_Stats_toString___closed__0_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [123, 110, 111, 100, 101, 115, 32, 58, 61, 32, 0],
};
static mut l_Lean_PersistentArray_Stats_toString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_Stats_toString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_Stats_toString___closed__1_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_PersistentArray_Stats_toString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_Stats_toString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_Stats_toString___closed__2_value: leanh::LeanStringObject<
    16,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        44, 32, 116, 97, 105, 108, 32, 115, 105, 122, 101, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_PersistentArray_Stats_toString___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_Stats_toString___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_Stats_toString___closed__3_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_PersistentArray_Stats_toString___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_Stats_toString___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PersistentArray_instToStringStats___closed__0_value:
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
    m_fun: l_Lean_PersistentArray_Stats_toString as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentArray_instToStringStats___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_instToStringStats___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_PersistentArray_instToStringStats: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_instToStringStats___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkPersistentArray___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkPersistentArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_PersistentArrayNode_ctorIdx___redArg(
    mut v_x_3047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3047_) == 0 {
        let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3048_ = leanh::lean_unsigned_to_nat(0);
        return v___x_3048_;
    } else {
        let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3049_ = leanh::lean_unsigned_to_nat(1);
        return v___x_3049_;
    }
}
pub unsafe fn l_Lean_PersistentArrayNode_ctorIdx___redArg___boxed(
    mut v_x_3050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3051_ = l_Lean_PersistentArrayNode_ctorIdx___redArg(v_x_3050_);
    leanh::lean_dec_ref(v_x_3050_);
    return v_res_3051_;
}
pub unsafe fn l_Lean_PersistentArrayNode_ctorIdx(
    mut v_00_u03b1_3052_: *mut leanh::LeanObject,
    mut v_x_3053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3054_ = l_Lean_PersistentArrayNode_ctorIdx___redArg(v_x_3053_);
    return v___x_3054_;
}
pub unsafe fn l_Lean_PersistentArrayNode_ctorIdx___boxed(
    mut v_00_u03b1_3055_: *mut leanh::LeanObject,
    mut v_x_3056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3057_ = l_Lean_PersistentArrayNode_ctorIdx(v_00_u03b1_3055_, v_x_3056_);
    leanh::lean_dec_ref(v_x_3056_);
    return v_res_3057_;
}
pub unsafe fn l_Lean_PersistentArrayNode_ctorElim___redArg(
    mut v_t_3058_: *mut leanh::LeanObject,
    mut v_k_3059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cs_3060_ = leanh::lean_ctor_get(v_t_3058_, 0);
    leanh::lean_inc_ref(v_cs_3060_);
    leanh::lean_dec_ref(v_t_3058_);
    v___x_3061_ = leanh::lean_apply_1(v_k_3059_, v_cs_3060_);
    return v___x_3061_;
}
pub unsafe fn l_Lean_PersistentArrayNode_ctorElim(
    mut v_00_u03b1_3062_: *mut leanh::LeanObject,
    mut v_motive__1_3063_: *mut leanh::LeanObject,
    mut v_ctorIdx_3064_: *mut leanh::LeanObject,
    mut v_t_3065_: *mut leanh::LeanObject,
    mut v_h_3066_: *mut leanh::LeanObject,
    mut v_k_3067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3068_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_3065_, v_k_3067_);
    return v___x_3068_;
}
pub unsafe fn l_Lean_PersistentArrayNode_ctorElim___boxed(
    mut v_00_u03b1_3069_: *mut leanh::LeanObject,
    mut v_motive__1_3070_: *mut leanh::LeanObject,
    mut v_ctorIdx_3071_: *mut leanh::LeanObject,
    mut v_t_3072_: *mut leanh::LeanObject,
    mut v_h_3073_: *mut leanh::LeanObject,
    mut v_k_3074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3075_ = l_Lean_PersistentArrayNode_ctorElim(
        v_00_u03b1_3069_,
        v_motive__1_3070_,
        v_ctorIdx_3071_,
        v_t_3072_,
        v_h_3073_,
        v_k_3074_,
    );
    leanh::lean_dec(v_ctorIdx_3071_);
    return v_res_3075_;
}
pub unsafe fn l_Lean_PersistentArrayNode_node_elim___redArg(
    mut v_t_3076_: *mut leanh::LeanObject,
    mut v_node_3077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3078_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_3076_, v_node_3077_);
    return v___x_3078_;
}
pub unsafe fn l_Lean_PersistentArrayNode_node_elim(
    mut v_00_u03b1_3079_: *mut leanh::LeanObject,
    mut v_motive__1_3080_: *mut leanh::LeanObject,
    mut v_t_3081_: *mut leanh::LeanObject,
    mut v_h_3082_: *mut leanh::LeanObject,
    mut v_node_3083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3084_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_3081_, v_node_3083_);
    return v___x_3084_;
}
pub unsafe fn l_Lean_PersistentArrayNode_leaf_elim___redArg(
    mut v_t_3085_: *mut leanh::LeanObject,
    mut v_leaf_3086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3087_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_3085_, v_leaf_3086_);
    return v___x_3087_;
}
pub unsafe fn l_Lean_PersistentArrayNode_leaf_elim(
    mut v_00_u03b1_3088_: *mut leanh::LeanObject,
    mut v_motive__1_3089_: *mut leanh::LeanObject,
    mut v_t_3090_: *mut leanh::LeanObject,
    mut v_h_3091_: *mut leanh::LeanObject,
    mut v_leaf_3092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3093_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_3090_, v_leaf_3092_);
    return v___x_3093_;
}
pub unsafe fn l_Lean_instInhabitedPersistentArrayNode_default(
    mut v_00_u03b1_3098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3099_ = l_Lean_instInhabitedPersistentArrayNode_default___closed__1;
    return v___x_3099_;
}
pub unsafe fn _init_l_Lean_instInhabitedPersistentArrayNode___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3100_ = l_Lean_instInhabitedPersistentArrayNode_default(leanh::lean_box(0));
    return v___x_3100_;
}
pub unsafe fn l_Lean_instInhabitedPersistentArrayNode(
    mut v_a_3101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3102_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0_once),
        _init_l_Lean_instInhabitedPersistentArrayNode___closed__0,
    );
    return v___x_3102_;
}
pub unsafe fn l_Lean_PersistentArrayNode_isNode___redArg(
    mut v_x_3103_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_3103_) == 0 {
        let mut v___x_3104_: u8 = 0;
        v___x_3104_ = 1;
        return v___x_3104_;
    } else {
        let mut v___x_3105_: u8 = 0;
        v___x_3105_ = 0;
        return v___x_3105_;
    }
}
pub unsafe fn l_Lean_PersistentArrayNode_isNode___redArg___boxed(
    mut v_x_3106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3107_: u8 = 0;
    let mut v_r_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3107_ = l_Lean_PersistentArrayNode_isNode___redArg(v_x_3106_);
    leanh::lean_dec_ref(v_x_3106_);
    v_r_3108_ = leanh::lean_box((v_res_3107_) as usize);
    return v_r_3108_;
}
pub unsafe fn l_Lean_PersistentArrayNode_isNode(
    mut v_00_u03b1_3109_: *mut leanh::LeanObject,
    mut v_x_3110_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3111_: u8 = 0;
    v___x_3111_ = l_Lean_PersistentArrayNode_isNode___redArg(v_x_3110_);
    return v___x_3111_;
}
pub unsafe fn l_Lean_PersistentArrayNode_isNode___boxed(
    mut v_00_u03b1_3112_: *mut leanh::LeanObject,
    mut v_x_3113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3114_: u8 = 0;
    let mut v_r_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3114_ = l_Lean_PersistentArrayNode_isNode(v_00_u03b1_3112_, v_x_3113_);
    leanh::lean_dec_ref(v_x_3113_);
    v_r_3115_ = leanh::lean_box((v_res_3114_) as usize);
    return v_r_3115_;
}
pub unsafe fn _init_l_Lean_PersistentArray_initShift() -> usize {
    let mut v___x_3116_: usize = 0;
    v___x_3116_ = 5usize;
    return v___x_3116_;
}
pub unsafe fn _init_l_Lean_PersistentArray_branching() -> usize {
    let mut v___x_3117_: usize = 0;
    v___x_3117_ = 32usize;
    return v___x_3117_;
}
pub unsafe fn _init_l_Lean_instInhabitedPersistentArray_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3118_ = leanh::lean_unsigned_to_nat(32);
    v___x_3119_ = lean_mk_empty_array_with_capacity(v___x_3118_);
    v___x_3120_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3120_, 0, v___x_3119_);
    return v___x_3120_;
}
pub unsafe fn _init_l_Lean_instInhabitedPersistentArray_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3121_: usize = 0;
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3121_ = 5usize;
    v___x_3122_ = leanh::lean_unsigned_to_nat(0);
    v___x_3123_ = leanh::lean_unsigned_to_nat(32);
    v___x_3124_ = lean_mk_empty_array_with_capacity(v___x_3123_);
    v___x_3125_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__0_once),
        _init_l_Lean_instInhabitedPersistentArray_default___closed__0,
    );
    v___x_3126_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3126_, 0, v___x_3125_);
    leanh::lean_ctor_set(v___x_3126_, 1, v___x_3124_);
    leanh::lean_ctor_set(v___x_3126_, 2, v___x_3122_);
    leanh::lean_ctor_set(v___x_3126_, 3, v___x_3122_);
    leanh::lean_ctor_set_usize(v___x_3126_, 4, v___x_3121_);
    return v___x_3126_;
}
pub unsafe fn l_Lean_instInhabitedPersistentArray_default(
    mut v_00_u03b1_3127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3128_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__1_once),
        _init_l_Lean_instInhabitedPersistentArray_default___closed__1,
    );
    return v___x_3128_;
}
pub unsafe fn _init_l_Lean_instInhabitedPersistentArray___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3129_ = l_Lean_instInhabitedPersistentArray_default(leanh::lean_box(0));
    return v___x_3129_;
}
pub unsafe fn l_Lean_instInhabitedPersistentArray(
    mut v_a_3130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3131_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray___closed__0_once),
        _init_l_Lean_instInhabitedPersistentArray___closed__0,
    );
    return v___x_3131_;
}
pub unsafe fn l_Lean_PersistentArray_empty(
    mut v_00_u03b1_3132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3133_ = leanh::lean_unsigned_to_nat(32);
    v___x_3134_ = lean_mk_empty_array_with_capacity(v___x_3133_);
    leanh::lean_dec_ref(v___x_3134_);
    v___x_3135_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__1_once),
        _init_l_Lean_instInhabitedPersistentArray_default___closed__1,
    );
    return v___x_3135_;
}
pub unsafe fn l_Lean_PersistentArray_isEmpty___redArg(
    mut v_a_3136_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    v_size_3137_ = leanh::lean_ctor_get(v_a_3136_, 2);
    v___x_3138_ = leanh::lean_unsigned_to_nat(0);
    v___x_3139_ = lean_nat_dec_eq(v_size_3137_, v___x_3138_);
    return v___x_3139_;
}
pub unsafe fn l_Lean_PersistentArray_isEmpty___redArg___boxed(
    mut v_a_3140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3141_: u8 = 0;
    let mut v_r_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3141_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_3140_);
    leanh::lean_dec_ref(v_a_3140_);
    v_r_3142_ = leanh::lean_box((v_res_3141_) as usize);
    return v_r_3142_;
}
pub unsafe fn l_Lean_PersistentArray_isEmpty(
    mut v_00_u03b1_3143_: *mut leanh::LeanObject,
    mut v_a_3144_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3145_: u8 = 0;
    v___x_3145_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_3144_);
    return v___x_3145_;
}
pub unsafe fn l_Lean_PersistentArray_isEmpty___boxed(
    mut v_00_u03b1_3146_: *mut leanh::LeanObject,
    mut v_a_3147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3148_: u8 = 0;
    let mut v_r_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3148_ = l_Lean_PersistentArray_isEmpty(v_00_u03b1_3146_, v_a_3147_);
    leanh::lean_dec_ref(v_a_3147_);
    v_r_3149_ = leanh::lean_box((v_res_3148_) as usize);
    return v_r_3149_;
}
pub unsafe fn l_Lean_PersistentArray_mkEmptyArray(
    mut v_00_u03b1_3150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3151_ = leanh::lean_unsigned_to_nat(32);
    v___x_3152_ = lean_mk_empty_array_with_capacity(v___x_3151_);
    return v___x_3152_;
}
pub unsafe fn l_Lean_PersistentArray_mul2Shift(
    mut v_i_3153_: usize,
    mut v_shift_3154_: usize,
) -> usize {
    let mut v___x_3155_: usize = 0;
    v___x_3155_ = lean_usize_shift_left(v_i_3153_, v_shift_3154_);
    return v___x_3155_;
}
pub unsafe fn l_Lean_PersistentArray_mul2Shift___boxed(
    mut v_i_3156_: *mut leanh::LeanObject,
    mut v_shift_3157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3158_: usize = 0;
    let mut v_shift_boxed_3159_: usize = 0;
    let mut v_res_3160_: usize = 0;
    let mut v_r_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3158_ = leanh::lean_unbox_usize(v_i_3156_);
    leanh::lean_dec(v_i_3156_);
    v_shift_boxed_3159_ = leanh::lean_unbox_usize(v_shift_3157_);
    leanh::lean_dec(v_shift_3157_);
    v_res_3160_ = l_Lean_PersistentArray_mul2Shift(v_i_boxed_3158_, v_shift_boxed_3159_);
    v_r_3161_ = leanh::lean_box_usize(v_res_3160_);
    return v_r_3161_;
}
pub unsafe fn l_Lean_PersistentArray_div2Shift(
    mut v_i_3162_: usize,
    mut v_shift_3163_: usize,
) -> usize {
    let mut v___x_3164_: usize = 0;
    v___x_3164_ = lean_usize_shift_right(v_i_3162_, v_shift_3163_);
    return v___x_3164_;
}
pub unsafe fn l_Lean_PersistentArray_div2Shift___boxed(
    mut v_i_3165_: *mut leanh::LeanObject,
    mut v_shift_3166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3167_: usize = 0;
    let mut v_shift_boxed_3168_: usize = 0;
    let mut v_res_3169_: usize = 0;
    let mut v_r_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3167_ = leanh::lean_unbox_usize(v_i_3165_);
    leanh::lean_dec(v_i_3165_);
    v_shift_boxed_3168_ = leanh::lean_unbox_usize(v_shift_3166_);
    leanh::lean_dec(v_shift_3166_);
    v_res_3169_ = l_Lean_PersistentArray_div2Shift(v_i_boxed_3167_, v_shift_boxed_3168_);
    v_r_3170_ = leanh::lean_box_usize(v_res_3169_);
    return v_r_3170_;
}
pub unsafe fn l_Lean_PersistentArray_mod2Shift(
    mut v_i_3171_: usize,
    mut v_shift_3172_: usize,
) -> usize {
    let mut v___x_3173_: usize = 0;
    let mut v___x_3174_: usize = 0;
    let mut v___x_3175_: usize = 0;
    let mut v___x_3176_: usize = 0;
    v___x_3173_ = 1usize;
    v___x_3174_ = lean_usize_shift_left(v___x_3173_, v_shift_3172_);
    v___x_3175_ = lean_usize_sub(v___x_3174_, v___x_3173_);
    v___x_3176_ = lean_usize_land(v_i_3171_, v___x_3175_);
    return v___x_3176_;
}
pub unsafe fn l_Lean_PersistentArray_mod2Shift___boxed(
    mut v_i_3177_: *mut leanh::LeanObject,
    mut v_shift_3178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3179_: usize = 0;
    let mut v_shift_boxed_3180_: usize = 0;
    let mut v_res_3181_: usize = 0;
    let mut v_r_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3179_ = leanh::lean_unbox_usize(v_i_3177_);
    leanh::lean_dec(v_i_3177_);
    v_shift_boxed_3180_ = leanh::lean_unbox_usize(v_shift_3178_);
    leanh::lean_dec(v_shift_3178_);
    v_res_3181_ = l_Lean_PersistentArray_mod2Shift(v_i_boxed_3179_, v_shift_boxed_3180_);
    v_r_3182_ = leanh::lean_box_usize(v_res_3181_);
    return v_r_3182_;
}
pub unsafe fn l_Lean_PersistentArray_getAux___redArg(
    mut v_inst_3183_: *mut leanh::LeanObject,
    mut v_x_3184_: *mut leanh::LeanObject,
    mut v_x_3185_: usize,
    mut v_x_3186_: usize,
) -> *mut leanh::LeanObject {
    let mut v_cs_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: usize = 0;
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: usize = 0;
    let mut v___x_3193_: usize = 0;
    let mut v___x_3194_: usize = 0;
    let mut v___x_3195_: usize = 0;
    let mut v___x_3196_: usize = 0;
    let mut v___x_3197_: usize = 0;
    let mut v_vs_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3184_) == 0 {
                    v_cs_3187_ = leanh::lean_ctor_get(v_x_3184_, 0);
                    v___x_3188_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_instInhabitedPersistentArrayNode___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_instInhabitedPersistentArrayNode___closed__0_once
                        ),
                        _init_l_Lean_instInhabitedPersistentArrayNode___closed__0,
                    );
                    v___x_3189_ = lean_usize_shift_right(v_x_3185_, v_x_3186_);
                    v___x_3190_ = lean_usize_to_nat(v___x_3189_);
                    v___x_3191_ = lean_array_get_borrowed(v___x_3188_, v_cs_3187_, v___x_3190_);
                    leanh::lean_dec(v___x_3190_);
                    v___x_3192_ = 1usize;
                    v___x_3193_ = lean_usize_shift_left(v___x_3192_, v_x_3186_);
                    v___x_3194_ = lean_usize_sub(v___x_3193_, v___x_3192_);
                    v___x_3195_ = lean_usize_land(v_x_3185_, v___x_3194_);
                    v___x_3196_ = 5usize;
                    v___x_3197_ = lean_usize_sub(v_x_3186_, v___x_3196_);
                    v_x_3184_ = v___x_3191_;
                    v_x_3185_ = v___x_3195_;
                    v_x_3186_ = v___x_3197_;
                    state = 0;
                    continue;
                } else {
                    v_vs_3199_ = leanh::lean_ctor_get(v_x_3184_, 0);
                    v___x_3200_ = lean_usize_to_nat(v_x_3185_);
                    v___x_3201_ = lean_array_get_borrowed(v_inst_3183_, v_vs_3199_, v___x_3200_);
                    leanh::lean_dec(v___x_3200_);
                    leanh::lean_inc(v___x_3201_);
                    return v___x_3201_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_getAux___redArg___boxed(
    mut v_inst_3202_: *mut leanh::LeanObject,
    mut v_x_3203_: *mut leanh::LeanObject,
    mut v_x_3204_: *mut leanh::LeanObject,
    mut v_x_3205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_92__boxed_3206_: usize = 0;
    let mut v_x_93__boxed_3207_: usize = 0;
    let mut v_res_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_92__boxed_3206_ = leanh::lean_unbox_usize(v_x_3204_);
    leanh::lean_dec(v_x_3204_);
    v_x_93__boxed_3207_ = leanh::lean_unbox_usize(v_x_3205_);
    leanh::lean_dec(v_x_3205_);
    v_res_3208_ = l_Lean_PersistentArray_getAux___redArg(
        v_inst_3202_,
        v_x_3203_,
        v_x_92__boxed_3206_,
        v_x_93__boxed_3207_,
    );
    leanh::lean_dec_ref(v_x_3203_);
    leanh::lean_dec(v_inst_3202_);
    return v_res_3208_;
}
pub unsafe fn l_Lean_PersistentArray_getAux(
    mut v_00_u03b1_3209_: *mut leanh::LeanObject,
    mut v_inst_3210_: *mut leanh::LeanObject,
    mut v_x_3211_: *mut leanh::LeanObject,
    mut v_x_3212_: usize,
    mut v_x_3213_: usize,
) -> *mut leanh::LeanObject {
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3214_ =
        l_Lean_PersistentArray_getAux___redArg(v_inst_3210_, v_x_3211_, v_x_3212_, v_x_3213_);
    return v___x_3214_;
}
pub unsafe fn l_Lean_PersistentArray_getAux___boxed(
    mut v_00_u03b1_3215_: *mut leanh::LeanObject,
    mut v_inst_3216_: *mut leanh::LeanObject,
    mut v_x_3217_: *mut leanh::LeanObject,
    mut v_x_3218_: *mut leanh::LeanObject,
    mut v_x_3219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_134__boxed_3220_: usize = 0;
    let mut v_x_135__boxed_3221_: usize = 0;
    let mut v_res_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_134__boxed_3220_ = leanh::lean_unbox_usize(v_x_3218_);
    leanh::lean_dec(v_x_3218_);
    v_x_135__boxed_3221_ = leanh::lean_unbox_usize(v_x_3219_);
    leanh::lean_dec(v_x_3219_);
    v_res_3222_ = l_Lean_PersistentArray_getAux(
        v_00_u03b1_3215_,
        v_inst_3216_,
        v_x_3217_,
        v_x_134__boxed_3220_,
        v_x_135__boxed_3221_,
    );
    leanh::lean_dec_ref(v_x_3217_);
    leanh::lean_dec(v_inst_3216_);
    return v_res_3222_;
}
pub unsafe fn l_Lean_PersistentArray_get_x21___redArg(
    mut v_inst_3223_: *mut leanh::LeanObject,
    mut v_t_3224_: *mut leanh::LeanObject,
    mut v_i_3225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_3228_: usize = 0;
    let mut v_tailOff_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: u8 = 0;
    v_root_3226_ = leanh::lean_ctor_get(v_t_3224_, 0);
    v_tail_3227_ = leanh::lean_ctor_get(v_t_3224_, 1);
    v_shift_3228_ = leanh::lean_ctor_get_usize(v_t_3224_, 4);
    v_tailOff_3229_ = leanh::lean_ctor_get(v_t_3224_, 3);
    v___x_3230_ = lean_nat_dec_le(v_tailOff_3229_, v_i_3225_);
    if v___x_3230_ == 0 {
        let mut v___x_3231_: usize = 0;
        let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3231_ = lean_usize_of_nat(v_i_3225_);
        v___x_3232_ = l_Lean_PersistentArray_getAux___redArg(
            v_inst_3223_,
            v_root_3226_,
            v___x_3231_,
            v_shift_3228_,
        );
        return v___x_3232_;
    } else {
        let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3233_ = lean_nat_sub(v_i_3225_, v_tailOff_3229_);
        v___x_3234_ = lean_array_get_borrowed(v_inst_3223_, v_tail_3227_, v___x_3233_);
        leanh::lean_dec(v___x_3233_);
        leanh::lean_inc(v___x_3234_);
        return v___x_3234_;
    }
}
pub unsafe fn l_Lean_PersistentArray_get_x21___redArg___boxed(
    mut v_inst_3235_: *mut leanh::LeanObject,
    mut v_t_3236_: *mut leanh::LeanObject,
    mut v_i_3237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3238_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_3235_, v_t_3236_, v_i_3237_);
    leanh::lean_dec(v_i_3237_);
    leanh::lean_dec_ref(v_t_3236_);
    leanh::lean_dec(v_inst_3235_);
    return v_res_3238_;
}
pub unsafe fn l_Lean_PersistentArray_get_x21(
    mut v_00_u03b1_3239_: *mut leanh::LeanObject,
    mut v_inst_3240_: *mut leanh::LeanObject,
    mut v_t_3241_: *mut leanh::LeanObject,
    mut v_i_3242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3243_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_3240_, v_t_3241_, v_i_3242_);
    return v___x_3243_;
}
pub unsafe fn l_Lean_PersistentArray_get_x21___boxed(
    mut v_00_u03b1_3244_: *mut leanh::LeanObject,
    mut v_inst_3245_: *mut leanh::LeanObject,
    mut v_t_3246_: *mut leanh::LeanObject,
    mut v_i_3247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3248_ =
        l_Lean_PersistentArray_get_x21(v_00_u03b1_3244_, v_inst_3245_, v_t_3246_, v_i_3247_);
    leanh::lean_dec(v_i_3247_);
    leanh::lean_dec_ref(v_t_3246_);
    leanh::lean_dec(v_inst_3245_);
    return v_res_3248_;
}
pub unsafe fn l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(
    mut v_inst_3249_: *mut leanh::LeanObject,
    mut v_xs_3250_: *mut leanh::LeanObject,
    mut v_i_3251_: *mut leanh::LeanObject,
    mut v_x_3252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3253_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_3249_, v_xs_3250_, v_i_3251_);
    return v___x_3253_;
}
pub unsafe fn l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed(
    mut v_inst_3254_: *mut leanh::LeanObject,
    mut v_xs_3255_: *mut leanh::LeanObject,
    mut v_i_3256_: *mut leanh::LeanObject,
    mut v_x_3257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3258_ = l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(
        v_inst_3254_,
        v_xs_3255_,
        v_i_3256_,
        v_x_3257_,
    );
    leanh::lean_dec(v_i_3256_);
    leanh::lean_dec_ref(v_xs_3255_);
    leanh::lean_dec(v_inst_3254_);
    return v_res_3258_;
}
pub unsafe fn l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg(
    mut v_inst_3259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3260_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3260_, 0, v_inst_3259_);
    return v___f_3260_;
}
pub unsafe fn l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited(
    mut v_00_u03b1_3261_: *mut leanh::LeanObject,
    mut v_inst_3262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3263_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3263_, 0, v_inst_3262_);
    return v___f_3263_;
}
pub unsafe fn l_Lean_PersistentArray_setAux___redArg(
    mut v_x_3264_: *mut leanh::LeanObject,
    mut v_x_3265_: usize,
    mut v_x_3266_: usize,
    mut v_x_3267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_3269_: usize = 0;
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: u8 = 0;
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3275_: u8 = 0;
    let mut v___x_3276_: usize = 0;
    let mut v___x_3277_: usize = 0;
    let mut v___x_3278_: usize = 0;
    let mut v_i_3279_: usize = 0;
    let mut v___x_3280_: usize = 0;
    let mut v_shift_3281_: usize = 0;
    let mut v_v_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3290_: u8 = 0;
    let mut v_unused_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3295_: u8 = 0;
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3264_) == 0 {
                    v_cs_3268_ = leanh::lean_ctor_get(v_x_3264_, 0);
                    v_j_3269_ = lean_usize_shift_right(v_x_3265_, v_x_3266_);
                    v___x_3270_ = lean_usize_to_nat(v_j_3269_);
                    v___x_3271_ = lean_array_get_size(v_cs_3268_);
                    v___x_3272_ = lean_nat_dec_lt(v___x_3270_, v___x_3271_);
                    if v___x_3272_ == 0 {
                        leanh::lean_dec(v___x_3270_);
                        leanh::lean_dec(v_x_3267_);
                        return v_x_3264_;
                    } else {
                        leanh::lean_inc_ref(v_cs_3268_);
                        v_isSharedCheck_3290_ = (!leanh::lean_is_exclusive(v_x_3264_)) as u8;
                        if v_isSharedCheck_3290_ == 0 {
                            v_unused_3291_ = leanh::lean_ctor_get(v_x_3264_, 0);
                            leanh::lean_dec(v_unused_3291_);
                            v___x_3274_ = v_x_3264_;
                            v_isShared_3275_ = v_isSharedCheck_3290_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3264_);
                            v___x_3274_ = leanh::lean_box(0);
                            v_isShared_3275_ = v_isSharedCheck_3290_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_vs_3292_ = leanh::lean_ctor_get(v_x_3264_, 0);
                    v_isSharedCheck_3301_ = (!leanh::lean_is_exclusive(v_x_3264_)) as u8;
                    if v_isSharedCheck_3301_ == 0 {
                        v___x_3294_ = v_x_3264_;
                        v_isShared_3295_ = v_isSharedCheck_3301_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3292_);
                        leanh::lean_dec(v_x_3264_);
                        v___x_3294_ = leanh::lean_box(0);
                        v_isShared_3295_ = v_isSharedCheck_3301_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3276_ = 1usize;
                v___x_3277_ = lean_usize_shift_left(v___x_3276_, v_x_3266_);
                v___x_3278_ = lean_usize_sub(v___x_3277_, v___x_3276_);
                v_i_3279_ = lean_usize_land(v_x_3265_, v___x_3278_);
                v___x_3280_ = 5usize;
                v_shift_3281_ = lean_usize_sub(v_x_3266_, v___x_3280_);
                v_v_3282_ = lean_array_fget(v_cs_3268_, v___x_3270_);
                v___x_3283_ = leanh::lean_box(0);
                v_xs_x27_3284_ = lean_array_fset(v_cs_3268_, v___x_3270_, v___x_3283_);
                v___x_3285_ = l_Lean_PersistentArray_setAux___redArg(
                    v_v_3282_,
                    v_i_3279_,
                    v_shift_3281_,
                    v_x_3267_,
                );
                v___x_3286_ = lean_array_fset(v_xs_x27_3284_, v___x_3270_, v___x_3285_);
                leanh::lean_dec(v___x_3270_);
                if v_isShared_3275_ == 0 {
                    leanh::lean_ctor_set(v___x_3274_, 0, v___x_3286_);
                    v___x_3288_ = v___x_3274_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
                    v___x_3288_ = v_reuseFailAlloc_3289_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3288_;
            }
            3 => {
                v___x_3296_ = lean_usize_to_nat(v_x_3265_);
                v___x_3297_ = lean_array_set(v_vs_3292_, v___x_3296_, v_x_3267_);
                leanh::lean_dec(v___x_3296_);
                if v_isShared_3295_ == 0 {
                    leanh::lean_ctor_set(v___x_3294_, 0, v___x_3297_);
                    v___x_3299_ = v___x_3294_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3300_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
                    v___x_3299_ = v_reuseFailAlloc_3300_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_setAux___redArg___boxed(
    mut v_x_3302_: *mut leanh::LeanObject,
    mut v_x_3303_: *mut leanh::LeanObject,
    mut v_x_3304_: *mut leanh::LeanObject,
    mut v_x_3305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_77__boxed_3306_: usize = 0;
    let mut v_x_78__boxed_3307_: usize = 0;
    let mut v_res_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_77__boxed_3306_ = leanh::lean_unbox_usize(v_x_3303_);
    leanh::lean_dec(v_x_3303_);
    v_x_78__boxed_3307_ = leanh::lean_unbox_usize(v_x_3304_);
    leanh::lean_dec(v_x_3304_);
    v_res_3308_ = l_Lean_PersistentArray_setAux___redArg(
        v_x_3302_,
        v_x_77__boxed_3306_,
        v_x_78__boxed_3307_,
        v_x_3305_,
    );
    return v_res_3308_;
}
pub unsafe fn l_Lean_PersistentArray_setAux(
    mut v_00_u03b1_3309_: *mut leanh::LeanObject,
    mut v_x_3310_: *mut leanh::LeanObject,
    mut v_x_3311_: usize,
    mut v_x_3312_: usize,
    mut v_x_3313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3314_ =
        l_Lean_PersistentArray_setAux___redArg(v_x_3310_, v_x_3311_, v_x_3312_, v_x_3313_);
    return v___x_3314_;
}
pub unsafe fn l_Lean_PersistentArray_setAux___boxed(
    mut v_00_u03b1_3315_: *mut leanh::LeanObject,
    mut v_x_3316_: *mut leanh::LeanObject,
    mut v_x_3317_: *mut leanh::LeanObject,
    mut v_x_3318_: *mut leanh::LeanObject,
    mut v_x_3319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_147__boxed_3320_: usize = 0;
    let mut v_x_148__boxed_3321_: usize = 0;
    let mut v_res_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_147__boxed_3320_ = leanh::lean_unbox_usize(v_x_3317_);
    leanh::lean_dec(v_x_3317_);
    v_x_148__boxed_3321_ = leanh::lean_unbox_usize(v_x_3318_);
    leanh::lean_dec(v_x_3318_);
    v_res_3322_ = l_Lean_PersistentArray_setAux(
        v_00_u03b1_3315_,
        v_x_3316_,
        v_x_147__boxed_3320_,
        v_x_148__boxed_3321_,
        v_x_3319_,
    );
    return v_res_3322_;
}
pub unsafe fn l_Lean_PersistentArray_set___redArg(
    mut v_t_3323_: *mut leanh::LeanObject,
    mut v_i_3324_: *mut leanh::LeanObject,
    mut v_a_3325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_3329_: usize = 0;
    let mut v_tailOff_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3333_: u8 = 0;
    let mut v___x_3334_: u8 = 0;
    let mut v___x_3335_: usize = 0;
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3326_ = leanh::lean_ctor_get(v_t_3323_, 0);
                v_tail_3327_ = leanh::lean_ctor_get(v_t_3323_, 1);
                v_size_3328_ = leanh::lean_ctor_get(v_t_3323_, 2);
                v_shift_3329_ = leanh::lean_ctor_get_usize(v_t_3323_, 4);
                v_tailOff_3330_ = leanh::lean_ctor_get(v_t_3323_, 3);
                v_isSharedCheck_3345_ = (!leanh::lean_is_exclusive(v_t_3323_)) as u8;
                if v_isSharedCheck_3345_ == 0 {
                    v___x_3332_ = v_t_3323_;
                    v_isShared_3333_ = v_isSharedCheck_3345_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tailOff_3330_);
                    leanh::lean_inc(v_size_3328_);
                    leanh::lean_inc(v_tail_3327_);
                    leanh::lean_inc(v_root_3326_);
                    leanh::lean_dec(v_t_3323_);
                    v___x_3332_ = leanh::lean_box(0);
                    v_isShared_3333_ = v_isSharedCheck_3345_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3334_ = lean_nat_dec_le(v_tailOff_3330_, v_i_3324_);
                if v___x_3334_ == 0 {
                    v___x_3335_ = lean_usize_of_nat(v_i_3324_);
                    v___x_3336_ = l_Lean_PersistentArray_setAux___redArg(
                        v_root_3326_,
                        v___x_3335_,
                        v_shift_3329_,
                        v_a_3325_,
                    );
                    if v_isShared_3333_ == 0 {
                        leanh::lean_ctor_set(v___x_3332_, 0, v___x_3336_);
                        v___x_3338_ = v___x_3332_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3339_ = leanh::lean_alloc_ctor(
                            0,
                            4,
                            (core::mem::size_of::<usize>() * 1) as u32,
                        );
                        leanh::lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3336_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_tail_3327_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3339_, 2, v_size_3328_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3339_, 3, v_tailOff_3330_);
                        leanh::lean_ctor_set_usize(v_reuseFailAlloc_3339_, 4, v_shift_3329_);
                        v___x_3338_ = v_reuseFailAlloc_3339_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3340_ = lean_nat_sub(v_i_3324_, v_tailOff_3330_);
                    v___x_3341_ = lean_array_set(v_tail_3327_, v___x_3340_, v_a_3325_);
                    leanh::lean_dec(v___x_3340_);
                    if v_isShared_3333_ == 0 {
                        leanh::lean_ctor_set(v___x_3332_, 1, v___x_3341_);
                        v___x_3343_ = v___x_3332_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3344_ = leanh::lean_alloc_ctor(
                            0,
                            4,
                            (core::mem::size_of::<usize>() * 1) as u32,
                        );
                        leanh::lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_root_3326_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3344_, 1, v___x_3341_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3344_, 2, v_size_3328_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3344_, 3, v_tailOff_3330_);
                        leanh::lean_ctor_set_usize(v_reuseFailAlloc_3344_, 4, v_shift_3329_);
                        v___x_3343_ = v_reuseFailAlloc_3344_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3338_;
            }
            3 => {
                return v___x_3343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_set___redArg___boxed(
    mut v_t_3346_: *mut leanh::LeanObject,
    mut v_i_3347_: *mut leanh::LeanObject,
    mut v_a_3348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3349_ = l_Lean_PersistentArray_set___redArg(v_t_3346_, v_i_3347_, v_a_3348_);
    leanh::lean_dec(v_i_3347_);
    return v_res_3349_;
}
pub unsafe fn l_Lean_PersistentArray_set(
    mut v_00_u03b1_3350_: *mut leanh::LeanObject,
    mut v_t_3351_: *mut leanh::LeanObject,
    mut v_i_3352_: *mut leanh::LeanObject,
    mut v_a_3353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3354_ = l_Lean_PersistentArray_set___redArg(v_t_3351_, v_i_3352_, v_a_3353_);
    return v___x_3354_;
}
pub unsafe fn l_Lean_PersistentArray_set___boxed(
    mut v_00_u03b1_3355_: *mut leanh::LeanObject,
    mut v_t_3356_: *mut leanh::LeanObject,
    mut v_i_3357_: *mut leanh::LeanObject,
    mut v_a_3358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3359_ = l_Lean_PersistentArray_set(v_00_u03b1_3355_, v_t_3356_, v_i_3357_, v_a_3358_);
    leanh::lean_dec(v_i_3357_);
    return v_res_3359_;
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___redArg(
    mut v_f_3360_: *mut leanh::LeanObject,
    mut v_x_3361_: *mut leanh::LeanObject,
    mut v_x_3362_: usize,
    mut v_x_3363_: usize,
) -> *mut leanh::LeanObject {
    let mut v_cs_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_3365_: usize = 0;
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: u8 = 0;
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3371_: u8 = 0;
    let mut v___x_3372_: usize = 0;
    let mut v___x_3373_: usize = 0;
    let mut v___x_3374_: usize = 0;
    let mut v_i_3375_: usize = 0;
    let mut v___x_3376_: usize = 0;
    let mut v_shift_3377_: usize = 0;
    let mut v_v_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3386_: u8 = 0;
    let mut v_unused_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: u8 = 0;
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3394_: u8 = 0;
    let mut v_v_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3403_: u8 = 0;
    let mut v_unused_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3361_) == 0 {
                    v_cs_3364_ = leanh::lean_ctor_get(v_x_3361_, 0);
                    v_j_3365_ = lean_usize_shift_right(v_x_3362_, v_x_3363_);
                    v___x_3366_ = lean_usize_to_nat(v_j_3365_);
                    v___x_3367_ = lean_array_get_size(v_cs_3364_);
                    v___x_3368_ = lean_nat_dec_lt(v___x_3366_, v___x_3367_);
                    if v___x_3368_ == 0 {
                        leanh::lean_dec(v___x_3366_);
                        leanh::lean_dec(v_f_3360_);
                        return v_x_3361_;
                    } else {
                        leanh::lean_inc_ref(v_cs_3364_);
                        v_isSharedCheck_3386_ = (!leanh::lean_is_exclusive(v_x_3361_)) as u8;
                        if v_isSharedCheck_3386_ == 0 {
                            v_unused_3387_ = leanh::lean_ctor_get(v_x_3361_, 0);
                            leanh::lean_dec(v_unused_3387_);
                            v___x_3370_ = v_x_3361_;
                            v_isShared_3371_ = v_isSharedCheck_3386_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3361_);
                            v___x_3370_ = leanh::lean_box(0);
                            v_isShared_3371_ = v_isSharedCheck_3386_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_vs_3388_ = leanh::lean_ctor_get(v_x_3361_, 0);
                    v___x_3389_ = lean_usize_to_nat(v_x_3362_);
                    v___x_3390_ = lean_array_get_size(v_vs_3388_);
                    v___x_3391_ = lean_nat_dec_lt(v___x_3389_, v___x_3390_);
                    if v___x_3391_ == 0 {
                        leanh::lean_dec(v___x_3389_);
                        leanh::lean_dec(v_f_3360_);
                        return v_x_3361_;
                    } else {
                        leanh::lean_inc_ref(v_vs_3388_);
                        v_isSharedCheck_3403_ = (!leanh::lean_is_exclusive(v_x_3361_)) as u8;
                        if v_isSharedCheck_3403_ == 0 {
                            v_unused_3404_ = leanh::lean_ctor_get(v_x_3361_, 0);
                            leanh::lean_dec(v_unused_3404_);
                            v___x_3393_ = v_x_3361_;
                            v_isShared_3394_ = v_isSharedCheck_3403_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3361_);
                            v___x_3393_ = leanh::lean_box(0);
                            v_isShared_3394_ = v_isSharedCheck_3403_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3372_ = 1usize;
                v___x_3373_ = lean_usize_shift_left(v___x_3372_, v_x_3363_);
                v___x_3374_ = lean_usize_sub(v___x_3373_, v___x_3372_);
                v_i_3375_ = lean_usize_land(v_x_3362_, v___x_3374_);
                v___x_3376_ = 5usize;
                v_shift_3377_ = lean_usize_sub(v_x_3363_, v___x_3376_);
                v_v_3378_ = lean_array_fget(v_cs_3364_, v___x_3366_);
                v___x_3379_ = leanh::lean_box(0);
                v_xs_x27_3380_ = lean_array_fset(v_cs_3364_, v___x_3366_, v___x_3379_);
                v___x_3381_ = l_Lean_PersistentArray_modifyAux___redArg(
                    v_f_3360_,
                    v_v_3378_,
                    v_i_3375_,
                    v_shift_3377_,
                );
                v___x_3382_ = lean_array_fset(v_xs_x27_3380_, v___x_3366_, v___x_3381_);
                leanh::lean_dec(v___x_3366_);
                if v_isShared_3371_ == 0 {
                    leanh::lean_ctor_set(v___x_3370_, 0, v___x_3382_);
                    v___x_3384_ = v___x_3370_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3385_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3382_);
                    v___x_3384_ = v_reuseFailAlloc_3385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3384_;
            }
            3 => {
                v_v_3395_ = lean_array_fget(v_vs_3388_, v___x_3389_);
                v___x_3396_ = leanh::lean_box(0);
                v_xs_x27_3397_ = lean_array_fset(v_vs_3388_, v___x_3389_, v___x_3396_);
                v___x_3398_ = leanh::lean_apply_1(v_f_3360_, v_v_3395_);
                v___x_3399_ = lean_array_fset(v_xs_x27_3397_, v___x_3389_, v___x_3398_);
                leanh::lean_dec(v___x_3389_);
                if v_isShared_3394_ == 0 {
                    leanh::lean_ctor_set(v___x_3393_, 0, v___x_3399_);
                    v___x_3401_ = v___x_3393_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3402_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3399_);
                    v___x_3401_ = v_reuseFailAlloc_3402_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___redArg___boxed(
    mut v_f_3405_: *mut leanh::LeanObject,
    mut v_x_3406_: *mut leanh::LeanObject,
    mut v_x_3407_: *mut leanh::LeanObject,
    mut v_x_3408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_92__boxed_3409_: usize = 0;
    let mut v_x_93__boxed_3410_: usize = 0;
    let mut v_res_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_92__boxed_3409_ = leanh::lean_unbox_usize(v_x_3407_);
    leanh::lean_dec(v_x_3407_);
    v_x_93__boxed_3410_ = leanh::lean_unbox_usize(v_x_3408_);
    leanh::lean_dec(v_x_3408_);
    v_res_3411_ = l_Lean_PersistentArray_modifyAux___redArg(
        v_f_3405_,
        v_x_3406_,
        v_x_92__boxed_3409_,
        v_x_93__boxed_3410_,
    );
    return v_res_3411_;
}
pub unsafe fn l_Lean_PersistentArray_modifyAux(
    mut v_00_u03b1_3412_: *mut leanh::LeanObject,
    mut v_inst_3413_: *mut leanh::LeanObject,
    mut v_f_3414_: *mut leanh::LeanObject,
    mut v_x_3415_: *mut leanh::LeanObject,
    mut v_x_3416_: usize,
    mut v_x_3417_: usize,
) -> *mut leanh::LeanObject {
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3418_ =
        l_Lean_PersistentArray_modifyAux___redArg(v_f_3414_, v_x_3415_, v_x_3416_, v_x_3417_);
    return v___x_3418_;
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___boxed(
    mut v_00_u03b1_3419_: *mut leanh::LeanObject,
    mut v_inst_3420_: *mut leanh::LeanObject,
    mut v_f_3421_: *mut leanh::LeanObject,
    mut v_x_3422_: *mut leanh::LeanObject,
    mut v_x_3423_: *mut leanh::LeanObject,
    mut v_x_3424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_170__boxed_3425_: usize = 0;
    let mut v_x_171__boxed_3426_: usize = 0;
    let mut v_res_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_170__boxed_3425_ = leanh::lean_unbox_usize(v_x_3423_);
    leanh::lean_dec(v_x_3423_);
    v_x_171__boxed_3426_ = leanh::lean_unbox_usize(v_x_3424_);
    leanh::lean_dec(v_x_3424_);
    v_res_3427_ = l_Lean_PersistentArray_modifyAux(
        v_00_u03b1_3419_,
        v_inst_3420_,
        v_f_3421_,
        v_x_3422_,
        v_x_170__boxed_3425_,
        v_x_171__boxed_3426_,
    );
    leanh::lean_dec(v_inst_3420_);
    return v_res_3427_;
}
pub unsafe fn l_Lean_PersistentArray_modify___redArg(
    mut v_t_3428_: *mut leanh::LeanObject,
    mut v_i_3429_: *mut leanh::LeanObject,
    mut v_f_3430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_3434_: usize = 0;
    let mut v_tailOff_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3439_: u8 = 0;
    let mut v___x_3440_: usize = 0;
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: u8 = 0;
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3431_ = leanh::lean_ctor_get(v_t_3428_, 0);
                v_tail_3432_ = leanh::lean_ctor_get(v_t_3428_, 1);
                v_size_3433_ = leanh::lean_ctor_get(v_t_3428_, 2);
                v_shift_3434_ = leanh::lean_ctor_get_usize(v_t_3428_, 4);
                v_tailOff_3435_ = leanh::lean_ctor_get(v_t_3428_, 3);
                v_isSharedCheck_3459_ = (!leanh::lean_is_exclusive(v_t_3428_)) as u8;
                if v_isSharedCheck_3459_ == 0 {
                    v___x_3437_ = v_t_3428_;
                    v_isShared_3438_ = v_isSharedCheck_3459_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tailOff_3435_);
                    leanh::lean_inc(v_size_3433_);
                    leanh::lean_inc(v_tail_3432_);
                    leanh::lean_inc(v_root_3431_);
                    leanh::lean_dec(v_t_3428_);
                    v___x_3437_ = leanh::lean_box(0);
                    v_isShared_3438_ = v_isSharedCheck_3459_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3439_ = lean_nat_dec_le(v_tailOff_3435_, v_i_3429_);
                if v___x_3439_ == 0 {
                    v___x_3440_ = lean_usize_of_nat(v_i_3429_);
                    v___x_3441_ = l_Lean_PersistentArray_modifyAux___redArg(
                        v_f_3430_,
                        v_root_3431_,
                        v___x_3440_,
                        v_shift_3434_,
                    );
                    if v_isShared_3438_ == 0 {
                        leanh::lean_ctor_set(v___x_3437_, 0, v___x_3441_);
                        v___x_3443_ = v___x_3437_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3444_ = leanh::lean_alloc_ctor(
                            0,
                            4,
                            (core::mem::size_of::<usize>() * 1) as u32,
                        );
                        leanh::lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_tail_3432_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3444_, 2, v_size_3433_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3444_, 3, v_tailOff_3435_);
                        leanh::lean_ctor_set_usize(v_reuseFailAlloc_3444_, 4, v_shift_3434_);
                        v___x_3443_ = v_reuseFailAlloc_3444_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3445_ = lean_nat_sub(v_i_3429_, v_tailOff_3435_);
                    v___x_3446_ = lean_array_get_size(v_tail_3432_);
                    v___x_3447_ = lean_nat_dec_lt(v___x_3445_, v___x_3446_);
                    if v___x_3447_ == 0 {
                        leanh::lean_dec(v___x_3445_);
                        leanh::lean_dec(v_f_3430_);
                        if v_isShared_3438_ == 0 {
                            v___x_3449_ = v___x_3437_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3450_ = leanh::lean_alloc_ctor(
                                0,
                                4,
                                (core::mem::size_of::<usize>() * 1) as u32,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_root_3431_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_tail_3432_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3450_, 2, v_size_3433_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3450_, 3, v_tailOff_3435_);
                            leanh::lean_ctor_set_usize(
                                v_reuseFailAlloc_3450_,
                                4,
                                v_shift_3434_,
                            );
                            v___x_3449_ = v_reuseFailAlloc_3450_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_v_3451_ = lean_array_fget(v_tail_3432_, v___x_3445_);
                        v___x_3452_ = leanh::lean_box(0);
                        v_xs_x27_3453_ = lean_array_fset(v_tail_3432_, v___x_3445_, v___x_3452_);
                        v___x_3454_ = leanh::lean_apply_1(v_f_3430_, v_v_3451_);
                        v___x_3455_ = lean_array_fset(v_xs_x27_3453_, v___x_3445_, v___x_3454_);
                        leanh::lean_dec(v___x_3445_);
                        if v_isShared_3438_ == 0 {
                            leanh::lean_ctor_set(v___x_3437_, 1, v___x_3455_);
                            v___x_3457_ = v___x_3437_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3458_ = leanh::lean_alloc_ctor(
                                0,
                                4,
                                (core::mem::size_of::<usize>() * 1) as u32,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_root_3431_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 1, v___x_3455_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 2, v_size_3433_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 3, v_tailOff_3435_);
                            leanh::lean_ctor_set_usize(
                                v_reuseFailAlloc_3458_,
                                4,
                                v_shift_3434_,
                            );
                            v___x_3457_ = v_reuseFailAlloc_3458_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3443_;
            }
            3 => {
                return v___x_3449_;
            }
            4 => {
                return v___x_3457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modify___redArg___boxed(
    mut v_t_3460_: *mut leanh::LeanObject,
    mut v_i_3461_: *mut leanh::LeanObject,
    mut v_f_3462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3463_ = l_Lean_PersistentArray_modify___redArg(v_t_3460_, v_i_3461_, v_f_3462_);
    leanh::lean_dec(v_i_3461_);
    return v_res_3463_;
}
pub unsafe fn l_Lean_PersistentArray_modify(
    mut v_00_u03b1_3464_: *mut leanh::LeanObject,
    mut v_inst_3465_: *mut leanh::LeanObject,
    mut v_t_3466_: *mut leanh::LeanObject,
    mut v_i_3467_: *mut leanh::LeanObject,
    mut v_f_3468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3469_ = l_Lean_PersistentArray_modify___redArg(v_t_3466_, v_i_3467_, v_f_3468_);
    return v___x_3469_;
}
pub unsafe fn l_Lean_PersistentArray_modify___boxed(
    mut v_00_u03b1_3470_: *mut leanh::LeanObject,
    mut v_inst_3471_: *mut leanh::LeanObject,
    mut v_t_3472_: *mut leanh::LeanObject,
    mut v_i_3473_: *mut leanh::LeanObject,
    mut v_f_3474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3475_ = l_Lean_PersistentArray_modify(
        v_00_u03b1_3470_,
        v_inst_3471_,
        v_t_3472_,
        v_i_3473_,
        v_f_3474_,
    );
    leanh::lean_dec(v_i_3473_);
    leanh::lean_dec(v_inst_3471_);
    return v_res_3475_;
}
pub unsafe fn _init_l_Lean_PersistentArray_mkNewPath___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3476_ = l_Lean_PersistentArray_mkEmptyArray(leanh::lean_box(0));
    return v___x_3476_;
}
pub unsafe fn l_Lean_PersistentArray_mkNewPath___redArg(
    mut v_shift_3477_: usize,
    mut v_a_3478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3479_: usize = 0;
    let mut v___x_3480_: u8 = 0;
    v___x_3479_ = 0usize;
    v___x_3480_ = lean_usize_dec_eq(v_shift_3477_, v___x_3479_);
    if v___x_3480_ == 0 {
        let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3482_: usize = 0;
        let mut v___x_3483_: usize = 0;
        let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3481_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_PersistentArray_mkNewPath___redArg___closed__0),
            core::ptr::addr_of_mut!(l_Lean_PersistentArray_mkNewPath___redArg___closed__0_once),
            _init_l_Lean_PersistentArray_mkNewPath___redArg___closed__0,
        );
        v___x_3482_ = 5usize;
        v___x_3483_ = lean_usize_sub(v_shift_3477_, v___x_3482_);
        v___x_3484_ = l_Lean_PersistentArray_mkNewPath___redArg(v___x_3483_, v_a_3478_);
        v___x_3485_ = lean_array_push(v___x_3481_, v___x_3484_);
        v___x_3486_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3486_, 0, v___x_3485_);
        return v___x_3486_;
    } else {
        let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3487_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3487_, 0, v_a_3478_);
        return v___x_3487_;
    }
}
pub unsafe fn l_Lean_PersistentArray_mkNewPath___redArg___boxed(
    mut v_shift_3488_: *mut leanh::LeanObject,
    mut v_a_3489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_shift_boxed_3490_: usize = 0;
    let mut v_res_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_shift_boxed_3490_ = leanh::lean_unbox_usize(v_shift_3488_);
    leanh::lean_dec(v_shift_3488_);
    v_res_3491_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_boxed_3490_, v_a_3489_);
    return v_res_3491_;
}
pub unsafe fn l_Lean_PersistentArray_mkNewPath(
    mut v_00_u03b1_3492_: *mut leanh::LeanObject,
    mut v_shift_3493_: usize,
    mut v_a_3494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3495_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_3493_, v_a_3494_);
    return v___x_3495_;
}
pub unsafe fn l_Lean_PersistentArray_mkNewPath___boxed(
    mut v_00_u03b1_3496_: *mut leanh::LeanObject,
    mut v_shift_3497_: *mut leanh::LeanObject,
    mut v_a_3498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_shift_boxed_3499_: usize = 0;
    let mut v_res_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_shift_boxed_3499_ = leanh::lean_unbox_usize(v_shift_3497_);
    leanh::lean_dec(v_shift_3497_);
    v_res_3500_ =
        l_Lean_PersistentArray_mkNewPath(v_00_u03b1_3496_, v_shift_boxed_3499_, v_a_3498_);
    return v_res_3500_;
}
pub unsafe fn l_Lean_PersistentArray_insertNewLeaf___redArg(
    mut v_x_3501_: *mut leanh::LeanObject,
    mut v_x_3502_: usize,
    mut v_x_3503_: usize,
    mut v_x_3504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: usize = 0;
    let mut v___x_3507_: u8 = 0;
    let mut v_j_3508_: usize = 0;
    let mut v___x_3509_: usize = 0;
    let mut v___x_3510_: usize = 0;
    let mut v___x_3511_: usize = 0;
    let mut v_shift_3512_: usize = 0;
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: u8 = 0;
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3518_: u8 = 0;
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3524_: u8 = 0;
    let mut v_unused_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v___x_3529_: usize = 0;
    let mut v_i_3530_: usize = 0;
    let mut v_v_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3539_: u8 = 0;
    let mut v_unused_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3543_: u8 = 0;
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3549_: u8 = 0;
    let mut v_unused_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3501_) == 0 {
                    v_cs_3505_ = leanh::lean_ctor_get(v_x_3501_, 0);
                    v___x_3506_ = 32usize;
                    v___x_3507_ = lean_usize_dec_lt(v_x_3502_, v___x_3506_);
                    if v___x_3507_ == 0 {
                        v_j_3508_ = lean_usize_shift_right(v_x_3502_, v_x_3503_);
                        v___x_3509_ = 1usize;
                        v___x_3510_ = lean_usize_shift_left(v___x_3509_, v_x_3503_);
                        v___x_3511_ = 5usize;
                        v_shift_3512_ = lean_usize_sub(v_x_3503_, v___x_3511_);
                        v___x_3513_ = lean_usize_to_nat(v_j_3508_);
                        v___x_3514_ = lean_array_get_size(v_cs_3505_);
                        v___x_3515_ = lean_nat_dec_lt(v___x_3513_, v___x_3514_);
                        if v___x_3515_ == 0 {
                            leanh::lean_inc_ref(v_cs_3505_);
                            leanh::lean_dec(v___x_3513_);
                            v_isSharedCheck_3524_ =
                                (!leanh::lean_is_exclusive(v_x_3501_)) as u8;
                            if v_isSharedCheck_3524_ == 0 {
                                v_unused_3525_ = leanh::lean_ctor_get(v_x_3501_, 0);
                                leanh::lean_dec(v_unused_3525_);
                                v___x_3517_ = v_x_3501_;
                                v_isShared_3518_ = v_isSharedCheck_3524_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_x_3501_);
                                v___x_3517_ = leanh::lean_box(0);
                                v_isShared_3518_ = v_isSharedCheck_3524_;
                                state = 1;
                                continue;
                            }
                        } else {
                            if v___x_3515_ == 0 {
                                leanh::lean_dec(v___x_3513_);
                                leanh::lean_dec_ref(v_x_3504_);
                                return v_x_3501_;
                            } else {
                                leanh::lean_inc_ref(v_cs_3505_);
                                v_isSharedCheck_3539_ =
                                    (!leanh::lean_is_exclusive(v_x_3501_)) as u8;
                                if v_isSharedCheck_3539_ == 0 {
                                    v_unused_3540_ = leanh::lean_ctor_get(v_x_3501_, 0);
                                    leanh::lean_dec(v_unused_3540_);
                                    v___x_3527_ = v_x_3501_;
                                    v_isShared_3528_ = v_isSharedCheck_3539_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_x_3501_);
                                    v___x_3527_ = leanh::lean_box(0);
                                    v_isShared_3528_ = v_isSharedCheck_3539_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_inc_ref(v_cs_3505_);
                        v_isSharedCheck_3549_ = (!leanh::lean_is_exclusive(v_x_3501_)) as u8;
                        if v_isSharedCheck_3549_ == 0 {
                            v_unused_3550_ = leanh::lean_ctor_get(v_x_3501_, 0);
                            leanh::lean_dec(v_unused_3550_);
                            v___x_3542_ = v_x_3501_;
                            v_isShared_3543_ = v_isSharedCheck_3549_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3501_);
                            v___x_3542_ = leanh::lean_box(0);
                            v_isShared_3543_ = v_isSharedCheck_3549_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_x_3504_);
                    return v_x_3501_;
                }
            }
            1 => {
                v___x_3519_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_3512_, v_x_3504_);
                v___x_3520_ = lean_array_push(v_cs_3505_, v___x_3519_);
                if v_isShared_3518_ == 0 {
                    leanh::lean_ctor_set(v___x_3517_, 0, v___x_3520_);
                    v___x_3522_ = v___x_3517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3523_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3520_);
                    v___x_3522_ = v_reuseFailAlloc_3523_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3522_;
            }
            3 => {
                v___x_3529_ = lean_usize_sub(v___x_3510_, v___x_3509_);
                v_i_3530_ = lean_usize_land(v_x_3502_, v___x_3529_);
                v_v_3531_ = lean_array_fget(v_cs_3505_, v___x_3513_);
                v___x_3532_ = leanh::lean_box(0);
                v_xs_x27_3533_ = lean_array_fset(v_cs_3505_, v___x_3513_, v___x_3532_);
                v___x_3534_ = l_Lean_PersistentArray_insertNewLeaf___redArg(
                    v_v_3531_,
                    v_i_3530_,
                    v_shift_3512_,
                    v_x_3504_,
                );
                v___x_3535_ = lean_array_fset(v_xs_x27_3533_, v___x_3513_, v___x_3534_);
                leanh::lean_dec(v___x_3513_);
                if v_isShared_3528_ == 0 {
                    leanh::lean_ctor_set(v___x_3527_, 0, v___x_3535_);
                    v___x_3537_ = v___x_3527_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3538_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
                    v___x_3537_ = v_reuseFailAlloc_3538_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3537_;
            }
            5 => {
                if v_isShared_3543_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3542_, 1);
                    leanh::lean_ctor_set(v___x_3542_, 0, v_x_3504_);
                    v___x_3545_ = v___x_3542_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3548_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_x_3504_);
                    v___x_3545_ = v_reuseFailAlloc_3548_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3546_ = lean_array_push(v_cs_3505_, v___x_3545_);
                v___x_3547_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3547_, 0, v___x_3546_);
                return v___x_3547_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_insertNewLeaf___redArg___boxed(
    mut v_x_3551_: *mut leanh::LeanObject,
    mut v_x_3552_: *mut leanh::LeanObject,
    mut v_x_3553_: *mut leanh::LeanObject,
    mut v_x_3554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_107__boxed_3555_: usize = 0;
    let mut v_x_108__boxed_3556_: usize = 0;
    let mut v_res_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_107__boxed_3555_ = leanh::lean_unbox_usize(v_x_3552_);
    leanh::lean_dec(v_x_3552_);
    v_x_108__boxed_3556_ = leanh::lean_unbox_usize(v_x_3553_);
    leanh::lean_dec(v_x_3553_);
    v_res_3557_ = l_Lean_PersistentArray_insertNewLeaf___redArg(
        v_x_3551_,
        v_x_107__boxed_3555_,
        v_x_108__boxed_3556_,
        v_x_3554_,
    );
    return v_res_3557_;
}
pub unsafe fn l_Lean_PersistentArray_insertNewLeaf(
    mut v_00_u03b1_3558_: *mut leanh::LeanObject,
    mut v_x_3559_: *mut leanh::LeanObject,
    mut v_x_3560_: usize,
    mut v_x_3561_: usize,
    mut v_x_3562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3563_ =
        l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_3559_, v_x_3560_, v_x_3561_, v_x_3562_);
    return v___x_3563_;
}
pub unsafe fn l_Lean_PersistentArray_insertNewLeaf___boxed(
    mut v_00_u03b1_3564_: *mut leanh::LeanObject,
    mut v_x_3565_: *mut leanh::LeanObject,
    mut v_x_3566_: *mut leanh::LeanObject,
    mut v_x_3567_: *mut leanh::LeanObject,
    mut v_x_3568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_201__boxed_3569_: usize = 0;
    let mut v_x_202__boxed_3570_: usize = 0;
    let mut v_res_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_201__boxed_3569_ = leanh::lean_unbox_usize(v_x_3566_);
    leanh::lean_dec(v_x_3566_);
    v_x_202__boxed_3570_ = leanh::lean_unbox_usize(v_x_3567_);
    leanh::lean_dec(v_x_3567_);
    v_res_3571_ = l_Lean_PersistentArray_insertNewLeaf(
        v_00_u03b1_3564_,
        v_x_3565_,
        v_x_201__boxed_3569_,
        v_x_202__boxed_3570_,
        v_x_3568_,
    );
    return v_res_3571_;
}
pub unsafe fn _init_l_Lean_PersistentArray_mkNewTail___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3574_ = l_Lean_PersistentArray_mkEmptyArray(leanh::lean_box(0));
    return v___x_3574_;
}
pub unsafe fn l_Lean_PersistentArray_mkNewTail___redArg(
    mut v_t_3575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_3579_: usize = 0;
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3582_: u8 = 0;
    let mut v___x_3583_: usize = 0;
    let mut v___x_3584_: usize = 0;
    let mut v___x_3585_: usize = 0;
    let mut v___x_3586_: usize = 0;
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: u8 = 0;
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: usize = 0;
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3606_: u8 = 0;
    let mut v_unused_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3576_ = leanh::lean_ctor_get(v_t_3575_, 0);
                v_tail_3577_ = leanh::lean_ctor_get(v_t_3575_, 1);
                v_size_3578_ = leanh::lean_ctor_get(v_t_3575_, 2);
                v_shift_3579_ = leanh::lean_ctor_get_usize(v_t_3575_, 4);
                v_isSharedCheck_3606_ = (!leanh::lean_is_exclusive(v_t_3575_)) as u8;
                if v_isSharedCheck_3606_ == 0 {
                    v_unused_3607_ = leanh::lean_ctor_get(v_t_3575_, 3);
                    leanh::lean_dec(v_unused_3607_);
                    v___x_3581_ = v_t_3575_;
                    v_isShared_3582_ = v_isSharedCheck_3606_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_size_3578_);
                    leanh::lean_inc(v_tail_3577_);
                    leanh::lean_inc(v_root_3576_);
                    leanh::lean_dec(v_t_3575_);
                    v___x_3581_ = leanh::lean_box(0);
                    v_isShared_3582_ = v_isSharedCheck_3606_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3583_ = 1usize;
                v___x_3584_ = 5usize;
                v___x_3585_ = lean_usize_add(v_shift_3579_, v___x_3584_);
                v___x_3586_ = lean_usize_shift_left(v___x_3583_, v___x_3585_);
                v___x_3587_ = lean_usize_to_nat(v___x_3586_);
                v___x_3588_ = lean_nat_dec_le(v_size_3578_, v___x_3587_);
                leanh::lean_dec(v___x_3587_);
                if v___x_3588_ == 0 {
                    v___x_3589_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentArray_mkNewPath___redArg___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentArray_mkNewPath___redArg___closed__0_once
                        ),
                        _init_l_Lean_PersistentArray_mkNewPath___redArg___closed__0,
                    );
                    v_n_3590_ = lean_array_push(v___x_3589_, v_root_3576_);
                    v___x_3591_ =
                        l_Lean_PersistentArray_mkNewPath___redArg(v_shift_3579_, v_tail_3577_);
                    v___x_3592_ = lean_array_push(v_n_3590_, v___x_3591_);
                    v___x_3593_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3593_, 0, v___x_3592_);
                    v___x_3594_ = l_Lean_PersistentArray_mkNewTail___redArg___closed__0;
                    leanh::lean_inc(v_size_3578_);
                    if v_isShared_3582_ == 0 {
                        leanh::lean_ctor_set(v___x_3581_, 3, v_size_3578_);
                        leanh::lean_ctor_set(v___x_3581_, 1, v___x_3594_);
                        leanh::lean_ctor_set(v___x_3581_, 0, v___x_3593_);
                        v___x_3596_ = v___x_3581_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3597_ = leanh::lean_alloc_ctor(
                            0,
                            4,
                            (core::mem::size_of::<usize>() * 1) as u32,
                        );
                        leanh::lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3593_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3597_, 1, v___x_3594_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3597_, 2, v_size_3578_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3597_, 3, v_size_3578_);
                        v___x_3596_ = v_reuseFailAlloc_3597_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3598_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3599_ = lean_nat_sub(v_size_3578_, v___x_3598_);
                    v___x_3600_ = lean_usize_of_nat(v___x_3599_);
                    leanh::lean_dec(v___x_3599_);
                    v___x_3601_ = l_Lean_PersistentArray_insertNewLeaf___redArg(
                        v_root_3576_,
                        v___x_3600_,
                        v_shift_3579_,
                        v_tail_3577_,
                    );
                    v___x_3602_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentArray_mkNewTail___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentArray_mkNewTail___redArg___closed__1_once
                        ),
                        _init_l_Lean_PersistentArray_mkNewTail___redArg___closed__1,
                    );
                    leanh::lean_inc(v_size_3578_);
                    if v_isShared_3582_ == 0 {
                        leanh::lean_ctor_set(v___x_3581_, 3, v_size_3578_);
                        leanh::lean_ctor_set(v___x_3581_, 1, v___x_3602_);
                        leanh::lean_ctor_set(v___x_3581_, 0, v___x_3601_);
                        v___x_3604_ = v___x_3581_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3605_ = leanh::lean_alloc_ctor(
                            0,
                            4,
                            (core::mem::size_of::<usize>() * 1) as u32,
                        );
                        leanh::lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3601_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3605_, 1, v___x_3602_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3605_, 2, v_size_3578_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3605_, 3, v_size_3578_);
                        leanh::lean_ctor_set_usize(v_reuseFailAlloc_3605_, 4, v_shift_3579_);
                        v___x_3604_ = v_reuseFailAlloc_3605_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_usize(v___x_3596_, 4, v___x_3585_);
                return v___x_3596_;
            }
            3 => {
                return v___x_3604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mkNewTail(
    mut v_00_u03b1_3608_: *mut leanh::LeanObject,
    mut v_t_3609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3610_ = l_Lean_PersistentArray_mkNewTail___redArg(v_t_3609_);
    return v___x_3610_;
}
pub unsafe fn _init_l_Lean_PersistentArray_tooBig___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3611_ = l_System_Platform_numBits;
    v___x_3612_ = leanh::lean_unsigned_to_nat(2);
    v___x_3613_ = lean_nat_pow(v___x_3612_, v___x_3611_);
    return v___x_3613_;
}
pub unsafe fn _init_l_Lean_PersistentArray_tooBig___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3614_ = leanh::lean_unsigned_to_nat(3);
    v___x_3615_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PersistentArray_tooBig___closed__0),
        core::ptr::addr_of_mut!(l_Lean_PersistentArray_tooBig___closed__0_once),
        _init_l_Lean_PersistentArray_tooBig___closed__0,
    );
    v___x_3616_ = lean_nat_shiftr(v___x_3615_, v___x_3614_);
    return v___x_3616_;
}
pub unsafe fn _init_l_Lean_PersistentArray_tooBig() -> *mut leanh::LeanObject {
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3617_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PersistentArray_tooBig___closed__1),
        core::ptr::addr_of_mut!(l_Lean_PersistentArray_tooBig___closed__1_once),
        _init_l_Lean_PersistentArray_tooBig___closed__1,
    );
    return v___x_3617_;
}
pub unsafe fn l_Lean_PersistentArray_push___redArg(
    mut v_t_3618_: *mut leanh::LeanObject,
    mut v_a_3619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_3623_: usize = 0;
    let mut v_tailOff_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3627_: u8 = 0;
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3634_: u8 = 0;
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: u8 = 0;
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: u8 = 0;
    let mut v_reuseFailAlloc_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3620_ = leanh::lean_ctor_get(v_t_3618_, 0);
                v_tail_3621_ = leanh::lean_ctor_get(v_t_3618_, 1);
                v_size_3622_ = leanh::lean_ctor_get(v_t_3618_, 2);
                v_shift_3623_ = leanh::lean_ctor_get_usize(v_t_3618_, 4);
                v_tailOff_3624_ = leanh::lean_ctor_get(v_t_3618_, 3);
                v_isSharedCheck_3642_ = (!leanh::lean_is_exclusive(v_t_3618_)) as u8;
                if v_isSharedCheck_3642_ == 0 {
                    v___x_3626_ = v_t_3618_;
                    v_isShared_3627_ = v_isSharedCheck_3642_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tailOff_3624_);
                    leanh::lean_inc(v_size_3622_);
                    leanh::lean_inc(v_tail_3621_);
                    leanh::lean_inc(v_root_3620_);
                    leanh::lean_dec(v_t_3618_);
                    v___x_3626_ = leanh::lean_box(0);
                    v_isShared_3627_ = v_isSharedCheck_3642_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3628_ = lean_array_push(v_tail_3621_, v_a_3619_);
                v___x_3629_ = leanh::lean_unsigned_to_nat(1);
                v___x_3630_ = lean_nat_add(v_size_3622_, v___x_3629_);
                leanh::lean_inc_ref(v___x_3628_);
                if v_isShared_3627_ == 0 {
                    leanh::lean_ctor_set(v___x_3626_, 2, v___x_3630_);
                    leanh::lean_ctor_set(v___x_3626_, 1, v___x_3628_);
                    v_r_3632_ = v___x_3626_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3641_ = leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_root_3620_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 1, v___x_3628_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 2, v___x_3630_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 3, v_tailOff_3624_);
                    leanh::lean_ctor_set_usize(v_reuseFailAlloc_3641_, 4, v_shift_3623_);
                    v_r_3632_ = v_reuseFailAlloc_3641_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3636_ = lean_array_get_size(v___x_3628_);
                leanh::lean_dec_ref(v___x_3628_);
                v___x_3637_ = leanh::lean_unsigned_to_nat(32);
                v___x_3638_ = lean_nat_dec_lt(v___x_3636_, v___x_3637_);
                if v___x_3638_ == 0 {
                    v___x_3639_ = l_Lean_PersistentArray_tooBig;
                    v___x_3640_ = lean_nat_dec_le(v___x_3639_, v_size_3622_);
                    leanh::lean_dec(v_size_3622_);
                    v___y_3634_ = v___x_3640_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v_size_3622_);
                    v___y_3634_ = v___x_3638_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_3634_ == 0 {
                    v___x_3635_ = l_Lean_PersistentArray_mkNewTail___redArg(v_r_3632_);
                    return v___x_3635_;
                } else {
                    return v_r_3632_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_push(
    mut v_00_u03b1_3643_: *mut leanh::LeanObject,
    mut v_t_3644_: *mut leanh::LeanObject,
    mut v_a_3645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3646_ = l_Lean_PersistentArray_push___redArg(v_t_3644_, v_a_3645_);
    return v___x_3646_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(
    mut v_00_u03b1_3647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3648_ = leanh::lean_unsigned_to_nat(32);
    v___x_3649_ = lean_mk_empty_array_with_capacity(v___x_3648_);
    return v___x_3649_;
}
pub unsafe fn _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3650_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(
        leanh::lean_box(0),
    );
    return v___x_3650_;
}
pub unsafe fn _init_l_Lean_PersistentArray_popLeaf___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3651_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PersistentArray_popLeaf___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_PersistentArray_popLeaf___redArg___closed__0_once),
        _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0,
    );
    v___x_3652_ = leanh::lean_box(0);
    v___x_3653_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3653_, 0, v___x_3652_);
    leanh::lean_ctor_set(v___x_3653_, 1, v___x_3651_);
    return v___x_3653_;
}
pub unsafe fn l_Lean_PersistentArray_popLeaf___redArg(
    mut v_x_3654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3658_: u8 = 0;
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: u8 = 0;
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_last_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3669_: u8 = 0;
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3674_: u8 = 0;
    let mut v_unused_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3680_: u8 = 0;
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cs_x27_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: u8 = 0;
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cs_x27_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: u8 = 0;
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3702_: u8 = 0;
    let mut v_unused_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3705_: u8 = 0;
    let mut v_vs_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3654_) == 0 {
                    v_cs_3655_ = leanh::lean_ctor_get(v_x_3654_, 0);
                    v_isSharedCheck_3705_ = (!leanh::lean_is_exclusive(v_x_3654_)) as u8;
                    if v_isSharedCheck_3705_ == 0 {
                        v___x_3657_ = v_x_3654_;
                        v_isShared_3658_ = v_isSharedCheck_3705_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_cs_3655_);
                        leanh::lean_dec(v_x_3654_);
                        v___x_3657_ = leanh::lean_box(0);
                        v_isShared_3658_ = v_isSharedCheck_3705_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_3706_ = leanh::lean_ctor_get(v_x_3654_, 0);
                    leanh::lean_inc_ref(v_vs_3706_);
                    leanh::lean_dec_ref_known(v_x_3654_, 1);
                    v___x_3707_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3707_, 0, v_vs_3706_);
                    v___x_3708_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentArray_popLeaf___redArg___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentArray_popLeaf___redArg___closed__0_once
                        ),
                        _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0,
                    );
                    v___x_3709_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3709_, 0, v___x_3707_);
                    leanh::lean_ctor_set(v___x_3709_, 1, v___x_3708_);
                    return v___x_3709_;
                }
            }
            1 => {
                v___x_3659_ = lean_array_get_size(v_cs_3655_);
                v___x_3660_ = leanh::lean_unsigned_to_nat(0);
                v___x_3661_ = lean_nat_dec_eq(v___x_3659_, v___x_3660_);
                if v___x_3661_ == 0 {
                    v___x_3662_ = leanh::lean_unsigned_to_nat(1);
                    v_idx_3663_ = lean_nat_sub(v___x_3659_, v___x_3662_);
                    v_last_3664_ = lean_array_fget_borrowed(v_cs_3655_, v_idx_3663_);
                    leanh::lean_inc(v_last_3664_);
                    v___x_3665_ = l_Lean_PersistentArray_popLeaf___redArg(v_last_3664_);
                    v_fst_3666_ = leanh::lean_ctor_get(v___x_3665_, 0);
                    leanh::lean_inc(v_fst_3666_);
                    if leanh::lean_obj_tag(v_fst_3666_) == 0 {
                        leanh::lean_dec(v_idx_3663_);
                        leanh::lean_del_object(v___x_3657_);
                        leanh::lean_dec_ref(v_cs_3655_);
                        v_isSharedCheck_3674_ =
                            (!leanh::lean_is_exclusive(v___x_3665_)) as u8;
                        if v_isSharedCheck_3674_ == 0 {
                            v_unused_3675_ = leanh::lean_ctor_get(v___x_3665_, 1);
                            leanh::lean_dec(v_unused_3675_);
                            v_unused_3676_ = leanh::lean_ctor_get(v___x_3665_, 0);
                            leanh::lean_dec(v_unused_3676_);
                            v___x_3668_ = v___x_3665_;
                            v_isShared_3669_ = v_isSharedCheck_3674_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3665_);
                            v___x_3668_ = leanh::lean_box(0);
                            v_isShared_3669_ = v_isSharedCheck_3674_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_3677_ = leanh::lean_ctor_get(v___x_3665_, 1);
                        v_isSharedCheck_3702_ =
                            (!leanh::lean_is_exclusive(v___x_3665_)) as u8;
                        if v_isSharedCheck_3702_ == 0 {
                            v_unused_3703_ = leanh::lean_ctor_get(v___x_3665_, 0);
                            leanh::lean_dec(v_unused_3703_);
                            v___x_3679_ = v___x_3665_;
                            v_isShared_3680_ = v_isSharedCheck_3702_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_3677_);
                            leanh::lean_dec(v___x_3665_);
                            v___x_3679_ = leanh::lean_box(0);
                            v_isShared_3680_ = v_isSharedCheck_3702_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_3657_);
                    leanh::lean_dec_ref(v_cs_3655_);
                    v___x_3704_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentArray_popLeaf___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentArray_popLeaf___redArg___closed__1_once
                        ),
                        _init_l_Lean_PersistentArray_popLeaf___redArg___closed__1,
                    );
                    return v___x_3704_;
                }
            }
            2 => {
                v___x_3670_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PersistentArray_popLeaf___redArg___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_PersistentArray_popLeaf___redArg___closed__0_once
                    ),
                    _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0,
                );
                if v_isShared_3669_ == 0 {
                    leanh::lean_ctor_set(v___x_3668_, 1, v___x_3670_);
                    v___x_3672_ = v___x_3668_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_fst_3666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 1, v___x_3670_);
                    v___x_3672_ = v_reuseFailAlloc_3673_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3672_;
            }
            4 => {
                v___x_3681_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_instInhabitedPersistentArrayNode___closed__0_once
                    ),
                    _init_l_Lean_instInhabitedPersistentArrayNode___closed__0,
                );
                v_cs_x27_3682_ = lean_array_fset(v_cs_3655_, v_idx_3663_, v___x_3681_);
                v___x_3683_ = lean_array_get_size(v_snd_3677_);
                v___x_3684_ = lean_nat_dec_eq(v___x_3683_, v___x_3660_);
                if v___x_3684_ == 0 {
                    if v_isShared_3658_ == 0 {
                        leanh::lean_ctor_set(v___x_3657_, 0, v_snd_3677_);
                        v___x_3686_ = v___x_3657_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3691_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_snd_3677_);
                        v___x_3686_ = v_reuseFailAlloc_3691_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_3677_);
                    leanh::lean_dec(v_idx_3663_);
                    leanh::lean_del_object(v___x_3657_);
                    v_cs_x27_3692_ = lean_array_pop(v_cs_x27_3682_);
                    v___x_3693_ = lean_array_get_size(v_cs_x27_3692_);
                    v___x_3694_ = lean_nat_dec_eq(v___x_3693_, v___x_3660_);
                    if v___x_3694_ == 0 {
                        if v_isShared_3680_ == 0 {
                            leanh::lean_ctor_set(v___x_3679_, 1, v_cs_x27_3692_);
                            v___x_3696_ = v___x_3679_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3697_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_fst_3666_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_cs_x27_3692_);
                            v___x_3696_ = v_reuseFailAlloc_3697_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_cs_x27_3692_);
                        v___x_3698_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_PersistentArray_popLeaf___redArg___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_PersistentArray_popLeaf___redArg___closed__0_once
                            ),
                            _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0,
                        );
                        if v_isShared_3680_ == 0 {
                            leanh::lean_ctor_set(v___x_3679_, 1, v___x_3698_);
                            v___x_3700_ = v___x_3679_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_3701_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_fst_3666_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3701_, 1, v___x_3698_);
                            v___x_3700_ = v_reuseFailAlloc_3701_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_3687_ = lean_array_fset(v_cs_x27_3682_, v_idx_3663_, v___x_3686_);
                leanh::lean_dec(v_idx_3663_);
                if v_isShared_3680_ == 0 {
                    leanh::lean_ctor_set(v___x_3679_, 1, v___x_3687_);
                    v___x_3689_ = v___x_3679_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3690_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_fst_3666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3690_, 1, v___x_3687_);
                    v___x_3689_ = v_reuseFailAlloc_3690_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3689_;
            }
            7 => {
                return v___x_3696_;
            }
            8 => {
                return v___x_3700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_popLeaf(
    mut v_00_u03b1_3710_: *mut leanh::LeanObject,
    mut v_x_3711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3712_ = l_Lean_PersistentArray_popLeaf___redArg(v_x_3711_);
    return v___x_3712_;
}
pub unsafe fn l_Lean_PersistentArray_pop___redArg(
    mut v_t_3713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_3717_: usize = 0;
    let mut v_tailOff_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: u8 = 0;
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3726_: u8 = 0;
    let mut v_snd_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3731_: u8 = 0;
    let mut v_last_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newSize_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newTailOff_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3738_: u8 = 0;
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: usize = 0;
    let mut v___x_3747_: usize = 0;
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: u8 = 0;
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: u8 = 0;
    let mut v_isSharedCheck_3755_: u8 = 0;
    let mut v_isSharedCheck_3756_: u8 = 0;
    let mut v_unused_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3763_: u8 = 0;
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v_unused_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3714_ = leanh::lean_ctor_get(v_t_3713_, 0);
                v_tail_3715_ = leanh::lean_ctor_get(v_t_3713_, 1);
                v_size_3716_ = leanh::lean_ctor_get(v_t_3713_, 2);
                v_shift_3717_ = leanh::lean_ctor_get_usize(v_t_3713_, 4);
                v_tailOff_3718_ = leanh::lean_ctor_get(v_t_3713_, 3);
                v___x_3719_ = leanh::lean_unsigned_to_nat(0);
                v___x_3720_ = lean_array_get_size(v_tail_3715_);
                v___x_3721_ = lean_nat_dec_lt(v___x_3719_, v___x_3720_);
                if v___x_3721_ == 0 {
                    leanh::lean_inc_ref(v_root_3714_);
                    v___x_3722_ = l_Lean_PersistentArray_popLeaf___redArg(v_root_3714_);
                    v_fst_3723_ = leanh::lean_ctor_get(v___x_3722_, 0);
                    leanh::lean_inc(v_fst_3723_);
                    if leanh::lean_obj_tag(v_fst_3723_) == 0 {
                        leanh::lean_dec_ref(v___x_3722_);
                        return v_t_3713_;
                    } else {
                        leanh::lean_inc(v_size_3716_);
                        v_isSharedCheck_3756_ = (!leanh::lean_is_exclusive(v_t_3713_)) as u8;
                        if v_isSharedCheck_3756_ == 0 {
                            v_unused_3757_ = leanh::lean_ctor_get(v_t_3713_, 3);
                            leanh::lean_dec(v_unused_3757_);
                            v_unused_3758_ = leanh::lean_ctor_get(v_t_3713_, 2);
                            leanh::lean_dec(v_unused_3758_);
                            v_unused_3759_ = leanh::lean_ctor_get(v_t_3713_, 1);
                            leanh::lean_dec(v_unused_3759_);
                            v_unused_3760_ = leanh::lean_ctor_get(v_t_3713_, 0);
                            leanh::lean_dec(v_unused_3760_);
                            v___x_3725_ = v_t_3713_;
                            v_isShared_3726_ = v_isSharedCheck_3756_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_t_3713_);
                            v___x_3725_ = leanh::lean_box(0);
                            v_isShared_3726_ = v_isSharedCheck_3756_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_tailOff_3718_);
                    leanh::lean_inc(v_size_3716_);
                    leanh::lean_inc_ref(v_tail_3715_);
                    leanh::lean_inc_ref(v_root_3714_);
                    v_isSharedCheck_3770_ = (!leanh::lean_is_exclusive(v_t_3713_)) as u8;
                    if v_isSharedCheck_3770_ == 0 {
                        v_unused_3771_ = leanh::lean_ctor_get(v_t_3713_, 3);
                        leanh::lean_dec(v_unused_3771_);
                        v_unused_3772_ = leanh::lean_ctor_get(v_t_3713_, 2);
                        leanh::lean_dec(v_unused_3772_);
                        v_unused_3773_ = leanh::lean_ctor_get(v_t_3713_, 1);
                        leanh::lean_dec(v_unused_3773_);
                        v_unused_3774_ = leanh::lean_ctor_get(v_t_3713_, 0);
                        leanh::lean_dec(v_unused_3774_);
                        v___x_3762_ = v_t_3713_;
                        v_isShared_3763_ = v_isSharedCheck_3770_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v_t_3713_);
                        v___x_3762_ = leanh::lean_box(0);
                        v_isShared_3763_ = v_isSharedCheck_3770_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3727_ = leanh::lean_ctor_get(v___x_3722_, 1);
                leanh::lean_inc(v_snd_3727_);
                leanh::lean_dec_ref(v___x_3722_);
                v_val_3728_ = leanh::lean_ctor_get(v_fst_3723_, 0);
                v_isSharedCheck_3755_ = (!leanh::lean_is_exclusive(v_fst_3723_)) as u8;
                if v_isSharedCheck_3755_ == 0 {
                    v___x_3730_ = v_fst_3723_;
                    v_isShared_3731_ = v_isSharedCheck_3755_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_val_3728_);
                    leanh::lean_dec(v_fst_3723_);
                    v___x_3730_ = leanh::lean_box(0);
                    v_isShared_3731_ = v_isSharedCheck_3755_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_last_3732_ = lean_array_pop(v_val_3728_);
                v___x_3733_ = leanh::lean_unsigned_to_nat(1);
                v_newSize_3734_ = lean_nat_sub(v_size_3716_, v___x_3733_);
                leanh::lean_dec(v_size_3716_);
                v___x_3735_ = lean_array_get_size(v_last_3732_);
                v_newTailOff_3736_ = lean_nat_sub(v_newSize_3734_, v___x_3735_);
                v___x_3751_ = lean_array_get_size(v_snd_3727_);
                v___x_3752_ = lean_nat_dec_eq(v___x_3751_, v___x_3733_);
                if v___x_3752_ == 0 {
                    v___y_3738_ = v___x_3752_;
                    state = 3;
                    continue;
                } else {
                    v___x_3753_ = lean_array_fget_borrowed(v_snd_3727_, v___x_3719_);
                    v___x_3754_ = l_Lean_PersistentArrayNode_isNode___redArg(v___x_3753_);
                    v___y_3738_ = v___x_3754_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_3738_ == 0 {
                    if v_isShared_3731_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3730_, 0);
                        leanh::lean_ctor_set(v___x_3730_, 0, v_snd_3727_);
                        v___x_3740_ = v___x_3730_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3744_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_snd_3727_);
                        v___x_3740_ = v_reuseFailAlloc_3744_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3730_);
                    v___x_3745_ = lean_array_fget(v_snd_3727_, v___x_3719_);
                    leanh::lean_dec(v_snd_3727_);
                    v___x_3746_ = 5usize;
                    v___x_3747_ = lean_usize_sub(v_shift_3717_, v___x_3746_);
                    if v_isShared_3726_ == 0 {
                        leanh::lean_ctor_set(v___x_3725_, 3, v_newTailOff_3736_);
                        leanh::lean_ctor_set(v___x_3725_, 2, v_newSize_3734_);
                        leanh::lean_ctor_set(v___x_3725_, 1, v_last_3732_);
                        leanh::lean_ctor_set(v___x_3725_, 0, v___x_3745_);
                        v___x_3749_ = v___x_3725_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3750_ = leanh::lean_alloc_ctor(
                            0,
                            4,
                            (core::mem::size_of::<usize>() * 1) as u32,
                        );
                        leanh::lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3745_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3750_, 1, v_last_3732_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3750_, 2, v_newSize_3734_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3750_, 3, v_newTailOff_3736_);
                        v___x_3749_ = v_reuseFailAlloc_3750_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3726_ == 0 {
                    leanh::lean_ctor_set(v___x_3725_, 3, v_newTailOff_3736_);
                    leanh::lean_ctor_set(v___x_3725_, 2, v_newSize_3734_);
                    leanh::lean_ctor_set(v___x_3725_, 1, v_last_3732_);
                    leanh::lean_ctor_set(v___x_3725_, 0, v___x_3740_);
                    v___x_3742_ = v___x_3725_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3743_ = leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3740_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_last_3732_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3743_, 2, v_newSize_3734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3743_, 3, v_newTailOff_3736_);
                    leanh::lean_ctor_set_usize(v_reuseFailAlloc_3743_, 4, v_shift_3717_);
                    v___x_3742_ = v_reuseFailAlloc_3743_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3742_;
            }
            6 => {
                leanh::lean_ctor_set_usize(v___x_3749_, 4, v___x_3747_);
                return v___x_3749_;
            }
            7 => {
                v___x_3764_ = lean_array_pop(v_tail_3715_);
                v___x_3765_ = leanh::lean_unsigned_to_nat(1);
                v___x_3766_ = lean_nat_sub(v_size_3716_, v___x_3765_);
                leanh::lean_dec(v_size_3716_);
                if v_isShared_3763_ == 0 {
                    leanh::lean_ctor_set(v___x_3762_, 2, v___x_3766_);
                    leanh::lean_ctor_set(v___x_3762_, 1, v___x_3764_);
                    v___x_3768_ = v___x_3762_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3769_ = leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_root_3714_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 1, v___x_3764_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 2, v___x_3766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 3, v_tailOff_3718_);
                    leanh::lean_ctor_set_usize(v_reuseFailAlloc_3769_, 4, v_shift_3717_);
                    v___x_3768_ = v_reuseFailAlloc_3769_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_pop(
    mut v_00_u03b1_3775_: *mut leanh::LeanObject,
    mut v_t_3776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3777_ = l_Lean_PersistentArray_pop___redArg(v_t_3776_);
    return v___x_3777_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(
    mut v_inst_3778_: *mut leanh::LeanObject,
    mut v_f_3779_: *mut leanh::LeanObject,
    mut v_x_3780_: *mut leanh::LeanObject,
    mut v_x_3781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3780_) == 0 {
        let mut v_cs_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3785_: u8 = 0;
        v_cs_3782_ = leanh::lean_ctor_get(v_x_3780_, 0);
        leanh::lean_inc_ref(v_cs_3782_);
        leanh::lean_dec_ref_known(v_x_3780_, 1);
        v___x_3783_ = leanh::lean_unsigned_to_nat(0);
        v___x_3784_ = lean_array_get_size(v_cs_3782_);
        v___x_3785_ = lean_nat_dec_lt(v___x_3783_, v___x_3784_);
        if v___x_3785_ == 0 {
            let mut v_toApplicative_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_cs_3782_);
            leanh::lean_dec(v_f_3779_);
            v_toApplicative_3786_ = leanh::lean_ctor_get(v_inst_3778_, 0);
            leanh::lean_inc_ref(v_toApplicative_3786_);
            leanh::lean_dec_ref(v_inst_3778_);
            v_toPure_3787_ = leanh::lean_ctor_get(v_toApplicative_3786_, 1);
            leanh::lean_inc(v_toPure_3787_);
            leanh::lean_dec_ref(v_toApplicative_3786_);
            v___x_3788_ =
                leanh::lean_apply_2(v_toPure_3787_, leanh::lean_box(0), v_x_3781_);
            return v___x_3788_;
        } else {
            let mut v___f_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3790_: u8 = 0;
            leanh::lean_inc_ref(v_inst_3778_);
            v___f_3789_ = leanh::lean_alloc_closure(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0 as *mut core::ffi::c_void, 4, 2);
            leanh::lean_closure_set(v___f_3789_, 0, v_inst_3778_);
            leanh::lean_closure_set(v___f_3789_, 1, v_f_3779_);
            v___x_3790_ = lean_nat_dec_le(v___x_3784_, v___x_3784_);
            if v___x_3790_ == 0 {
                if v___x_3785_ == 0 {
                    let mut v_toApplicative_3791_: *mut leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_toPure_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec_ref(v___f_3789_);
                    leanh::lean_dec_ref(v_cs_3782_);
                    v_toApplicative_3791_ = leanh::lean_ctor_get(v_inst_3778_, 0);
                    leanh::lean_inc_ref(v_toApplicative_3791_);
                    leanh::lean_dec_ref(v_inst_3778_);
                    v_toPure_3792_ = leanh::lean_ctor_get(v_toApplicative_3791_, 1);
                    leanh::lean_inc(v_toPure_3792_);
                    leanh::lean_dec_ref(v_toApplicative_3791_);
                    v___x_3793_ = leanh::lean_apply_2(
                        v_toPure_3792_,
                        leanh::lean_box(0),
                        v_x_3781_,
                    );
                    return v___x_3793_;
                } else {
                    let mut v___x_3794_: usize = 0;
                    let mut v___x_3795_: usize = 0;
                    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_3794_ = 0usize;
                    v___x_3795_ = lean_usize_of_nat(v___x_3784_);
                    v___x_3796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_3778_,
                        v___f_3789_,
                        v_cs_3782_,
                        v___x_3794_,
                        v___x_3795_,
                        v_x_3781_,
                    );
                    return v___x_3796_;
                }
            } else {
                let mut v___x_3797_: usize = 0;
                let mut v___x_3798_: usize = 0;
                let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3797_ = 0usize;
                v___x_3798_ = lean_usize_of_nat(v___x_3784_);
                v___x_3799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3778_,
                    v___f_3789_,
                    v_cs_3782_,
                    v___x_3797_,
                    v___x_3798_,
                    v_x_3781_,
                );
                return v___x_3799_;
            }
        }
    } else {
        let mut v_vs_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3803_: u8 = 0;
        v_vs_3800_ = leanh::lean_ctor_get(v_x_3780_, 0);
        leanh::lean_inc_ref(v_vs_3800_);
        leanh::lean_dec_ref_known(v_x_3780_, 1);
        v___x_3801_ = leanh::lean_unsigned_to_nat(0);
        v___x_3802_ = lean_array_get_size(v_vs_3800_);
        v___x_3803_ = lean_nat_dec_lt(v___x_3801_, v___x_3802_);
        if v___x_3803_ == 0 {
            let mut v_toApplicative_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_vs_3800_);
            leanh::lean_dec(v_f_3779_);
            v_toApplicative_3804_ = leanh::lean_ctor_get(v_inst_3778_, 0);
            leanh::lean_inc_ref(v_toApplicative_3804_);
            leanh::lean_dec_ref(v_inst_3778_);
            v_toPure_3805_ = leanh::lean_ctor_get(v_toApplicative_3804_, 1);
            leanh::lean_inc(v_toPure_3805_);
            leanh::lean_dec_ref(v_toApplicative_3804_);
            v___x_3806_ =
                leanh::lean_apply_2(v_toPure_3805_, leanh::lean_box(0), v_x_3781_);
            return v___x_3806_;
        } else {
            let mut v___x_3807_: u8 = 0;
            v___x_3807_ = lean_nat_dec_le(v___x_3802_, v___x_3802_);
            if v___x_3807_ == 0 {
                if v___x_3803_ == 0 {
                    let mut v_toApplicative_3808_: *mut leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_toPure_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec_ref(v_vs_3800_);
                    leanh::lean_dec(v_f_3779_);
                    v_toApplicative_3808_ = leanh::lean_ctor_get(v_inst_3778_, 0);
                    leanh::lean_inc_ref(v_toApplicative_3808_);
                    leanh::lean_dec_ref(v_inst_3778_);
                    v_toPure_3809_ = leanh::lean_ctor_get(v_toApplicative_3808_, 1);
                    leanh::lean_inc(v_toPure_3809_);
                    leanh::lean_dec_ref(v_toApplicative_3808_);
                    v___x_3810_ = leanh::lean_apply_2(
                        v_toPure_3809_,
                        leanh::lean_box(0),
                        v_x_3781_,
                    );
                    return v___x_3810_;
                } else {
                    let mut v___x_3811_: usize = 0;
                    let mut v___x_3812_: usize = 0;
                    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_3811_ = 0usize;
                    v___x_3812_ = lean_usize_of_nat(v___x_3802_);
                    v___x_3813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_3778_,
                        v_f_3779_,
                        v_vs_3800_,
                        v___x_3811_,
                        v___x_3812_,
                        v_x_3781_,
                    );
                    return v___x_3813_;
                }
            } else {
                let mut v___x_3814_: usize = 0;
                let mut v___x_3815_: usize = 0;
                let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3814_ = 0usize;
                v___x_3815_ = lean_usize_of_nat(v___x_3802_);
                v___x_3816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3778_,
                    v_f_3779_,
                    v_vs_3800_,
                    v___x_3814_,
                    v___x_3815_,
                    v_x_3781_,
                );
                return v___x_3816_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0(
    mut v_inst_3817_: *mut leanh::LeanObject,
    mut v_f_3818_: *mut leanh::LeanObject,
    mut v_b_3819_: *mut leanh::LeanObject,
    mut v_c_3820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3821_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(
        v_inst_3817_,
        v_f_3818_,
        v_c_3820_,
        v_b_3819_,
    );
    return v___x_3821_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux(
    mut v_00_u03b1_3822_: *mut leanh::LeanObject,
    mut v_m_3823_: *mut leanh::LeanObject,
    mut v_inst_3824_: *mut leanh::LeanObject,
    mut v_00_u03b2_3825_: *mut leanh::LeanObject,
    mut v_f_3826_: *mut leanh::LeanObject,
    mut v_x_3827_: *mut leanh::LeanObject,
    mut v_x_3828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3829_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(
        v_inst_3824_,
        v_f_3826_,
        v_x_3827_,
        v_x_3828_,
    );
    return v___x_3829_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(
    mut v_j_3830_: *mut leanh::LeanObject,
    mut v_cs_3831_: *mut leanh::LeanObject,
    mut v_toApplicative_3832_: *mut leanh::LeanObject,
    mut v_inst_3833_: *mut leanh::LeanObject,
    mut v___f_3834_: *mut leanh::LeanObject,
    mut v_b_3835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: u8 = 0;
    v___x_3836_ = leanh::lean_unsigned_to_nat(1);
    v___x_3837_ = lean_nat_add(v_j_3830_, v___x_3836_);
    v___x_3838_ = lean_array_get_size(v_cs_3831_);
    v___x_3839_ = lean_nat_dec_lt(v___x_3837_, v___x_3838_);
    if v___x_3839_ == 0 {
        let mut v_toPure_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_3837_);
        leanh::lean_dec(v___f_3834_);
        leanh::lean_dec_ref(v_inst_3833_);
        leanh::lean_dec_ref(v_cs_3831_);
        v_toPure_3840_ = leanh::lean_ctor_get(v_toApplicative_3832_, 1);
        leanh::lean_inc(v_toPure_3840_);
        leanh::lean_dec_ref(v_toApplicative_3832_);
        v___x_3841_ =
            leanh::lean_apply_2(v_toPure_3840_, leanh::lean_box(0), v_b_3835_);
        return v___x_3841_;
    } else {
        let mut v___x_3842_: u8 = 0;
        v___x_3842_ = lean_nat_dec_le(v___x_3838_, v___x_3838_);
        if v___x_3842_ == 0 {
            if v___x_3839_ == 0 {
                let mut v_toPure_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_3837_);
                leanh::lean_dec(v___f_3834_);
                leanh::lean_dec_ref(v_inst_3833_);
                leanh::lean_dec_ref(v_cs_3831_);
                v_toPure_3843_ = leanh::lean_ctor_get(v_toApplicative_3832_, 1);
                leanh::lean_inc(v_toPure_3843_);
                leanh::lean_dec_ref(v_toApplicative_3832_);
                v___x_3844_ = leanh::lean_apply_2(
                    v_toPure_3843_,
                    leanh::lean_box(0),
                    v_b_3835_,
                );
                return v___x_3844_;
            } else {
                let mut v___x_3845_: usize = 0;
                let mut v___x_3846_: usize = 0;
                let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_toApplicative_3832_);
                v___x_3845_ = lean_usize_of_nat(v___x_3837_);
                leanh::lean_dec(v___x_3837_);
                v___x_3846_ = lean_usize_of_nat(v___x_3838_);
                v___x_3847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3833_,
                    v___f_3834_,
                    v_cs_3831_,
                    v___x_3845_,
                    v___x_3846_,
                    v_b_3835_,
                );
                return v___x_3847_;
            }
        } else {
            let mut v___x_3848_: usize = 0;
            let mut v___x_3849_: usize = 0;
            let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_toApplicative_3832_);
            v___x_3848_ = lean_usize_of_nat(v___x_3837_);
            leanh::lean_dec(v___x_3837_);
            v___x_3849_ = lean_usize_of_nat(v___x_3838_);
            v___x_3850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_3833_,
                v___f_3834_,
                v_cs_3831_,
                v___x_3848_,
                v___x_3849_,
                v_b_3835_,
            );
            return v___x_3850_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed(
    mut v_j_3851_: *mut leanh::LeanObject,
    mut v_cs_3852_: *mut leanh::LeanObject,
    mut v_toApplicative_3853_: *mut leanh::LeanObject,
    mut v_inst_3854_: *mut leanh::LeanObject,
    mut v___f_3855_: *mut leanh::LeanObject,
    mut v_b_3856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3857_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(v_j_3851_, v_cs_3852_, v_toApplicative_3853_, v_inst_3854_, v___f_3855_, v_b_3856_);
    leanh::lean_dec(v_j_3851_);
    return v_res_3857_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(
    mut v_inst_3858_: *mut leanh::LeanObject,
    mut v_f_3859_: *mut leanh::LeanObject,
    mut v_x_3860_: *mut leanh::LeanObject,
    mut v_x_3861_: usize,
    mut v_x_3862_: usize,
    mut v_x_3863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3860_) == 0 {
        let mut v_toApplicative_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_cs_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3869_: usize = 0;
        let mut v_j_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3873_: usize = 0;
        let mut v___x_3874_: usize = 0;
        let mut v___x_3875_: usize = 0;
        let mut v___x_3876_: usize = 0;
        let mut v___x_3877_: usize = 0;
        let mut v___x_3878_: usize = 0;
        let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_3864_ = leanh::lean_ctor_get(v_inst_3858_, 0);
        v_toBind_3865_ = leanh::lean_ctor_get(v_inst_3858_, 1);
        leanh::lean_inc(v_toBind_3865_);
        v_cs_3866_ = leanh::lean_ctor_get(v_x_3860_, 0);
        leanh::lean_inc_ref_n(v_cs_3866_, 2);
        leanh::lean_dec_ref_known(v_x_3860_, 1);
        leanh::lean_inc(v_f_3859_);
        leanh::lean_inc_ref_n(v_inst_3858_, 2);
        v___f_3867_ = leanh::lean_alloc_closure(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0 as *mut core::ffi::c_void, 4, 2);
        leanh::lean_closure_set(v___f_3867_, 0, v_inst_3858_);
        leanh::lean_closure_set(v___f_3867_, 1, v_f_3859_);
        v___x_3868_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0),
            core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0_once),
            _init_l_Lean_instInhabitedPersistentArrayNode___closed__0,
        );
        v___x_3869_ = lean_usize_shift_right(v_x_3861_, v_x_3862_);
        v_j_3870_ = lean_usize_to_nat(v___x_3869_);
        leanh::lean_inc_ref(v_toApplicative_3864_);
        leanh::lean_inc(v_j_3870_);
        v___f_3871_ = leanh::lean_alloc_closure(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 5);
        leanh::lean_closure_set(v___f_3871_, 0, v_j_3870_);
        leanh::lean_closure_set(v___f_3871_, 1, v_cs_3866_);
        leanh::lean_closure_set(v___f_3871_, 2, v_toApplicative_3864_);
        leanh::lean_closure_set(v___f_3871_, 3, v_inst_3858_);
        leanh::lean_closure_set(v___f_3871_, 4, v___f_3867_);
        v___x_3872_ = lean_array_get(v___x_3868_, v_cs_3866_, v_j_3870_);
        leanh::lean_dec(v_j_3870_);
        leanh::lean_dec_ref(v_cs_3866_);
        v___x_3873_ = 1usize;
        v___x_3874_ = lean_usize_shift_left(v___x_3873_, v_x_3862_);
        v___x_3875_ = lean_usize_sub(v___x_3874_, v___x_3873_);
        v___x_3876_ = lean_usize_land(v_x_3861_, v___x_3875_);
        v___x_3877_ = 5usize;
        v___x_3878_ = lean_usize_sub(v_x_3862_, v___x_3877_);
        v___x_3879_ =
            l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(
                v_inst_3858_,
                v_f_3859_,
                v___x_3872_,
                v___x_3876_,
                v___x_3878_,
                v_x_3863_,
            );
        v___x_3880_ = leanh::lean_apply_4(
            v_toBind_3865_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3879_,
            v___f_3871_,
        );
        return v___x_3880_;
    } else {
        let mut v_toApplicative_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3885_: u8 = 0;
        v_toApplicative_3881_ = leanh::lean_ctor_get(v_inst_3858_, 0);
        v_vs_3882_ = leanh::lean_ctor_get(v_x_3860_, 0);
        leanh::lean_inc_ref(v_vs_3882_);
        leanh::lean_dec_ref_known(v_x_3860_, 1);
        v___x_3883_ = lean_usize_to_nat(v_x_3861_);
        v___x_3884_ = lean_array_get_size(v_vs_3882_);
        v___x_3885_ = lean_nat_dec_lt(v___x_3883_, v___x_3884_);
        if v___x_3885_ == 0 {
            let mut v_toPure_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_toApplicative_3881_);
            leanh::lean_dec(v___x_3883_);
            leanh::lean_dec_ref(v_vs_3882_);
            leanh::lean_dec(v_f_3859_);
            leanh::lean_dec_ref(v_inst_3858_);
            v_toPure_3886_ = leanh::lean_ctor_get(v_toApplicative_3881_, 1);
            leanh::lean_inc(v_toPure_3886_);
            leanh::lean_dec_ref(v_toApplicative_3881_);
            v___x_3887_ =
                leanh::lean_apply_2(v_toPure_3886_, leanh::lean_box(0), v_x_3863_);
            return v___x_3887_;
        } else {
            let mut v___x_3888_: u8 = 0;
            v___x_3888_ = lean_nat_dec_le(v___x_3884_, v___x_3884_);
            if v___x_3888_ == 0 {
                if v___x_3885_ == 0 {
                    let mut v_toPure_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_inc_ref(v_toApplicative_3881_);
                    leanh::lean_dec(v___x_3883_);
                    leanh::lean_dec_ref(v_vs_3882_);
                    leanh::lean_dec(v_f_3859_);
                    leanh::lean_dec_ref(v_inst_3858_);
                    v_toPure_3889_ = leanh::lean_ctor_get(v_toApplicative_3881_, 1);
                    leanh::lean_inc(v_toPure_3889_);
                    leanh::lean_dec_ref(v_toApplicative_3881_);
                    v___x_3890_ = leanh::lean_apply_2(
                        v_toPure_3889_,
                        leanh::lean_box(0),
                        v_x_3863_,
                    );
                    return v___x_3890_;
                } else {
                    let mut v___x_3891_: usize = 0;
                    let mut v___x_3892_: usize = 0;
                    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_3891_ = lean_usize_of_nat(v___x_3883_);
                    leanh::lean_dec(v___x_3883_);
                    v___x_3892_ = lean_usize_of_nat(v___x_3884_);
                    v___x_3893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_3858_,
                        v_f_3859_,
                        v_vs_3882_,
                        v___x_3891_,
                        v___x_3892_,
                        v_x_3863_,
                    );
                    return v___x_3893_;
                }
            } else {
                let mut v___x_3894_: usize = 0;
                let mut v___x_3895_: usize = 0;
                let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3894_ = lean_usize_of_nat(v___x_3883_);
                leanh::lean_dec(v___x_3883_);
                v___x_3895_ = lean_usize_of_nat(v___x_3884_);
                v___x_3896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3858_,
                    v_f_3859_,
                    v_vs_3882_,
                    v___x_3894_,
                    v___x_3895_,
                    v_x_3863_,
                );
                return v___x_3896_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___boxed(
    mut v_inst_3897_: *mut leanh::LeanObject,
    mut v_f_3898_: *mut leanh::LeanObject,
    mut v_x_3899_: *mut leanh::LeanObject,
    mut v_x_3900_: *mut leanh::LeanObject,
    mut v_x_3901_: *mut leanh::LeanObject,
    mut v_x_3902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_215__boxed_3903_: usize = 0;
    let mut v_x_216__boxed_3904_: usize = 0;
    let mut v_res_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_215__boxed_3903_ = leanh::lean_unbox_usize(v_x_3900_);
    leanh::lean_dec(v_x_3900_);
    v_x_216__boxed_3904_ = leanh::lean_unbox_usize(v_x_3901_);
    leanh::lean_dec(v_x_3901_);
    v_res_3905_ =
        l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(
            v_inst_3897_,
            v_f_3898_,
            v_x_3899_,
            v_x_215__boxed_3903_,
            v_x_216__boxed_3904_,
            v_x_3902_,
        );
    return v_res_3905_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(
    mut v_00_u03b1_3906_: *mut leanh::LeanObject,
    mut v_m_3907_: *mut leanh::LeanObject,
    mut v_inst_3908_: *mut leanh::LeanObject,
    mut v_00_u03b2_3909_: *mut leanh::LeanObject,
    mut v_f_3910_: *mut leanh::LeanObject,
    mut v_x_3911_: *mut leanh::LeanObject,
    mut v_x_3912_: usize,
    mut v_x_3913_: usize,
    mut v_x_3914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3915_ =
        l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(
            v_inst_3908_,
            v_f_3910_,
            v_x_3911_,
            v_x_3912_,
            v_x_3913_,
            v_x_3914_,
        );
    return v___x_3915_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___boxed(
    mut v_00_u03b1_3916_: *mut leanh::LeanObject,
    mut v_m_3917_: *mut leanh::LeanObject,
    mut v_inst_3918_: *mut leanh::LeanObject,
    mut v_00_u03b2_3919_: *mut leanh::LeanObject,
    mut v_f_3920_: *mut leanh::LeanObject,
    mut v_x_3921_: *mut leanh::LeanObject,
    mut v_x_3922_: *mut leanh::LeanObject,
    mut v_x_3923_: *mut leanh::LeanObject,
    mut v_x_3924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_284__boxed_3925_: usize = 0;
    let mut v_x_285__boxed_3926_: usize = 0;
    let mut v_res_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_284__boxed_3925_ = leanh::lean_unbox_usize(v_x_3922_);
    leanh::lean_dec(v_x_3922_);
    v_x_285__boxed_3926_ = leanh::lean_unbox_usize(v_x_3923_);
    leanh::lean_dec(v_x_3923_);
    v_res_3927_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(
        v_00_u03b1_3916_,
        v_m_3917_,
        v_inst_3918_,
        v_00_u03b2_3919_,
        v_f_3920_,
        v_x_3921_,
        v_x_284__boxed_3925_,
        v_x_285__boxed_3926_,
        v_x_3924_,
    );
    return v_res_3927_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___redArg___lam__0(
    mut v_tail_3928_: *mut leanh::LeanObject,
    mut v___x_3929_: *mut leanh::LeanObject,
    mut v_toApplicative_3930_: *mut leanh::LeanObject,
    mut v_inst_3931_: *mut leanh::LeanObject,
    mut v_f_3932_: *mut leanh::LeanObject,
    mut v_b_3933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: u8 = 0;
    v___x_3934_ = lean_array_get_size(v_tail_3928_);
    v___x_3935_ = lean_nat_dec_lt(v___x_3929_, v___x_3934_);
    if v___x_3935_ == 0 {
        let mut v_toPure_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_3932_);
        leanh::lean_dec_ref(v_inst_3931_);
        leanh::lean_dec_ref(v_tail_3928_);
        v_toPure_3936_ = leanh::lean_ctor_get(v_toApplicative_3930_, 1);
        leanh::lean_inc(v_toPure_3936_);
        leanh::lean_dec_ref(v_toApplicative_3930_);
        v___x_3937_ =
            leanh::lean_apply_2(v_toPure_3936_, leanh::lean_box(0), v_b_3933_);
        return v___x_3937_;
    } else {
        let mut v___x_3938_: u8 = 0;
        v___x_3938_ = lean_nat_dec_le(v___x_3934_, v___x_3934_);
        if v___x_3938_ == 0 {
            if v___x_3935_ == 0 {
                let mut v_toPure_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_f_3932_);
                leanh::lean_dec_ref(v_inst_3931_);
                leanh::lean_dec_ref(v_tail_3928_);
                v_toPure_3939_ = leanh::lean_ctor_get(v_toApplicative_3930_, 1);
                leanh::lean_inc(v_toPure_3939_);
                leanh::lean_dec_ref(v_toApplicative_3930_);
                v___x_3940_ = leanh::lean_apply_2(
                    v_toPure_3939_,
                    leanh::lean_box(0),
                    v_b_3933_,
                );
                return v___x_3940_;
            } else {
                let mut v___x_3941_: usize = 0;
                let mut v___x_3942_: usize = 0;
                let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_toApplicative_3930_);
                v___x_3941_ = 0usize;
                v___x_3942_ = lean_usize_of_nat(v___x_3934_);
                v___x_3943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3931_,
                    v_f_3932_,
                    v_tail_3928_,
                    v___x_3941_,
                    v___x_3942_,
                    v_b_3933_,
                );
                return v___x_3943_;
            }
        } else {
            let mut v___x_3944_: usize = 0;
            let mut v___x_3945_: usize = 0;
            let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_toApplicative_3930_);
            v___x_3944_ = 0usize;
            v___x_3945_ = lean_usize_of_nat(v___x_3934_);
            v___x_3946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_3931_,
                v_f_3932_,
                v_tail_3928_,
                v___x_3944_,
                v___x_3945_,
                v_b_3933_,
            );
            return v___x_3946_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed(
    mut v_tail_3947_: *mut leanh::LeanObject,
    mut v___x_3948_: *mut leanh::LeanObject,
    mut v_toApplicative_3949_: *mut leanh::LeanObject,
    mut v_inst_3950_: *mut leanh::LeanObject,
    mut v_f_3951_: *mut leanh::LeanObject,
    mut v_b_3952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3953_ = l_Lean_PersistentArray_foldlM___redArg___lam__0(
        v_tail_3947_,
        v___x_3948_,
        v_toApplicative_3949_,
        v_inst_3950_,
        v_f_3951_,
        v_b_3952_,
    );
    leanh::lean_dec(v___x_3948_);
    return v_res_3953_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___redArg(
    mut v_inst_3954_: *mut leanh::LeanObject,
    mut v_t_3955_: *mut leanh::LeanObject,
    mut v_f_3956_: *mut leanh::LeanObject,
    mut v_init_3957_: *mut leanh::LeanObject,
    mut v_start_3958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: u8 = 0;
    v___x_3959_ = leanh::lean_unsigned_to_nat(0);
    v___x_3960_ = lean_nat_dec_eq(v_start_3958_, v___x_3959_);
    if v___x_3960_ == 0 {
        let mut v_root_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_3963_: usize = 0;
        let mut v_tailOff_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3965_: u8 = 0;
        v_root_3961_ = leanh::lean_ctor_get(v_t_3955_, 0);
        leanh::lean_inc_ref(v_root_3961_);
        v_tail_3962_ = leanh::lean_ctor_get(v_t_3955_, 1);
        leanh::lean_inc_ref(v_tail_3962_);
        v_shift_3963_ = leanh::lean_ctor_get_usize(v_t_3955_, 4);
        v_tailOff_3964_ = leanh::lean_ctor_get(v_t_3955_, 3);
        leanh::lean_inc(v_tailOff_3964_);
        leanh::lean_dec_ref(v_t_3955_);
        v___x_3965_ = lean_nat_dec_le(v_tailOff_3964_, v_start_3958_);
        if v___x_3965_ == 0 {
            let mut v_toApplicative_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3969_: usize = 0;
            let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_tailOff_3964_);
            v_toApplicative_3966_ = leanh::lean_ctor_get(v_inst_3954_, 0);
            v_toBind_3967_ = leanh::lean_ctor_get(v_inst_3954_, 1);
            leanh::lean_inc(v_toBind_3967_);
            leanh::lean_inc(v_f_3956_);
            leanh::lean_inc_ref(v_inst_3954_);
            leanh::lean_inc_ref(v_toApplicative_3966_);
            v___f_3968_ = leanh::lean_alloc_closure(
                l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            leanh::lean_closure_set(v___f_3968_, 0, v_tail_3962_);
            leanh::lean_closure_set(v___f_3968_, 1, v___x_3959_);
            leanh::lean_closure_set(v___f_3968_, 2, v_toApplicative_3966_);
            leanh::lean_closure_set(v___f_3968_, 3, v_inst_3954_);
            leanh::lean_closure_set(v___f_3968_, 4, v_f_3956_);
            v___x_3969_ = lean_usize_of_nat(v_start_3958_);
            v___x_3970_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_3954_, v_f_3956_, v_root_3961_, v___x_3969_, v_shift_3963_, v_init_3957_);
            v___x_3971_ = leanh::lean_apply_4(
                v_toBind_3967_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_3970_,
                v___f_3968_,
            );
            return v___x_3971_;
        } else {
            let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3974_: u8 = 0;
            leanh::lean_dec_ref(v_root_3961_);
            v___x_3972_ = lean_nat_sub(v_start_3958_, v_tailOff_3964_);
            leanh::lean_dec(v_tailOff_3964_);
            v___x_3973_ = lean_array_get_size(v_tail_3962_);
            v___x_3974_ = lean_nat_dec_lt(v___x_3972_, v___x_3973_);
            if v___x_3974_ == 0 {
                let mut v_toApplicative_3975_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_3972_);
                leanh::lean_dec_ref(v_tail_3962_);
                leanh::lean_dec(v_f_3956_);
                v_toApplicative_3975_ = leanh::lean_ctor_get(v_inst_3954_, 0);
                leanh::lean_inc_ref(v_toApplicative_3975_);
                leanh::lean_dec_ref(v_inst_3954_);
                v_toPure_3976_ = leanh::lean_ctor_get(v_toApplicative_3975_, 1);
                leanh::lean_inc(v_toPure_3976_);
                leanh::lean_dec_ref(v_toApplicative_3975_);
                v___x_3977_ = leanh::lean_apply_2(
                    v_toPure_3976_,
                    leanh::lean_box(0),
                    v_init_3957_,
                );
                return v___x_3977_;
            } else {
                let mut v___x_3978_: u8 = 0;
                v___x_3978_ = lean_nat_dec_le(v___x_3973_, v___x_3973_);
                if v___x_3978_ == 0 {
                    if v___x_3974_ == 0 {
                        let mut v_toApplicative_3979_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toPure_3980_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec(v___x_3972_);
                        leanh::lean_dec_ref(v_tail_3962_);
                        leanh::lean_dec(v_f_3956_);
                        v_toApplicative_3979_ = leanh::lean_ctor_get(v_inst_3954_, 0);
                        leanh::lean_inc_ref(v_toApplicative_3979_);
                        leanh::lean_dec_ref(v_inst_3954_);
                        v_toPure_3980_ = leanh::lean_ctor_get(v_toApplicative_3979_, 1);
                        leanh::lean_inc(v_toPure_3980_);
                        leanh::lean_dec_ref(v_toApplicative_3979_);
                        v___x_3981_ = leanh::lean_apply_2(
                            v_toPure_3980_,
                            leanh::lean_box(0),
                            v_init_3957_,
                        );
                        return v___x_3981_;
                    } else {
                        let mut v___x_3982_: usize = 0;
                        let mut v___x_3983_: usize = 0;
                        let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_3982_ = lean_usize_of_nat(v___x_3972_);
                        leanh::lean_dec(v___x_3972_);
                        v___x_3983_ = lean_usize_of_nat(v___x_3973_);
                        v___x_3984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v_inst_3954_,
                            v_f_3956_,
                            v_tail_3962_,
                            v___x_3982_,
                            v___x_3983_,
                            v_init_3957_,
                        );
                        return v___x_3984_;
                    }
                } else {
                    let mut v___x_3985_: usize = 0;
                    let mut v___x_3986_: usize = 0;
                    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_3985_ = lean_usize_of_nat(v___x_3972_);
                    leanh::lean_dec(v___x_3972_);
                    v___x_3986_ = lean_usize_of_nat(v___x_3973_);
                    v___x_3987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_3954_,
                        v_f_3956_,
                        v_tail_3962_,
                        v___x_3985_,
                        v___x_3986_,
                        v_init_3957_,
                    );
                    return v___x_3987_;
                }
            }
        }
    } else {
        let mut v_toApplicative_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_root_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_3988_ = leanh::lean_ctor_get(v_inst_3954_, 0);
        v_toBind_3989_ = leanh::lean_ctor_get(v_inst_3954_, 1);
        leanh::lean_inc(v_toBind_3989_);
        v_root_3990_ = leanh::lean_ctor_get(v_t_3955_, 0);
        leanh::lean_inc_ref(v_root_3990_);
        v_tail_3991_ = leanh::lean_ctor_get(v_t_3955_, 1);
        leanh::lean_inc_ref(v_tail_3991_);
        leanh::lean_dec_ref(v_t_3955_);
        leanh::lean_inc(v_f_3956_);
        leanh::lean_inc_ref(v_inst_3954_);
        leanh::lean_inc_ref(v_toApplicative_3988_);
        v___f_3992_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            5,
        );
        leanh::lean_closure_set(v___f_3992_, 0, v_tail_3991_);
        leanh::lean_closure_set(v___f_3992_, 1, v___x_3959_);
        leanh::lean_closure_set(v___f_3992_, 2, v_toApplicative_3988_);
        leanh::lean_closure_set(v___f_3992_, 3, v_inst_3954_);
        leanh::lean_closure_set(v___f_3992_, 4, v_f_3956_);
        v___x_3993_ =
            l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(
                v_inst_3954_,
                v_f_3956_,
                v_root_3990_,
                v_init_3957_,
            );
        v___x_3994_ = leanh::lean_apply_4(
            v_toBind_3989_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3993_,
            v___f_3992_,
        );
        return v___x_3994_;
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___redArg___boxed(
    mut v_inst_3995_: *mut leanh::LeanObject,
    mut v_t_3996_: *mut leanh::LeanObject,
    mut v_f_3997_: *mut leanh::LeanObject,
    mut v_init_3998_: *mut leanh::LeanObject,
    mut v_start_3999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4000_ = l_Lean_PersistentArray_foldlM___redArg(
        v_inst_3995_,
        v_t_3996_,
        v_f_3997_,
        v_init_3998_,
        v_start_3999_,
    );
    leanh::lean_dec(v_start_3999_);
    return v_res_4000_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM(
    mut v_00_u03b1_4001_: *mut leanh::LeanObject,
    mut v_m_4002_: *mut leanh::LeanObject,
    mut v_inst_4003_: *mut leanh::LeanObject,
    mut v_00_u03b2_4004_: *mut leanh::LeanObject,
    mut v_t_4005_: *mut leanh::LeanObject,
    mut v_f_4006_: *mut leanh::LeanObject,
    mut v_init_4007_: *mut leanh::LeanObject,
    mut v_start_4008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4009_ = l_Lean_PersistentArray_foldlM___redArg(
        v_inst_4003_,
        v_t_4005_,
        v_f_4006_,
        v_init_4007_,
        v_start_4008_,
    );
    return v___x_4009_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___boxed(
    mut v_00_u03b1_4010_: *mut leanh::LeanObject,
    mut v_m_4011_: *mut leanh::LeanObject,
    mut v_inst_4012_: *mut leanh::LeanObject,
    mut v_00_u03b2_4013_: *mut leanh::LeanObject,
    mut v_t_4014_: *mut leanh::LeanObject,
    mut v_f_4015_: *mut leanh::LeanObject,
    mut v_init_4016_: *mut leanh::LeanObject,
    mut v_start_4017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4018_ = l_Lean_PersistentArray_foldlM(
        v_00_u03b1_4010_,
        v_m_4011_,
        v_inst_4012_,
        v_00_u03b2_4013_,
        v_t_4014_,
        v_f_4015_,
        v_init_4016_,
        v_start_4017_,
    );
    leanh::lean_dec(v_start_4017_);
    return v_res_4018_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(
    mut v_inst_4019_: *mut leanh::LeanObject,
    mut v_f_4020_: *mut leanh::LeanObject,
    mut v_x_4021_: *mut leanh::LeanObject,
    mut v_x_4022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4021_) == 0 {
        let mut v_cs_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4026_: u8 = 0;
        v_cs_4023_ = leanh::lean_ctor_get(v_x_4021_, 0);
        leanh::lean_inc_ref(v_cs_4023_);
        leanh::lean_dec_ref_known(v_x_4021_, 1);
        v___x_4024_ = lean_array_get_size(v_cs_4023_);
        v___x_4025_ = leanh::lean_unsigned_to_nat(0);
        v___x_4026_ = lean_nat_dec_lt(v___x_4025_, v___x_4024_);
        if v___x_4026_ == 0 {
            let mut v_toApplicative_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_cs_4023_);
            leanh::lean_dec(v_f_4020_);
            v_toApplicative_4027_ = leanh::lean_ctor_get(v_inst_4019_, 0);
            leanh::lean_inc_ref(v_toApplicative_4027_);
            leanh::lean_dec_ref(v_inst_4019_);
            v_toPure_4028_ = leanh::lean_ctor_get(v_toApplicative_4027_, 1);
            leanh::lean_inc(v_toPure_4028_);
            leanh::lean_dec_ref(v_toApplicative_4027_);
            v___x_4029_ =
                leanh::lean_apply_2(v_toPure_4028_, leanh::lean_box(0), v_x_4022_);
            return v___x_4029_;
        } else {
            let mut v___f_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4031_: usize = 0;
            let mut v___x_4032_: usize = 0;
            let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_inst_4019_);
            v___f_4030_ = leanh::lean_alloc_closure(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0 as *mut core::ffi::c_void, 4, 2);
            leanh::lean_closure_set(v___f_4030_, 0, v_inst_4019_);
            leanh::lean_closure_set(v___f_4030_, 1, v_f_4020_);
            v___x_4031_ = lean_usize_of_nat(v___x_4024_);
            v___x_4032_ = 0usize;
            v___x_4033_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_4019_,
                v___f_4030_,
                v_cs_4023_,
                v___x_4031_,
                v___x_4032_,
                v_x_4022_,
            );
            return v___x_4033_;
        }
    } else {
        let mut v_vs_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4037_: u8 = 0;
        v_vs_4034_ = leanh::lean_ctor_get(v_x_4021_, 0);
        leanh::lean_inc_ref(v_vs_4034_);
        leanh::lean_dec_ref_known(v_x_4021_, 1);
        v___x_4035_ = lean_array_get_size(v_vs_4034_);
        v___x_4036_ = leanh::lean_unsigned_to_nat(0);
        v___x_4037_ = lean_nat_dec_lt(v___x_4036_, v___x_4035_);
        if v___x_4037_ == 0 {
            let mut v_toApplicative_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_vs_4034_);
            leanh::lean_dec(v_f_4020_);
            v_toApplicative_4038_ = leanh::lean_ctor_get(v_inst_4019_, 0);
            leanh::lean_inc_ref(v_toApplicative_4038_);
            leanh::lean_dec_ref(v_inst_4019_);
            v_toPure_4039_ = leanh::lean_ctor_get(v_toApplicative_4038_, 1);
            leanh::lean_inc(v_toPure_4039_);
            leanh::lean_dec_ref(v_toApplicative_4038_);
            v___x_4040_ =
                leanh::lean_apply_2(v_toPure_4039_, leanh::lean_box(0), v_x_4022_);
            return v___x_4040_;
        } else {
            let mut v___x_4041_: usize = 0;
            let mut v___x_4042_: usize = 0;
            let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4041_ = lean_usize_of_nat(v___x_4035_);
            v___x_4042_ = 0usize;
            v___x_4043_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_4019_,
                v_f_4020_,
                v_vs_4034_,
                v___x_4041_,
                v___x_4042_,
                v_x_4022_,
            );
            return v___x_4043_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0(
    mut v_inst_4044_: *mut leanh::LeanObject,
    mut v_f_4045_: *mut leanh::LeanObject,
    mut v_c_4046_: *mut leanh::LeanObject,
    mut v_b_4047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4048_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(
        v_inst_4044_,
        v_f_4045_,
        v_c_4046_,
        v_b_4047_,
    );
    return v___x_4048_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux(
    mut v_00_u03b1_4049_: *mut leanh::LeanObject,
    mut v_m_4050_: *mut leanh::LeanObject,
    mut v_00_u03b2_4051_: *mut leanh::LeanObject,
    mut v_inst_4052_: *mut leanh::LeanObject,
    mut v_f_4053_: *mut leanh::LeanObject,
    mut v_x_4054_: *mut leanh::LeanObject,
    mut v_x_4055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4056_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(
        v_inst_4052_,
        v_f_4053_,
        v_x_4054_,
        v_x_4055_,
    );
    return v___x_4056_;
}
pub unsafe fn l_Lean_PersistentArray_foldrM___redArg___lam__0(
    mut v_inst_4057_: *mut leanh::LeanObject,
    mut v_f_4058_: *mut leanh::LeanObject,
    mut v_root_4059_: *mut leanh::LeanObject,
    mut v_____do__lift_4060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4061_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(
        v_inst_4057_,
        v_f_4058_,
        v_root_4059_,
        v_____do__lift_4060_,
    );
    return v___x_4061_;
}
pub unsafe fn l_Lean_PersistentArray_foldrM___redArg(
    mut v_inst_4062_: *mut leanh::LeanObject,
    mut v_t_4063_: *mut leanh::LeanObject,
    mut v_f_4064_: *mut leanh::LeanObject,
    mut v_init_4065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: u8 = 0;
    v_toApplicative_4066_ = leanh::lean_ctor_get(v_inst_4062_, 0);
    v_toBind_4067_ = leanh::lean_ctor_get(v_inst_4062_, 1);
    leanh::lean_inc(v_toBind_4067_);
    v_root_4068_ = leanh::lean_ctor_get(v_t_4063_, 0);
    leanh::lean_inc_ref(v_root_4068_);
    v_tail_4069_ = leanh::lean_ctor_get(v_t_4063_, 1);
    leanh::lean_inc_ref(v_tail_4069_);
    leanh::lean_dec_ref(v_t_4063_);
    leanh::lean_inc(v_f_4064_);
    leanh::lean_inc_ref(v_inst_4062_);
    v___f_4070_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_4070_, 0, v_inst_4062_);
    leanh::lean_closure_set(v___f_4070_, 1, v_f_4064_);
    leanh::lean_closure_set(v___f_4070_, 2, v_root_4068_);
    v___x_4071_ = lean_array_get_size(v_tail_4069_);
    v___x_4072_ = leanh::lean_unsigned_to_nat(0);
    v___x_4073_ = lean_nat_dec_lt(v___x_4072_, v___x_4071_);
    if v___x_4073_ == 0 {
        let mut v_toPure_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_toApplicative_4066_);
        leanh::lean_dec_ref(v_tail_4069_);
        leanh::lean_dec(v_f_4064_);
        leanh::lean_dec_ref(v_inst_4062_);
        v_toPure_4074_ = leanh::lean_ctor_get(v_toApplicative_4066_, 1);
        leanh::lean_inc(v_toPure_4074_);
        leanh::lean_dec_ref(v_toApplicative_4066_);
        v___x_4075_ =
            leanh::lean_apply_2(v_toPure_4074_, leanh::lean_box(0), v_init_4065_);
        v___x_4076_ = leanh::lean_apply_4(
            v_toBind_4067_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4075_,
            v___f_4070_,
        );
        return v___x_4076_;
    } else {
        let mut v___x_4077_: usize = 0;
        let mut v___x_4078_: usize = 0;
        let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4077_ = lean_usize_of_nat(v___x_4071_);
        v___x_4078_ = 0usize;
        v___x_4079_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_4062_,
            v_f_4064_,
            v_tail_4069_,
            v___x_4077_,
            v___x_4078_,
            v_init_4065_,
        );
        v___x_4080_ = leanh::lean_apply_4(
            v_toBind_4067_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4079_,
            v___f_4070_,
        );
        return v___x_4080_;
    }
}
pub unsafe fn l_Lean_PersistentArray_foldrM(
    mut v_00_u03b1_4081_: *mut leanh::LeanObject,
    mut v_m_4082_: *mut leanh::LeanObject,
    mut v_00_u03b2_4083_: *mut leanh::LeanObject,
    mut v_inst_4084_: *mut leanh::LeanObject,
    mut v_t_4085_: *mut leanh::LeanObject,
    mut v_f_4086_: *mut leanh::LeanObject,
    mut v_init_4087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4088_ =
        l_Lean_PersistentArray_foldrM___redArg(v_inst_4084_, v_t_4085_, v_f_4086_, v_init_4087_);
    return v___x_4088_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___redArg___lam__0(
    mut v_toPure_4089_: *mut leanh::LeanObject,
    mut v_____s_4090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_4091_ = leanh::lean_ctor_get(v_____s_4090_, 0);
    if leanh::lean_obj_tag(v_fst_4091_) == 0 {
        let mut v_snd_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_snd_4092_ = leanh::lean_ctor_get(v_____s_4090_, 1);
        leanh::lean_inc(v_snd_4092_);
        leanh::lean_dec_ref(v_____s_4090_);
        v___x_4093_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4093_, 0, v_snd_4092_);
        v___x_4094_ =
            leanh::lean_apply_2(v_toPure_4089_, leanh::lean_box(0), v___x_4093_);
        return v___x_4094_;
    } else {
        let mut v_val_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_fst_4091_);
        leanh::lean_dec_ref(v_____s_4090_);
        v_val_4095_ = leanh::lean_ctor_get(v_fst_4091_, 0);
        leanh::lean_inc(v_val_4095_);
        leanh::lean_dec_ref_known(v_fst_4091_, 1);
        v___x_4096_ =
            leanh::lean_apply_2(v_toPure_4089_, leanh::lean_box(0), v_val_4095_);
        return v___x_4096_;
    }
}
pub unsafe fn l_Lean_PersistentArray_forInAux___redArg___lam__1(
    mut v_snd_4097_: *mut leanh::LeanObject,
    mut v_toPure_4098_: *mut leanh::LeanObject,
    mut v___x_4099_: *mut leanh::LeanObject,
    mut v_____do__lift_4100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4108_: u8 = 0;
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_4100_) == 0 {
                    leanh::lean_dec(v___x_4099_);
                    v___x_4101_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4101_, 0, v_____do__lift_4100_);
                    v___x_4102_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4102_, 0, v___x_4101_);
                    leanh::lean_ctor_set(v___x_4102_, 1, v_snd_4097_);
                    v___x_4103_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4103_, 0, v___x_4102_);
                    v___x_4104_ = leanh::lean_apply_2(
                        v_toPure_4098_,
                        leanh::lean_box(0),
                        v___x_4103_,
                    );
                    return v___x_4104_;
                } else {
                    leanh::lean_dec(v_snd_4097_);
                    v_a_4105_ = leanh::lean_ctor_get(v_____do__lift_4100_, 0);
                    v_isSharedCheck_4114_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_4100_)) as u8;
                    if v_isSharedCheck_4114_ == 0 {
                        v___x_4107_ = v_____do__lift_4100_;
                        v_isShared_4108_ = v_isSharedCheck_4114_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4105_);
                        leanh::lean_dec(v_____do__lift_4100_);
                        v___x_4107_ = leanh::lean_box(0);
                        v_isShared_4108_ = v_isSharedCheck_4114_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4109_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4109_, 0, v___x_4099_);
                leanh::lean_ctor_set(v___x_4109_, 1, v_a_4105_);
                if v_isShared_4108_ == 0 {
                    leanh::lean_ctor_set(v___x_4107_, 0, v___x_4109_);
                    v___x_4111_ = v___x_4107_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4109_);
                    v___x_4111_ = v_reuseFailAlloc_4113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4112_ = leanh::lean_apply_2(
                    v_toPure_4098_,
                    leanh::lean_box(0),
                    v___x_4111_,
                );
                return v___x_4112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forInAux___redArg___lam__5(
    mut v_toPure_4115_: *mut leanh::LeanObject,
    mut v___x_4116_: *mut leanh::LeanObject,
    mut v_f_4117_: *mut leanh::LeanObject,
    mut v_toBind_4118_: *mut leanh::LeanObject,
    mut v_a_4119_: *mut leanh::LeanObject,
    mut v_x_4120_: *mut leanh::LeanObject,
    mut v___y_4121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_4122_ = leanh::lean_ctor_get(v___y_4121_, 1);
    leanh::lean_inc_n(v_snd_4122_, 2);
    leanh::lean_dec_ref(v___y_4121_);
    v___f_4123_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_forInAux___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_4123_, 0, v_snd_4122_);
    leanh::lean_closure_set(v___f_4123_, 1, v_toPure_4115_);
    leanh::lean_closure_set(v___f_4123_, 2, v___x_4116_);
    v___x_4124_ = leanh::lean_apply_2(v_f_4117_, v_a_4119_, v_snd_4122_);
    v___x_4125_ = leanh::lean_apply_4(
        v_toBind_4118_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4124_,
        v___f_4123_,
    );
    return v___x_4125_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed(
    mut v_toPure_4126_: *mut leanh::LeanObject,
    mut v___x_4127_: *mut leanh::LeanObject,
    mut v_inst_4128_: *mut leanh::LeanObject,
    mut v_f_4129_: *mut leanh::LeanObject,
    mut v_toBind_4130_: *mut leanh::LeanObject,
    mut v_a_4131_: *mut leanh::LeanObject,
    mut v_x_4132_: *mut leanh::LeanObject,
    mut v___y_4133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4134_ = l_Lean_PersistentArray_forInAux___redArg___lam__2(
        v_toPure_4126_,
        v___x_4127_,
        v_inst_4128_,
        v_f_4129_,
        v_toBind_4130_,
        v_a_4131_,
        v_x_4132_,
        v___y_4133_,
    );
    leanh::lean_dec_ref(v_a_4131_);
    return v_res_4134_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___redArg(
    mut v_inst_4135_: *mut leanh::LeanObject,
    mut v_f_4136_: *mut leanh::LeanObject,
    mut v_n_4137_: *mut leanh::LeanObject,
    mut v_b_4138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_n_4137_) == 0 {
        let mut v_toApplicative_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_cs_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4147_: usize = 0;
        let mut v___x_4148_: usize = 0;
        let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_4139_ = leanh::lean_ctor_get(v_inst_4135_, 0);
        v_toBind_4140_ = leanh::lean_ctor_get(v_inst_4135_, 1);
        leanh::lean_inc_n(v_toBind_4140_, 2);
        v_toPure_4141_ = leanh::lean_ctor_get(v_toApplicative_4139_, 1);
        v_cs_4142_ = leanh::lean_ctor_get(v_n_4137_, 0);
        leanh::lean_inc_n(v_toPure_4141_, 2);
        v___f_4143_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_forInAux___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_4143_, 0, v_toPure_4141_);
        v___x_4144_ = leanh::lean_box(0);
        leanh::lean_inc_ref(v_inst_4135_);
        v___f_4145_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed as *mut core::ffi::c_void,
            8,
            5,
        );
        leanh::lean_closure_set(v___f_4145_, 0, v_toPure_4141_);
        leanh::lean_closure_set(v___f_4145_, 1, v___x_4144_);
        leanh::lean_closure_set(v___f_4145_, 2, v_inst_4135_);
        leanh::lean_closure_set(v___f_4145_, 3, v_f_4136_);
        leanh::lean_closure_set(v___f_4145_, 4, v_toBind_4140_);
        v___x_4146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4146_, 0, v___x_4144_);
        leanh::lean_ctor_set(v___x_4146_, 1, v_b_4138_);
        v_sz_4147_ = lean_array_size(v_cs_4142_);
        v___x_4148_ = 0usize;
        leanh::lean_inc_ref(v_cs_4142_);
        v___x_4149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_4135_,
            v_cs_4142_,
            v___f_4145_,
            v_sz_4147_,
            v___x_4148_,
            v___x_4146_,
        );
        v___x_4150_ = leanh::lean_apply_4(
            v_toBind_4140_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4149_,
            v___f_4143_,
        );
        return v___x_4150_;
    } else {
        let mut v_toApplicative_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4159_: usize = 0;
        let mut v___x_4160_: usize = 0;
        let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_4151_ = leanh::lean_ctor_get(v_inst_4135_, 0);
        v_toBind_4152_ = leanh::lean_ctor_get(v_inst_4135_, 1);
        leanh::lean_inc_n(v_toBind_4152_, 2);
        v_toPure_4153_ = leanh::lean_ctor_get(v_toApplicative_4151_, 1);
        v_vs_4154_ = leanh::lean_ctor_get(v_n_4137_, 0);
        leanh::lean_inc_n(v_toPure_4153_, 2);
        v___f_4155_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_forInAux___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_4155_, 0, v_toPure_4153_);
        v___x_4156_ = leanh::lean_box(0);
        v___f_4157_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_forInAux___redArg___lam__5 as *mut core::ffi::c_void,
            7,
            4,
        );
        leanh::lean_closure_set(v___f_4157_, 0, v_toPure_4153_);
        leanh::lean_closure_set(v___f_4157_, 1, v___x_4156_);
        leanh::lean_closure_set(v___f_4157_, 2, v_f_4136_);
        leanh::lean_closure_set(v___f_4157_, 3, v_toBind_4152_);
        v___x_4158_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4158_, 0, v___x_4156_);
        leanh::lean_ctor_set(v___x_4158_, 1, v_b_4138_);
        v_sz_4159_ = lean_array_size(v_vs_4154_);
        v___x_4160_ = 0usize;
        leanh::lean_inc_ref(v_vs_4154_);
        v___x_4161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_4135_,
            v_vs_4154_,
            v___f_4157_,
            v_sz_4159_,
            v___x_4160_,
            v___x_4158_,
        );
        v___x_4162_ = leanh::lean_apply_4(
            v_toBind_4152_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4161_,
            v___f_4155_,
        );
        return v___x_4162_;
    }
}
pub unsafe fn l_Lean_PersistentArray_forInAux___redArg___lam__2(
    mut v_toPure_4163_: *mut leanh::LeanObject,
    mut v___x_4164_: *mut leanh::LeanObject,
    mut v_inst_4165_: *mut leanh::LeanObject,
    mut v_f_4166_: *mut leanh::LeanObject,
    mut v_toBind_4167_: *mut leanh::LeanObject,
    mut v_a_4168_: *mut leanh::LeanObject,
    mut v_x_4169_: *mut leanh::LeanObject,
    mut v___y_4170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_4171_ = leanh::lean_ctor_get(v___y_4170_, 1);
    leanh::lean_inc_n(v_snd_4171_, 2);
    leanh::lean_dec_ref(v___y_4170_);
    v___f_4172_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_forInAux___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_4172_, 0, v_snd_4171_);
    leanh::lean_closure_set(v___f_4172_, 1, v_toPure_4163_);
    leanh::lean_closure_set(v___f_4172_, 2, v___x_4164_);
    v___x_4173_ =
        l_Lean_PersistentArray_forInAux___redArg(v_inst_4165_, v_f_4166_, v_a_4168_, v_snd_4171_);
    v___x_4174_ = leanh::lean_apply_4(
        v_toBind_4167_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4173_,
        v___f_4172_,
    );
    return v___x_4174_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___redArg___boxed(
    mut v_inst_4175_: *mut leanh::LeanObject,
    mut v_f_4176_: *mut leanh::LeanObject,
    mut v_n_4177_: *mut leanh::LeanObject,
    mut v_b_4178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4179_ =
        l_Lean_PersistentArray_forInAux___redArg(v_inst_4175_, v_f_4176_, v_n_4177_, v_b_4178_);
    leanh::lean_dec_ref(v_n_4177_);
    return v_res_4179_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux(
    mut v_00_u03b1_4180_: *mut leanh::LeanObject,
    mut v_00_u03b2_4181_: *mut leanh::LeanObject,
    mut v_m_4182_: *mut leanh::LeanObject,
    mut v_inst_4183_: *mut leanh::LeanObject,
    mut v_inh_4184_: *mut leanh::LeanObject,
    mut v_f_4185_: *mut leanh::LeanObject,
    mut v_n_4186_: *mut leanh::LeanObject,
    mut v_b_4187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4188_ =
        l_Lean_PersistentArray_forInAux___redArg(v_inst_4183_, v_f_4185_, v_n_4186_, v_b_4187_);
    return v___x_4188_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___boxed(
    mut v_00_u03b1_4189_: *mut leanh::LeanObject,
    mut v_00_u03b2_4190_: *mut leanh::LeanObject,
    mut v_m_4191_: *mut leanh::LeanObject,
    mut v_inst_4192_: *mut leanh::LeanObject,
    mut v_inh_4193_: *mut leanh::LeanObject,
    mut v_f_4194_: *mut leanh::LeanObject,
    mut v_n_4195_: *mut leanh::LeanObject,
    mut v_b_4196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4197_ = l_Lean_PersistentArray_forInAux(
        v_00_u03b1_4189_,
        v_00_u03b2_4190_,
        v_m_4191_,
        v_inst_4192_,
        v_inh_4193_,
        v_f_4194_,
        v_n_4195_,
        v_b_4196_,
    );
    leanh::lean_dec_ref(v_n_4195_);
    leanh::lean_dec(v_inh_4193_);
    return v_res_4197_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___redArg___lam__0(
    mut v_toPure_4198_: *mut leanh::LeanObject,
    mut v_____s_4199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_4200_ = leanh::lean_ctor_get(v_____s_4199_, 0);
    if leanh::lean_obj_tag(v_fst_4200_) == 0 {
        let mut v_snd_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_snd_4201_ = leanh::lean_ctor_get(v_____s_4199_, 1);
        leanh::lean_inc(v_snd_4201_);
        leanh::lean_dec_ref(v_____s_4199_);
        v___x_4202_ =
            leanh::lean_apply_2(v_toPure_4198_, leanh::lean_box(0), v_snd_4201_);
        return v___x_4202_;
    } else {
        let mut v_val_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_fst_4200_);
        leanh::lean_dec_ref(v_____s_4199_);
        v_val_4203_ = leanh::lean_ctor_get(v_fst_4200_, 0);
        leanh::lean_inc(v_val_4203_);
        leanh::lean_dec_ref_known(v_fst_4200_, 1);
        v___x_4204_ =
            leanh::lean_apply_2(v_toPure_4198_, leanh::lean_box(0), v_val_4203_);
        return v___x_4204_;
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___redArg___lam__1(
    mut v_snd_4205_: *mut leanh::LeanObject,
    mut v_toPure_4206_: *mut leanh::LeanObject,
    mut v___x_4207_: *mut leanh::LeanObject,
    mut v_____do__lift_4208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4212_: u8 = 0;
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4219_: u8 = 0;
    let mut v_a_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4223_: u8 = 0;
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_4208_) == 0 {
                    leanh::lean_dec(v___x_4207_);
                    v_a_4209_ = leanh::lean_ctor_get(v_____do__lift_4208_, 0);
                    v_isSharedCheck_4219_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_4208_)) as u8;
                    if v_isSharedCheck_4219_ == 0 {
                        v___x_4211_ = v_____do__lift_4208_;
                        v_isShared_4212_ = v_isSharedCheck_4219_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4209_);
                        leanh::lean_dec(v_____do__lift_4208_);
                        v___x_4211_ = leanh::lean_box(0);
                        v_isShared_4212_ = v_isSharedCheck_4219_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_4205_);
                    v_a_4220_ = leanh::lean_ctor_get(v_____do__lift_4208_, 0);
                    v_isSharedCheck_4229_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_4208_)) as u8;
                    if v_isSharedCheck_4229_ == 0 {
                        v___x_4222_ = v_____do__lift_4208_;
                        v_isShared_4223_ = v_isSharedCheck_4229_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4220_);
                        leanh::lean_dec(v_____do__lift_4208_);
                        v___x_4222_ = leanh::lean_box(0);
                        v_isShared_4223_ = v_isSharedCheck_4229_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4213_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4213_, 0, v_a_4209_);
                v___x_4214_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4214_, 0, v___x_4213_);
                leanh::lean_ctor_set(v___x_4214_, 1, v_snd_4205_);
                if v_isShared_4212_ == 0 {
                    leanh::lean_ctor_set(v___x_4211_, 0, v___x_4214_);
                    v___x_4216_ = v___x_4211_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4218_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4214_);
                    v___x_4216_ = v_reuseFailAlloc_4218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4217_ = leanh::lean_apply_2(
                    v_toPure_4206_,
                    leanh::lean_box(0),
                    v___x_4216_,
                );
                return v___x_4217_;
            }
            3 => {
                v___x_4224_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4224_, 0, v___x_4207_);
                leanh::lean_ctor_set(v___x_4224_, 1, v_a_4220_);
                if v_isShared_4223_ == 0 {
                    leanh::lean_ctor_set(v___x_4222_, 0, v___x_4224_);
                    v___x_4226_ = v___x_4222_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4228_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4224_);
                    v___x_4226_ = v_reuseFailAlloc_4228_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4227_ = leanh::lean_apply_2(
                    v_toPure_4206_,
                    leanh::lean_box(0),
                    v___x_4226_,
                );
                return v___x_4227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___redArg___lam__2(
    mut v_toPure_4230_: *mut leanh::LeanObject,
    mut v___x_4231_: *mut leanh::LeanObject,
    mut v_f_4232_: *mut leanh::LeanObject,
    mut v_toBind_4233_: *mut leanh::LeanObject,
    mut v_a_4234_: *mut leanh::LeanObject,
    mut v_x_4235_: *mut leanh::LeanObject,
    mut v___y_4236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_4237_ = leanh::lean_ctor_get(v___y_4236_, 1);
    leanh::lean_inc_n(v_snd_4237_, 2);
    leanh::lean_dec_ref(v___y_4236_);
    v___f_4238_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_4238_, 0, v_snd_4237_);
    leanh::lean_closure_set(v___f_4238_, 1, v_toPure_4230_);
    leanh::lean_closure_set(v___f_4238_, 2, v___x_4231_);
    v___x_4239_ = leanh::lean_apply_2(v_f_4232_, v_a_4234_, v_snd_4237_);
    v___x_4240_ = leanh::lean_apply_4(
        v_toBind_4233_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4239_,
        v___f_4238_,
    );
    return v___x_4240_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___redArg___lam__3(
    mut v_toPure_4241_: *mut leanh::LeanObject,
    mut v_f_4242_: *mut leanh::LeanObject,
    mut v_toBind_4243_: *mut leanh::LeanObject,
    mut v_tail_4244_: *mut leanh::LeanObject,
    mut v_inst_4245_: *mut leanh::LeanObject,
    mut v___f_4246_: *mut leanh::LeanObject,
    mut v_____do__lift_4247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_4247_) == 0 {
        let mut v_a_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_4246_);
        leanh::lean_dec_ref(v_inst_4245_);
        leanh::lean_dec_ref(v_tail_4244_);
        leanh::lean_dec(v_toBind_4243_);
        leanh::lean_dec(v_f_4242_);
        v_a_4248_ = leanh::lean_ctor_get(v_____do__lift_4247_, 0);
        leanh::lean_inc(v_a_4248_);
        leanh::lean_dec_ref_known(v_____do__lift_4247_, 1);
        v___x_4249_ =
            leanh::lean_apply_2(v_toPure_4241_, leanh::lean_box(0), v_a_4248_);
        return v___x_4249_;
    } else {
        let mut v_a_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4254_: usize = 0;
        let mut v___x_4255_: usize = 0;
        let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4250_ = leanh::lean_ctor_get(v_____do__lift_4247_, 0);
        leanh::lean_inc(v_a_4250_);
        leanh::lean_dec_ref_known(v_____do__lift_4247_, 1);
        v___x_4251_ = leanh::lean_box(0);
        leanh::lean_inc(v_toBind_4243_);
        v___f_4252_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_forIn___redArg___lam__2 as *mut core::ffi::c_void,
            7,
            4,
        );
        leanh::lean_closure_set(v___f_4252_, 0, v_toPure_4241_);
        leanh::lean_closure_set(v___f_4252_, 1, v___x_4251_);
        leanh::lean_closure_set(v___f_4252_, 2, v_f_4242_);
        leanh::lean_closure_set(v___f_4252_, 3, v_toBind_4243_);
        v___x_4253_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4253_, 0, v___x_4251_);
        leanh::lean_ctor_set(v___x_4253_, 1, v_a_4250_);
        v_sz_4254_ = lean_array_size(v_tail_4244_);
        v___x_4255_ = 0usize;
        v___x_4256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_4245_,
            v_tail_4244_,
            v___f_4252_,
            v_sz_4254_,
            v___x_4255_,
            v___x_4253_,
        );
        v___x_4257_ = leanh::lean_apply_4(
            v_toBind_4243_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4256_,
            v___f_4246_,
        );
        return v___x_4257_;
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___redArg(
    mut v_inst_4258_: *mut leanh::LeanObject,
    mut v_t_4259_: *mut leanh::LeanObject,
    mut v_init_4260_: *mut leanh::LeanObject,
    mut v_f_4261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4262_ = leanh::lean_ctor_get(v_inst_4258_, 0);
    v_toBind_4263_ = leanh::lean_ctor_get(v_inst_4258_, 1);
    leanh::lean_inc_n(v_toBind_4263_, 2);
    v_root_4264_ = leanh::lean_ctor_get(v_t_4259_, 0);
    v_tail_4265_ = leanh::lean_ctor_get(v_t_4259_, 1);
    v_toPure_4266_ = leanh::lean_ctor_get(v_toApplicative_4262_, 1);
    leanh::lean_inc_n(v_toPure_4266_, 2);
    leanh::lean_inc(v_f_4261_);
    leanh::lean_inc_ref(v_inst_4258_);
    v___x_4267_ = l_Lean_PersistentArray_forInAux___redArg(
        v_inst_4258_,
        v_f_4261_,
        v_root_4264_,
        v_init_4260_,
    );
    v___f_4268_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4268_, 0, v_toPure_4266_);
    leanh::lean_inc_ref(v_tail_4265_);
    v___f_4269_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_forIn___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_4269_, 0, v_toPure_4266_);
    leanh::lean_closure_set(v___f_4269_, 1, v_f_4261_);
    leanh::lean_closure_set(v___f_4269_, 2, v_toBind_4263_);
    leanh::lean_closure_set(v___f_4269_, 3, v_tail_4265_);
    leanh::lean_closure_set(v___f_4269_, 4, v_inst_4258_);
    leanh::lean_closure_set(v___f_4269_, 5, v___f_4268_);
    v___x_4270_ = leanh::lean_apply_4(
        v_toBind_4263_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4267_,
        v___f_4269_,
    );
    return v___x_4270_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___redArg___boxed(
    mut v_inst_4271_: *mut leanh::LeanObject,
    mut v_t_4272_: *mut leanh::LeanObject,
    mut v_init_4273_: *mut leanh::LeanObject,
    mut v_f_4274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4275_ =
        l_Lean_PersistentArray_forIn___redArg(v_inst_4271_, v_t_4272_, v_init_4273_, v_f_4274_);
    leanh::lean_dec_ref(v_t_4272_);
    return v_res_4275_;
}
pub unsafe fn l_Lean_PersistentArray_forIn(
    mut v_00_u03b1_4276_: *mut leanh::LeanObject,
    mut v_m_4277_: *mut leanh::LeanObject,
    mut v_inst_4278_: *mut leanh::LeanObject,
    mut v_00_u03b2_4279_: *mut leanh::LeanObject,
    mut v_t_4280_: *mut leanh::LeanObject,
    mut v_init_4281_: *mut leanh::LeanObject,
    mut v_f_4282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4283_ =
        l_Lean_PersistentArray_forIn___redArg(v_inst_4278_, v_t_4280_, v_init_4281_, v_f_4282_);
    return v___x_4283_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___boxed(
    mut v_00_u03b1_4284_: *mut leanh::LeanObject,
    mut v_m_4285_: *mut leanh::LeanObject,
    mut v_inst_4286_: *mut leanh::LeanObject,
    mut v_00_u03b2_4287_: *mut leanh::LeanObject,
    mut v_t_4288_: *mut leanh::LeanObject,
    mut v_init_4289_: *mut leanh::LeanObject,
    mut v_f_4290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4291_ = l_Lean_PersistentArray_forIn(
        v_00_u03b1_4284_,
        v_m_4285_,
        v_inst_4286_,
        v_00_u03b2_4287_,
        v_t_4288_,
        v_init_4289_,
        v_f_4290_,
    );
    leanh::lean_dec_ref(v_t_4288_);
    return v_res_4291_;
}
pub unsafe fn l_Lean_PersistentArray_instForInOfMonad___redArg(
    mut v_inst_4292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4293_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_forIn___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    leanh::lean_closure_set(v___x_4293_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4293_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4293_, 2, v_inst_4292_);
    return v___x_4293_;
}
pub unsafe fn l_Lean_PersistentArray_instForInOfMonad(
    mut v_00_u03b1_4294_: *mut leanh::LeanObject,
    mut v_m_4295_: *mut leanh::LeanObject,
    mut v_inst_4296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4297_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_forIn___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    leanh::lean_closure_set(v___x_4297_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4297_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4297_, 2, v_inst_4296_);
    return v___x_4297_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___redArg___lam__0(
    mut v_toPure_4298_: *mut leanh::LeanObject,
    mut v_____s_4299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_4300_ = leanh::lean_ctor_get(v_____s_4299_, 0);
    leanh::lean_inc(v_fst_4300_);
    leanh::lean_dec_ref(v_____s_4299_);
    if leanh::lean_obj_tag(v_fst_4300_) == 0 {
        let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4301_ = leanh::lean_box(0);
        v___x_4302_ =
            leanh::lean_apply_2(v_toPure_4298_, leanh::lean_box(0), v___x_4301_);
        return v___x_4302_;
    } else {
        let mut v_val_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4303_ = leanh::lean_ctor_get(v_fst_4300_, 0);
        leanh::lean_inc(v_val_4303_);
        leanh::lean_dec_ref_known(v_fst_4300_, 1);
        v___x_4304_ =
            leanh::lean_apply_2(v_toPure_4298_, leanh::lean_box(0), v_val_4303_);
        return v___x_4304_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___redArg___lam__1(
    mut v___x_4305_: *mut leanh::LeanObject,
    mut v_toPure_4306_: *mut leanh::LeanObject,
    mut v___x_4307_: *mut leanh::LeanObject,
    mut v_____do__lift_4308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_4308_) == 1 {
        let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_4307_);
        v___x_4309_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4309_, 0, v_____do__lift_4308_);
        v___x_4310_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4310_, 0, v___x_4309_);
        leanh::lean_ctor_set(v___x_4310_, 1, v___x_4305_);
        v___x_4311_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4311_, 0, v___x_4310_);
        v___x_4312_ =
            leanh::lean_apply_2(v_toPure_4306_, leanh::lean_box(0), v___x_4311_);
        return v___x_4312_;
    } else {
        let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_____do__lift_4308_);
        v___x_4313_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4313_, 0, v___x_4307_);
        v___x_4314_ =
            leanh::lean_apply_2(v_toPure_4306_, leanh::lean_box(0), v___x_4313_);
        return v___x_4314_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(
    mut v_f_4315_: *mut leanh::LeanObject,
    mut v_toBind_4316_: *mut leanh::LeanObject,
    mut v___f_4317_: *mut leanh::LeanObject,
    mut v_a_4318_: *mut leanh::LeanObject,
    mut v_x_4319_: *mut leanh::LeanObject,
    mut v___y_4320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4321_ = leanh::lean_apply_1(v_f_4315_, v_a_4318_);
    v___x_4322_ = leanh::lean_apply_4(
        v_toBind_4316_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4321_,
        v___f_4317_,
    );
    return v___x_4322_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed(
    mut v_f_4323_: *mut leanh::LeanObject,
    mut v_toBind_4324_: *mut leanh::LeanObject,
    mut v___f_4325_: *mut leanh::LeanObject,
    mut v_a_4326_: *mut leanh::LeanObject,
    mut v_x_4327_: *mut leanh::LeanObject,
    mut v___y_4328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4329_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(
        v_f_4323_,
        v_toBind_4324_,
        v___f_4325_,
        v_a_4326_,
        v_x_4327_,
        v___y_4328_,
    );
    leanh::lean_dec_ref(v___y_4328_);
    return v_res_4329_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed(
    mut v_inst_4333_: *mut leanh::LeanObject,
    mut v_f_4334_: *mut leanh::LeanObject,
    mut v_toBind_4335_: *mut leanh::LeanObject,
    mut v___f_4336_: *mut leanh::LeanObject,
    mut v_a_4337_: *mut leanh::LeanObject,
    mut v_x_4338_: *mut leanh::LeanObject,
    mut v___y_4339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4340_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(
        v_inst_4333_,
        v_f_4334_,
        v_toBind_4335_,
        v___f_4336_,
        v_a_4337_,
        v_x_4338_,
        v___y_4339_,
    );
    leanh::lean_dec_ref(v___y_4339_);
    return v_res_4340_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___redArg(
    mut v_inst_4341_: *mut leanh::LeanObject,
    mut v_f_4342_: *mut leanh::LeanObject,
    mut v_x_4343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4343_) == 0 {
        let mut v_toApplicative_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_cs_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4353_: usize = 0;
        let mut v___x_4354_: usize = 0;
        let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_4344_ = leanh::lean_ctor_get(v_inst_4341_, 0);
        v_cs_4345_ = leanh::lean_ctor_get(v_x_4343_, 0);
        leanh::lean_inc_ref(v_cs_4345_);
        leanh::lean_dec_ref_known(v_x_4343_, 1);
        v_toBind_4346_ = leanh::lean_ctor_get(v_inst_4341_, 1);
        leanh::lean_inc_n(v_toBind_4346_, 2);
        v_toPure_4347_ = leanh::lean_ctor_get(v_toApplicative_4344_, 1);
        v___x_4348_ = leanh::lean_box(0);
        v___x_4349_ = l_Lean_PersistentArray_findSomeMAux___redArg___closed__0;
        leanh::lean_inc_n(v_toPure_4347_, 2);
        v___f_4350_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_findSomeMAux___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_4350_, 0, v_toPure_4347_);
        v___f_4351_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_findSomeMAux___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_4351_, 0, v___x_4348_);
        leanh::lean_closure_set(v___f_4351_, 1, v_toPure_4347_);
        leanh::lean_closure_set(v___f_4351_, 2, v___x_4349_);
        leanh::lean_inc_ref(v_inst_4341_);
        v___f_4352_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed as *mut core::ffi::c_void,
            7,
            4,
        );
        leanh::lean_closure_set(v___f_4352_, 0, v_inst_4341_);
        leanh::lean_closure_set(v___f_4352_, 1, v_f_4342_);
        leanh::lean_closure_set(v___f_4352_, 2, v_toBind_4346_);
        leanh::lean_closure_set(v___f_4352_, 3, v___f_4351_);
        v_sz_4353_ = lean_array_size(v_cs_4345_);
        v___x_4354_ = 0usize;
        v___x_4355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_4341_,
            v_cs_4345_,
            v___f_4352_,
            v_sz_4353_,
            v___x_4354_,
            v___x_4349_,
        );
        v___x_4356_ = leanh::lean_apply_4(
            v_toBind_4346_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4355_,
            v___f_4350_,
        );
        return v___x_4356_;
    } else {
        let mut v_toApplicative_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4366_: usize = 0;
        let mut v___x_4367_: usize = 0;
        let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_4357_ = leanh::lean_ctor_get(v_inst_4341_, 0);
        v_vs_4358_ = leanh::lean_ctor_get(v_x_4343_, 0);
        leanh::lean_inc_ref(v_vs_4358_);
        leanh::lean_dec_ref_known(v_x_4343_, 1);
        v_toBind_4359_ = leanh::lean_ctor_get(v_inst_4341_, 1);
        leanh::lean_inc_n(v_toBind_4359_, 2);
        v_toPure_4360_ = leanh::lean_ctor_get(v_toApplicative_4357_, 1);
        v___x_4361_ = leanh::lean_box(0);
        v___x_4362_ = l_Lean_PersistentArray_findSomeMAux___redArg___closed__0;
        leanh::lean_inc_n(v_toPure_4360_, 2);
        v___f_4363_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_findSomeMAux___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_4363_, 0, v_toPure_4360_);
        v___f_4364_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_findSomeMAux___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_4364_, 0, v___x_4361_);
        leanh::lean_closure_set(v___f_4364_, 1, v_toPure_4360_);
        leanh::lean_closure_set(v___f_4364_, 2, v___x_4362_);
        v___f_4365_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed as *mut core::ffi::c_void,
            6,
            3,
        );
        leanh::lean_closure_set(v___f_4365_, 0, v_f_4342_);
        leanh::lean_closure_set(v___f_4365_, 1, v_toBind_4359_);
        leanh::lean_closure_set(v___f_4365_, 2, v___f_4364_);
        v_sz_4366_ = lean_array_size(v_vs_4358_);
        v___x_4367_ = 0usize;
        v___x_4368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_4341_,
            v_vs_4358_,
            v___f_4365_,
            v_sz_4366_,
            v___x_4367_,
            v___x_4362_,
        );
        v___x_4369_ = leanh::lean_apply_4(
            v_toBind_4359_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4368_,
            v___f_4363_,
        );
        return v___x_4369_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(
    mut v_inst_4370_: *mut leanh::LeanObject,
    mut v_f_4371_: *mut leanh::LeanObject,
    mut v_toBind_4372_: *mut leanh::LeanObject,
    mut v___f_4373_: *mut leanh::LeanObject,
    mut v_a_4374_: *mut leanh::LeanObject,
    mut v_x_4375_: *mut leanh::LeanObject,
    mut v___y_4376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4377_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_4370_, v_f_4371_, v_a_4374_);
    v___x_4378_ = leanh::lean_apply_4(
        v_toBind_4372_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4377_,
        v___f_4373_,
    );
    return v___x_4378_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux(
    mut v_00_u03b1_4379_: *mut leanh::LeanObject,
    mut v_m_4380_: *mut leanh::LeanObject,
    mut v_inst_4381_: *mut leanh::LeanObject,
    mut v_00_u03b2_4382_: *mut leanh::LeanObject,
    mut v_f_4383_: *mut leanh::LeanObject,
    mut v_x_4384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4385_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_4381_, v_f_4383_, v_x_4384_);
    return v___x_4385_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0(
    mut v_toPure_4386_: *mut leanh::LeanObject,
    mut v_____do__lift_4387_: *mut leanh::LeanObject,
    mut v_____s_4388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_4389_ = leanh::lean_ctor_get(v_____s_4388_, 0);
    leanh::lean_inc(v_fst_4389_);
    leanh::lean_dec_ref(v_____s_4388_);
    if leanh::lean_obj_tag(v_fst_4389_) == 0 {
        let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4390_ = leanh::lean_apply_2(
            v_toPure_4386_,
            leanh::lean_box(0),
            v_____do__lift_4387_,
        );
        return v___x_4390_;
    } else {
        let mut v_val_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_____do__lift_4387_);
        v_val_4391_ = leanh::lean_ctor_get(v_fst_4389_, 0);
        leanh::lean_inc(v_val_4391_);
        leanh::lean_dec_ref_known(v_fst_4389_, 1);
        v___x_4392_ =
            leanh::lean_apply_2(v_toPure_4386_, leanh::lean_box(0), v_val_4391_);
        return v___x_4392_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1(
    mut v___x_4393_: *mut leanh::LeanObject,
    mut v_toPure_4394_: *mut leanh::LeanObject,
    mut v___x_4395_: *mut leanh::LeanObject,
    mut v_____do__lift_4396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_4396_) == 1 {
        let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_4395_);
        v___x_4397_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4397_, 0, v_____do__lift_4396_);
        v___x_4398_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4398_, 0, v___x_4397_);
        leanh::lean_ctor_set(v___x_4398_, 1, v___x_4393_);
        v___x_4399_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4399_, 0, v___x_4398_);
        v___x_4400_ =
            leanh::lean_apply_2(v_toPure_4394_, leanh::lean_box(0), v___x_4399_);
        return v___x_4400_;
    } else {
        let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_____do__lift_4396_);
        v___x_4401_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4401_, 0, v___x_4395_);
        v___x_4402_ =
            leanh::lean_apply_2(v_toPure_4394_, leanh::lean_box(0), v___x_4401_);
        return v___x_4402_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(
    mut v_f_4403_: *mut leanh::LeanObject,
    mut v_toBind_4404_: *mut leanh::LeanObject,
    mut v___f_4405_: *mut leanh::LeanObject,
    mut v_a_4406_: *mut leanh::LeanObject,
    mut v_x_4407_: *mut leanh::LeanObject,
    mut v___y_4408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4409_ = leanh::lean_apply_1(v_f_4403_, v_a_4406_);
    v___x_4410_ = leanh::lean_apply_4(
        v_toBind_4404_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4409_,
        v___f_4405_,
    );
    return v___x_4410_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed(
    mut v_f_4411_: *mut leanh::LeanObject,
    mut v_toBind_4412_: *mut leanh::LeanObject,
    mut v___f_4413_: *mut leanh::LeanObject,
    mut v_a_4414_: *mut leanh::LeanObject,
    mut v_x_4415_: *mut leanh::LeanObject,
    mut v___y_4416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4417_ = l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(
        v_f_4411_,
        v_toBind_4412_,
        v___f_4413_,
        v_a_4414_,
        v_x_4415_,
        v___y_4416_,
    );
    leanh::lean_dec_ref(v___y_4416_);
    return v_res_4417_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3(
    mut v_toPure_4418_: *mut leanh::LeanObject,
    mut v_f_4419_: *mut leanh::LeanObject,
    mut v_toBind_4420_: *mut leanh::LeanObject,
    mut v_tail_4421_: *mut leanh::LeanObject,
    mut v_inst_4422_: *mut leanh::LeanObject,
    mut v_____do__lift_4423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_4423_) == 0 {
        let mut v___f_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4429_: usize = 0;
        let mut v___x_4430_: usize = 0;
        let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_toPure_4418_);
        v___f_4424_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_4424_, 0, v_toPure_4418_);
        leanh::lean_closure_set(v___f_4424_, 1, v_____do__lift_4423_);
        v___x_4425_ = leanh::lean_box(0);
        v___x_4426_ = l_Lean_PersistentArray_findSomeMAux___redArg___closed__0;
        v___f_4427_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_4427_, 0, v___x_4425_);
        leanh::lean_closure_set(v___f_4427_, 1, v_toPure_4418_);
        leanh::lean_closure_set(v___f_4427_, 2, v___x_4426_);
        leanh::lean_inc(v_toBind_4420_);
        v___f_4428_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed
                as *mut core::ffi::c_void,
            6,
            3,
        );
        leanh::lean_closure_set(v___f_4428_, 0, v_f_4419_);
        leanh::lean_closure_set(v___f_4428_, 1, v_toBind_4420_);
        leanh::lean_closure_set(v___f_4428_, 2, v___f_4427_);
        v_sz_4429_ = lean_array_size(v_tail_4421_);
        v___x_4430_ = 0usize;
        v___x_4431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_4422_,
            v_tail_4421_,
            v___f_4428_,
            v_sz_4429_,
            v___x_4430_,
            v___x_4426_,
        );
        v___x_4432_ = leanh::lean_apply_4(
            v_toBind_4420_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4431_,
            v___f_4424_,
        );
        return v___x_4432_;
    } else {
        let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_4422_);
        leanh::lean_dec_ref(v_tail_4421_);
        leanh::lean_dec(v_toBind_4420_);
        leanh::lean_dec(v_f_4419_);
        v___x_4433_ = leanh::lean_apply_2(
            v_toPure_4418_,
            leanh::lean_box(0),
            v_____do__lift_4423_,
        );
        return v___x_4433_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___redArg(
    mut v_inst_4434_: *mut leanh::LeanObject,
    mut v_t_4435_: *mut leanh::LeanObject,
    mut v_f_4436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4437_ = leanh::lean_ctor_get(v_inst_4434_, 0);
    v_toBind_4438_ = leanh::lean_ctor_get(v_inst_4434_, 1);
    leanh::lean_inc_n(v_toBind_4438_, 2);
    v_root_4439_ = leanh::lean_ctor_get(v_t_4435_, 0);
    leanh::lean_inc_ref(v_root_4439_);
    v_tail_4440_ = leanh::lean_ctor_get(v_t_4435_, 1);
    leanh::lean_inc_ref(v_tail_4440_);
    leanh::lean_dec_ref(v_t_4435_);
    v_toPure_4441_ = leanh::lean_ctor_get(v_toApplicative_4437_, 1);
    leanh::lean_inc(v_toPure_4441_);
    leanh::lean_inc(v_f_4436_);
    leanh::lean_inc_ref(v_inst_4434_);
    v___x_4442_ =
        l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_4434_, v_f_4436_, v_root_4439_);
    v___f_4443_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_4443_, 0, v_toPure_4441_);
    leanh::lean_closure_set(v___f_4443_, 1, v_f_4436_);
    leanh::lean_closure_set(v___f_4443_, 2, v_toBind_4438_);
    leanh::lean_closure_set(v___f_4443_, 3, v_tail_4440_);
    leanh::lean_closure_set(v___f_4443_, 4, v_inst_4434_);
    v___x_4444_ = leanh::lean_apply_4(
        v_toBind_4438_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4442_,
        v___f_4443_,
    );
    return v___x_4444_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f(
    mut v_00_u03b1_4445_: *mut leanh::LeanObject,
    mut v_m_4446_: *mut leanh::LeanObject,
    mut v_inst_4447_: *mut leanh::LeanObject,
    mut v_00_u03b2_4448_: *mut leanh::LeanObject,
    mut v_t_4449_: *mut leanh::LeanObject,
    mut v_f_4450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4451_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_4447_, v_t_4449_, v_f_4450_);
    return v___x_4451_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevMAux___redArg(
    mut v_inst_4452_: *mut leanh::LeanObject,
    mut v_f_4453_: *mut leanh::LeanObject,
    mut v_x_4454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4454_) == 0 {
        let mut v_cs_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_cs_4455_ = leanh::lean_ctor_get(v_x_4454_, 0);
        leanh::lean_inc_ref(v_cs_4455_);
        leanh::lean_dec_ref_known(v_x_4454_, 1);
        leanh::lean_inc_ref(v_inst_4452_);
        v___f_4456_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_4456_, 0, v_inst_4452_);
        leanh::lean_closure_set(v___f_4456_, 1, v_f_4453_);
        v___x_4457_ = lean_array_get_size(v_cs_4455_);
        v___x_4458_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_4452_,
            v___f_4456_,
            v_cs_4455_,
            v___x_4457_,
            leanh::lean_box(0),
        );
        return v___x_4458_;
    } else {
        let mut v_vs_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_vs_4459_ = leanh::lean_ctor_get(v_x_4454_, 0);
        leanh::lean_inc_ref(v_vs_4459_);
        leanh::lean_dec_ref_known(v_x_4454_, 1);
        v___x_4460_ = lean_array_get_size(v_vs_4459_);
        v___x_4461_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_4452_,
            v_f_4453_,
            v_vs_4459_,
            v___x_4460_,
            leanh::lean_box(0),
        );
        return v___x_4461_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0(
    mut v_inst_4462_: *mut leanh::LeanObject,
    mut v_f_4463_: *mut leanh::LeanObject,
    mut v_c_4464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4465_ =
        l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_4462_, v_f_4463_, v_c_4464_);
    return v___x_4465_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevMAux(
    mut v_00_u03b1_4466_: *mut leanh::LeanObject,
    mut v_m_4467_: *mut leanh::LeanObject,
    mut v_inst_4468_: *mut leanh::LeanObject,
    mut v_00_u03b2_4469_: *mut leanh::LeanObject,
    mut v_f_4470_: *mut leanh::LeanObject,
    mut v_x_4471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4472_ =
        l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_4468_, v_f_4470_, v_x_4471_);
    return v___x_4472_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0(
    mut v_inst_4473_: *mut leanh::LeanObject,
    mut v_f_4474_: *mut leanh::LeanObject,
    mut v_root_4475_: *mut leanh::LeanObject,
    mut v_toPure_4476_: *mut leanh::LeanObject,
    mut v_____do__lift_4477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_4477_) == 0 {
        let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_4476_);
        v___x_4478_ =
            l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_4473_, v_f_4474_, v_root_4475_);
        return v___x_4478_;
    } else {
        let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_root_4475_);
        leanh::lean_dec(v_f_4474_);
        leanh::lean_dec_ref(v_inst_4473_);
        v___x_4479_ = leanh::lean_apply_2(
            v_toPure_4476_,
            leanh::lean_box(0),
            v_____do__lift_4477_,
        );
        return v___x_4479_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevM_x3f___redArg(
    mut v_inst_4480_: *mut leanh::LeanObject,
    mut v_t_4481_: *mut leanh::LeanObject,
    mut v_f_4482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4483_ = leanh::lean_ctor_get(v_inst_4480_, 0);
    v_toBind_4484_ = leanh::lean_ctor_get(v_inst_4480_, 1);
    leanh::lean_inc(v_toBind_4484_);
    v_root_4485_ = leanh::lean_ctor_get(v_t_4481_, 0);
    leanh::lean_inc_ref(v_root_4485_);
    v_tail_4486_ = leanh::lean_ctor_get(v_t_4481_, 1);
    leanh::lean_inc_ref(v_tail_4486_);
    leanh::lean_dec_ref(v_t_4481_);
    v_toPure_4487_ = leanh::lean_ctor_get(v_toApplicative_4483_, 1);
    leanh::lean_inc(v_toPure_4487_);
    v___x_4488_ = lean_array_get_size(v_tail_4486_);
    leanh::lean_inc(v_f_4482_);
    leanh::lean_inc_ref(v_inst_4480_);
    v___x_4489_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_4480_,
        v_f_4482_,
        v_tail_4486_,
        v___x_4488_,
        leanh::lean_box(0),
    );
    v___f_4490_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_4490_, 0, v_inst_4480_);
    leanh::lean_closure_set(v___f_4490_, 1, v_f_4482_);
    leanh::lean_closure_set(v___f_4490_, 2, v_root_4485_);
    leanh::lean_closure_set(v___f_4490_, 3, v_toPure_4487_);
    v___x_4491_ = leanh::lean_apply_4(
        v_toBind_4484_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4489_,
        v___f_4490_,
    );
    return v___x_4491_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevM_x3f(
    mut v_00_u03b1_4492_: *mut leanh::LeanObject,
    mut v_m_4493_: *mut leanh::LeanObject,
    mut v_inst_4494_: *mut leanh::LeanObject,
    mut v_00_u03b2_4495_: *mut leanh::LeanObject,
    mut v_t_4496_: *mut leanh::LeanObject,
    mut v_f_4497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4498_ =
        l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_4494_, v_t_4496_, v_f_4497_);
    return v___x_4498_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___redArg___lam__1(
    mut v_f_4499_: *mut leanh::LeanObject,
    mut v_x_4500_: *mut leanh::LeanObject,
    mut v___y_4501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4502_ = leanh::lean_apply_1(v_f_4499_, v___y_4501_);
    return v___x_4502_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___redArg(
    mut v_inst_4503_: *mut leanh::LeanObject,
    mut v_f_4504_: *mut leanh::LeanObject,
    mut v_x_4505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4505_) == 0 {
        let mut v_cs_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4510_: u8 = 0;
        v_cs_4506_ = leanh::lean_ctor_get(v_x_4505_, 0);
        leanh::lean_inc_ref(v_cs_4506_);
        leanh::lean_dec_ref_known(v_x_4505_, 1);
        v___x_4507_ = leanh::lean_unsigned_to_nat(0);
        v___x_4508_ = lean_array_get_size(v_cs_4506_);
        v___x_4509_ = leanh::lean_box(0);
        v___x_4510_ = lean_nat_dec_lt(v___x_4507_, v___x_4508_);
        if v___x_4510_ == 0 {
            let mut v_toApplicative_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_cs_4506_);
            leanh::lean_dec(v_f_4504_);
            v_toApplicative_4511_ = leanh::lean_ctor_get(v_inst_4503_, 0);
            leanh::lean_inc_ref(v_toApplicative_4511_);
            leanh::lean_dec_ref(v_inst_4503_);
            v_toPure_4512_ = leanh::lean_ctor_get(v_toApplicative_4511_, 1);
            leanh::lean_inc(v_toPure_4512_);
            leanh::lean_dec_ref(v_toApplicative_4511_);
            v___x_4513_ =
                leanh::lean_apply_2(v_toPure_4512_, leanh::lean_box(0), v___x_4509_);
            return v___x_4513_;
        } else {
            let mut v___f_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4515_: u8 = 0;
            leanh::lean_inc_ref(v_inst_4503_);
            v___f_4514_ = leanh::lean_alloc_closure(
                l_Lean_PersistentArray_forMAux___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                2,
            );
            leanh::lean_closure_set(v___f_4514_, 0, v_inst_4503_);
            leanh::lean_closure_set(v___f_4514_, 1, v_f_4504_);
            v___x_4515_ = lean_nat_dec_le(v___x_4508_, v___x_4508_);
            if v___x_4515_ == 0 {
                if v___x_4510_ == 0 {
                    let mut v_toApplicative_4516_: *mut leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_toPure_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec_ref(v___f_4514_);
                    leanh::lean_dec_ref(v_cs_4506_);
                    v_toApplicative_4516_ = leanh::lean_ctor_get(v_inst_4503_, 0);
                    leanh::lean_inc_ref(v_toApplicative_4516_);
                    leanh::lean_dec_ref(v_inst_4503_);
                    v_toPure_4517_ = leanh::lean_ctor_get(v_toApplicative_4516_, 1);
                    leanh::lean_inc(v_toPure_4517_);
                    leanh::lean_dec_ref(v_toApplicative_4516_);
                    v___x_4518_ = leanh::lean_apply_2(
                        v_toPure_4517_,
                        leanh::lean_box(0),
                        v___x_4509_,
                    );
                    return v___x_4518_;
                } else {
                    let mut v___x_4519_: usize = 0;
                    let mut v___x_4520_: usize = 0;
                    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4519_ = 0usize;
                    v___x_4520_ = lean_usize_of_nat(v___x_4508_);
                    v___x_4521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_4503_,
                        v___f_4514_,
                        v_cs_4506_,
                        v___x_4519_,
                        v___x_4520_,
                        v___x_4509_,
                    );
                    return v___x_4521_;
                }
            } else {
                let mut v___x_4522_: usize = 0;
                let mut v___x_4523_: usize = 0;
                let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4522_ = 0usize;
                v___x_4523_ = lean_usize_of_nat(v___x_4508_);
                v___x_4524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_4503_,
                    v___f_4514_,
                    v_cs_4506_,
                    v___x_4522_,
                    v___x_4523_,
                    v___x_4509_,
                );
                return v___x_4524_;
            }
        }
    } else {
        let mut v_vs_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4529_: u8 = 0;
        v_vs_4525_ = leanh::lean_ctor_get(v_x_4505_, 0);
        leanh::lean_inc_ref(v_vs_4525_);
        leanh::lean_dec_ref_known(v_x_4505_, 1);
        v___x_4526_ = leanh::lean_unsigned_to_nat(0);
        v___x_4527_ = lean_array_get_size(v_vs_4525_);
        v___x_4528_ = leanh::lean_box(0);
        v___x_4529_ = lean_nat_dec_lt(v___x_4526_, v___x_4527_);
        if v___x_4529_ == 0 {
            let mut v_toApplicative_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_vs_4525_);
            leanh::lean_dec(v_f_4504_);
            v_toApplicative_4530_ = leanh::lean_ctor_get(v_inst_4503_, 0);
            leanh::lean_inc_ref(v_toApplicative_4530_);
            leanh::lean_dec_ref(v_inst_4503_);
            v_toPure_4531_ = leanh::lean_ctor_get(v_toApplicative_4530_, 1);
            leanh::lean_inc(v_toPure_4531_);
            leanh::lean_dec_ref(v_toApplicative_4530_);
            v___x_4532_ =
                leanh::lean_apply_2(v_toPure_4531_, leanh::lean_box(0), v___x_4528_);
            return v___x_4532_;
        } else {
            let mut v___f_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4534_: u8 = 0;
            v___f_4533_ = leanh::lean_alloc_closure(
                l_Lean_PersistentArray_forMAux___redArg___lam__1 as *mut core::ffi::c_void,
                3,
                1,
            );
            leanh::lean_closure_set(v___f_4533_, 0, v_f_4504_);
            v___x_4534_ = lean_nat_dec_le(v___x_4527_, v___x_4527_);
            if v___x_4534_ == 0 {
                if v___x_4529_ == 0 {
                    let mut v_toApplicative_4535_: *mut leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_toPure_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec_ref(v___f_4533_);
                    leanh::lean_dec_ref(v_vs_4525_);
                    v_toApplicative_4535_ = leanh::lean_ctor_get(v_inst_4503_, 0);
                    leanh::lean_inc_ref(v_toApplicative_4535_);
                    leanh::lean_dec_ref(v_inst_4503_);
                    v_toPure_4536_ = leanh::lean_ctor_get(v_toApplicative_4535_, 1);
                    leanh::lean_inc(v_toPure_4536_);
                    leanh::lean_dec_ref(v_toApplicative_4535_);
                    v___x_4537_ = leanh::lean_apply_2(
                        v_toPure_4536_,
                        leanh::lean_box(0),
                        v___x_4528_,
                    );
                    return v___x_4537_;
                } else {
                    let mut v___x_4538_: usize = 0;
                    let mut v___x_4539_: usize = 0;
                    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4538_ = 0usize;
                    v___x_4539_ = lean_usize_of_nat(v___x_4527_);
                    v___x_4540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_4503_,
                        v___f_4533_,
                        v_vs_4525_,
                        v___x_4538_,
                        v___x_4539_,
                        v___x_4528_,
                    );
                    return v___x_4540_;
                }
            } else {
                let mut v___x_4541_: usize = 0;
                let mut v___x_4542_: usize = 0;
                let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4541_ = 0usize;
                v___x_4542_ = lean_usize_of_nat(v___x_4527_);
                v___x_4543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_4503_,
                    v___f_4533_,
                    v_vs_4525_,
                    v___x_4541_,
                    v___x_4542_,
                    v___x_4528_,
                );
                return v___x_4543_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forMAux___redArg___lam__0(
    mut v_inst_4544_: *mut leanh::LeanObject,
    mut v_f_4545_: *mut leanh::LeanObject,
    mut v_x_4546_: *mut leanh::LeanObject,
    mut v___y_4547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4548_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_4544_, v_f_4545_, v___y_4547_);
    return v___x_4548_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux(
    mut v_00_u03b1_4549_: *mut leanh::LeanObject,
    mut v_m_4550_: *mut leanh::LeanObject,
    mut v_inst_4551_: *mut leanh::LeanObject,
    mut v_f_4552_: *mut leanh::LeanObject,
    mut v_x_4553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4554_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_4551_, v_f_4552_, v_x_4553_);
    return v___x_4554_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___redArg___lam__0(
    mut v_f_4555_: *mut leanh::LeanObject,
    mut v_x_4556_: *mut leanh::LeanObject,
    mut v___y_4557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4558_ = leanh::lean_apply_1(v_f_4555_, v___y_4557_);
    return v___x_4558_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___redArg___lam__1(
    mut v_tail_4559_: *mut leanh::LeanObject,
    mut v_toPure_4560_: *mut leanh::LeanObject,
    mut v_inst_4561_: *mut leanh::LeanObject,
    mut v___f_4562_: *mut leanh::LeanObject,
    mut v_x_4563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: u8 = 0;
    v___x_4564_ = leanh::lean_unsigned_to_nat(0);
    v___x_4565_ = lean_array_get_size(v_tail_4559_);
    v___x_4566_ = leanh::lean_box(0);
    v___x_4567_ = lean_nat_dec_lt(v___x_4564_, v___x_4565_);
    if v___x_4567_ == 0 {
        let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_4562_);
        leanh::lean_dec_ref(v_inst_4561_);
        leanh::lean_dec_ref(v_tail_4559_);
        v___x_4568_ =
            leanh::lean_apply_2(v_toPure_4560_, leanh::lean_box(0), v___x_4566_);
        return v___x_4568_;
    } else {
        let mut v___x_4569_: u8 = 0;
        v___x_4569_ = lean_nat_dec_le(v___x_4565_, v___x_4565_);
        if v___x_4569_ == 0 {
            if v___x_4567_ == 0 {
                let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___f_4562_);
                leanh::lean_dec_ref(v_inst_4561_);
                leanh::lean_dec_ref(v_tail_4559_);
                v___x_4570_ = leanh::lean_apply_2(
                    v_toPure_4560_,
                    leanh::lean_box(0),
                    v___x_4566_,
                );
                return v___x_4570_;
            } else {
                let mut v___x_4571_: usize = 0;
                let mut v___x_4572_: usize = 0;
                let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_toPure_4560_);
                v___x_4571_ = 0usize;
                v___x_4572_ = lean_usize_of_nat(v___x_4565_);
                v___x_4573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_4561_,
                    v___f_4562_,
                    v_tail_4559_,
                    v___x_4571_,
                    v___x_4572_,
                    v___x_4566_,
                );
                return v___x_4573_;
            }
        } else {
            let mut v___x_4574_: usize = 0;
            let mut v___x_4575_: usize = 0;
            let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toPure_4560_);
            v___x_4574_ = 0usize;
            v___x_4575_ = lean_usize_of_nat(v___x_4565_);
            v___x_4576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_4561_,
                v___f_4562_,
                v_tail_4559_,
                v___x_4574_,
                v___x_4575_,
                v___x_4566_,
            );
            return v___x_4576_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___redArg(
    mut v_inst_4577_: *mut leanh::LeanObject,
    mut v_t_4578_: *mut leanh::LeanObject,
    mut v_f_4579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4580_ = leanh::lean_ctor_get(v_inst_4577_, 0);
    v_toPure_4581_ = leanh::lean_ctor_get(v_toApplicative_4580_, 1);
    v_toSeqRight_4582_ = leanh::lean_ctor_get(v_toApplicative_4580_, 4);
    leanh::lean_inc(v_toSeqRight_4582_);
    v_root_4583_ = leanh::lean_ctor_get(v_t_4578_, 0);
    leanh::lean_inc_ref(v_root_4583_);
    v_tail_4584_ = leanh::lean_ctor_get(v_t_4578_, 1);
    leanh::lean_inc_ref(v_tail_4584_);
    leanh::lean_dec_ref(v_t_4578_);
    leanh::lean_inc(v_f_4579_);
    v___f_4585_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_forMFrom0___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4585_, 0, v_f_4579_);
    leanh::lean_inc_ref(v_inst_4577_);
    leanh::lean_inc(v_toPure_4581_);
    v___f_4586_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_forMFrom0___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_4586_, 0, v_tail_4584_);
    leanh::lean_closure_set(v___f_4586_, 1, v_toPure_4581_);
    leanh::lean_closure_set(v___f_4586_, 2, v_inst_4577_);
    leanh::lean_closure_set(v___f_4586_, 3, v___f_4585_);
    v___x_4587_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_4577_, v_f_4579_, v_root_4583_);
    v___x_4588_ = leanh::lean_apply_4(
        v_toSeqRight_4582_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4587_,
        v___f_4586_,
    );
    return v___x_4588_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0(
    mut v_00_u03b1_4589_: *mut leanh::LeanObject,
    mut v_m_4590_: *mut leanh::LeanObject,
    mut v_inst_4591_: *mut leanh::LeanObject,
    mut v_t_4592_: *mut leanh::LeanObject,
    mut v_f_4593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4594_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_4591_, v_t_4592_, v_f_4593_);
    return v___x_4594_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(
    mut v_j_4595_: *mut leanh::LeanObject,
    mut v_cs_4596_: *mut leanh::LeanObject,
    mut v_toApplicative_4597_: *mut leanh::LeanObject,
    mut v_inst_4598_: *mut leanh::LeanObject,
    mut v___f_4599_: *mut leanh::LeanObject,
    mut v_____r_4600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: u8 = 0;
    v___x_4601_ = leanh::lean_unsigned_to_nat(1);
    v___x_4602_ = lean_nat_add(v_j_4595_, v___x_4601_);
    v___x_4603_ = lean_array_get_size(v_cs_4596_);
    v___x_4604_ = leanh::lean_box(0);
    v___x_4605_ = lean_nat_dec_lt(v___x_4602_, v___x_4603_);
    if v___x_4605_ == 0 {
        let mut v_toPure_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_4602_);
        leanh::lean_dec(v___f_4599_);
        leanh::lean_dec_ref(v_inst_4598_);
        leanh::lean_dec_ref(v_cs_4596_);
        v_toPure_4606_ = leanh::lean_ctor_get(v_toApplicative_4597_, 1);
        leanh::lean_inc(v_toPure_4606_);
        leanh::lean_dec_ref(v_toApplicative_4597_);
        v___x_4607_ =
            leanh::lean_apply_2(v_toPure_4606_, leanh::lean_box(0), v___x_4604_);
        return v___x_4607_;
    } else {
        let mut v___x_4608_: u8 = 0;
        v___x_4608_ = lean_nat_dec_le(v___x_4603_, v___x_4603_);
        if v___x_4608_ == 0 {
            if v___x_4605_ == 0 {
                let mut v_toPure_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_4602_);
                leanh::lean_dec(v___f_4599_);
                leanh::lean_dec_ref(v_inst_4598_);
                leanh::lean_dec_ref(v_cs_4596_);
                v_toPure_4609_ = leanh::lean_ctor_get(v_toApplicative_4597_, 1);
                leanh::lean_inc(v_toPure_4609_);
                leanh::lean_dec_ref(v_toApplicative_4597_);
                v___x_4610_ = leanh::lean_apply_2(
                    v_toPure_4609_,
                    leanh::lean_box(0),
                    v___x_4604_,
                );
                return v___x_4610_;
            } else {
                let mut v___x_4611_: usize = 0;
                let mut v___x_4612_: usize = 0;
                let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_toApplicative_4597_);
                v___x_4611_ = lean_usize_of_nat(v___x_4602_);
                leanh::lean_dec(v___x_4602_);
                v___x_4612_ = lean_usize_of_nat(v___x_4603_);
                v___x_4613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_4598_,
                    v___f_4599_,
                    v_cs_4596_,
                    v___x_4611_,
                    v___x_4612_,
                    v___x_4604_,
                );
                return v___x_4613_;
            }
        } else {
            let mut v___x_4614_: usize = 0;
            let mut v___x_4615_: usize = 0;
            let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_toApplicative_4597_);
            v___x_4614_ = lean_usize_of_nat(v___x_4602_);
            leanh::lean_dec(v___x_4602_);
            v___x_4615_ = lean_usize_of_nat(v___x_4603_);
            v___x_4616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_4598_,
                v___f_4599_,
                v_cs_4596_,
                v___x_4614_,
                v___x_4615_,
                v___x_4604_,
            );
            return v___x_4616_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed(
    mut v_j_4617_: *mut leanh::LeanObject,
    mut v_cs_4618_: *mut leanh::LeanObject,
    mut v_toApplicative_4619_: *mut leanh::LeanObject,
    mut v_inst_4620_: *mut leanh::LeanObject,
    mut v___f_4621_: *mut leanh::LeanObject,
    mut v_____r_4622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4623_ =
        l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(
            v_j_4617_,
            v_cs_4618_,
            v_toApplicative_4619_,
            v_inst_4620_,
            v___f_4621_,
            v_____r_4622_,
        );
    leanh::lean_dec(v_j_4617_);
    return v_res_4623_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(
    mut v_inst_4624_: *mut leanh::LeanObject,
    mut v_f_4625_: *mut leanh::LeanObject,
    mut v_x_4626_: *mut leanh::LeanObject,
    mut v_x_4627_: usize,
    mut v_x_4628_: usize,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4626_) == 0 {
        let mut v_toApplicative_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_cs_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4634_: usize = 0;
        let mut v_j_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4638_: usize = 0;
        let mut v___x_4639_: usize = 0;
        let mut v___x_4640_: usize = 0;
        let mut v___x_4641_: usize = 0;
        let mut v___x_4642_: usize = 0;
        let mut v___x_4643_: usize = 0;
        let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_4629_ = leanh::lean_ctor_get(v_inst_4624_, 0);
        v_toBind_4630_ = leanh::lean_ctor_get(v_inst_4624_, 1);
        leanh::lean_inc(v_toBind_4630_);
        v_cs_4631_ = leanh::lean_ctor_get(v_x_4626_, 0);
        leanh::lean_inc_ref_n(v_cs_4631_, 2);
        leanh::lean_dec_ref_known(v_x_4626_, 1);
        leanh::lean_inc(v_f_4625_);
        leanh::lean_inc_ref_n(v_inst_4624_, 2);
        v___f_4632_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_forMAux___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_4632_, 0, v_inst_4624_);
        leanh::lean_closure_set(v___f_4632_, 1, v_f_4625_);
        v___x_4633_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0),
            core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0_once),
            _init_l_Lean_instInhabitedPersistentArrayNode___closed__0,
        );
        v___x_4634_ = lean_usize_shift_right(v_x_4627_, v_x_4628_);
        v_j_4635_ = lean_usize_to_nat(v___x_4634_);
        leanh::lean_inc_ref(v_toApplicative_4629_);
        leanh::lean_inc(v_j_4635_);
        v___f_4636_ = leanh::lean_alloc_closure(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 5);
        leanh::lean_closure_set(v___f_4636_, 0, v_j_4635_);
        leanh::lean_closure_set(v___f_4636_, 1, v_cs_4631_);
        leanh::lean_closure_set(v___f_4636_, 2, v_toApplicative_4629_);
        leanh::lean_closure_set(v___f_4636_, 3, v_inst_4624_);
        leanh::lean_closure_set(v___f_4636_, 4, v___f_4632_);
        v___x_4637_ = lean_array_get(v___x_4633_, v_cs_4631_, v_j_4635_);
        leanh::lean_dec(v_j_4635_);
        leanh::lean_dec_ref(v_cs_4631_);
        v___x_4638_ = 1usize;
        v___x_4639_ = lean_usize_shift_left(v___x_4638_, v_x_4628_);
        v___x_4640_ = lean_usize_sub(v___x_4639_, v___x_4638_);
        v___x_4641_ = lean_usize_land(v_x_4627_, v___x_4640_);
        v___x_4642_ = 5usize;
        v___x_4643_ = lean_usize_sub(v_x_4628_, v___x_4642_);
        v___x_4644_ =
            l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(
                v_inst_4624_,
                v_f_4625_,
                v___x_4637_,
                v___x_4641_,
                v___x_4643_,
            );
        v___x_4645_ = leanh::lean_apply_4(
            v_toBind_4630_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4644_,
            v___f_4636_,
        );
        return v___x_4645_;
    } else {
        let mut v_toApplicative_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4651_: u8 = 0;
        v_toApplicative_4646_ = leanh::lean_ctor_get(v_inst_4624_, 0);
        v_vs_4647_ = leanh::lean_ctor_get(v_x_4626_, 0);
        leanh::lean_inc_ref(v_vs_4647_);
        leanh::lean_dec_ref_known(v_x_4626_, 1);
        v___x_4648_ = lean_usize_to_nat(v_x_4627_);
        v___x_4649_ = lean_array_get_size(v_vs_4647_);
        v___x_4650_ = leanh::lean_box(0);
        v___x_4651_ = lean_nat_dec_lt(v___x_4648_, v___x_4649_);
        if v___x_4651_ == 0 {
            let mut v_toPure_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_toApplicative_4646_);
            leanh::lean_dec(v___x_4648_);
            leanh::lean_dec_ref(v_vs_4647_);
            leanh::lean_dec(v_f_4625_);
            leanh::lean_dec_ref(v_inst_4624_);
            v_toPure_4652_ = leanh::lean_ctor_get(v_toApplicative_4646_, 1);
            leanh::lean_inc(v_toPure_4652_);
            leanh::lean_dec_ref(v_toApplicative_4646_);
            v___x_4653_ =
                leanh::lean_apply_2(v_toPure_4652_, leanh::lean_box(0), v___x_4650_);
            return v___x_4653_;
        } else {
            let mut v___f_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4655_: u8 = 0;
            v___f_4654_ = leanh::lean_alloc_closure(
                l_Lean_PersistentArray_forMAux___redArg___lam__1 as *mut core::ffi::c_void,
                3,
                1,
            );
            leanh::lean_closure_set(v___f_4654_, 0, v_f_4625_);
            v___x_4655_ = lean_nat_dec_le(v___x_4649_, v___x_4649_);
            if v___x_4655_ == 0 {
                if v___x_4651_ == 0 {
                    let mut v_toPure_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_inc_ref(v_toApplicative_4646_);
                    leanh::lean_dec_ref(v___f_4654_);
                    leanh::lean_dec(v___x_4648_);
                    leanh::lean_dec_ref(v_vs_4647_);
                    leanh::lean_dec_ref(v_inst_4624_);
                    v_toPure_4656_ = leanh::lean_ctor_get(v_toApplicative_4646_, 1);
                    leanh::lean_inc(v_toPure_4656_);
                    leanh::lean_dec_ref(v_toApplicative_4646_);
                    v___x_4657_ = leanh::lean_apply_2(
                        v_toPure_4656_,
                        leanh::lean_box(0),
                        v___x_4650_,
                    );
                    return v___x_4657_;
                } else {
                    let mut v___x_4658_: usize = 0;
                    let mut v___x_4659_: usize = 0;
                    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4658_ = lean_usize_of_nat(v___x_4648_);
                    leanh::lean_dec(v___x_4648_);
                    v___x_4659_ = lean_usize_of_nat(v___x_4649_);
                    v___x_4660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_4624_,
                        v___f_4654_,
                        v_vs_4647_,
                        v___x_4658_,
                        v___x_4659_,
                        v___x_4650_,
                    );
                    return v___x_4660_;
                }
            } else {
                let mut v___x_4661_: usize = 0;
                let mut v___x_4662_: usize = 0;
                let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4661_ = lean_usize_of_nat(v___x_4648_);
                leanh::lean_dec(v___x_4648_);
                v___x_4662_ = lean_usize_of_nat(v___x_4649_);
                v___x_4663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_4624_,
                    v___f_4654_,
                    v_vs_4647_,
                    v___x_4661_,
                    v___x_4662_,
                    v___x_4650_,
                );
                return v___x_4663_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___boxed(
    mut v_inst_4664_: *mut leanh::LeanObject,
    mut v_f_4665_: *mut leanh::LeanObject,
    mut v_x_4666_: *mut leanh::LeanObject,
    mut v_x_4667_: *mut leanh::LeanObject,
    mut v_x_4668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_290__boxed_4669_: usize = 0;
    let mut v_x_291__boxed_4670_: usize = 0;
    let mut v_res_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_290__boxed_4669_ = leanh::lean_unbox_usize(v_x_4667_);
    leanh::lean_dec(v_x_4667_);
    v_x_291__boxed_4670_ = leanh::lean_unbox_usize(v_x_4668_);
    leanh::lean_dec(v_x_4668_);
    v_res_4671_ =
        l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(
            v_inst_4664_,
            v_f_4665_,
            v_x_4666_,
            v_x_290__boxed_4669_,
            v_x_291__boxed_4670_,
        );
    return v_res_4671_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(
    mut v_00_u03b1_4672_: *mut leanh::LeanObject,
    mut v_m_4673_: *mut leanh::LeanObject,
    mut v_inst_4674_: *mut leanh::LeanObject,
    mut v_f_4675_: *mut leanh::LeanObject,
    mut v_x_4676_: *mut leanh::LeanObject,
    mut v_x_4677_: usize,
    mut v_x_4678_: usize,
) -> *mut leanh::LeanObject {
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4679_ =
        l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(
            v_inst_4674_,
            v_f_4675_,
            v_x_4676_,
            v_x_4677_,
            v_x_4678_,
        );
    return v___x_4679_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___boxed(
    mut v_00_u03b1_4680_: *mut leanh::LeanObject,
    mut v_m_4681_: *mut leanh::LeanObject,
    mut v_inst_4682_: *mut leanh::LeanObject,
    mut v_f_4683_: *mut leanh::LeanObject,
    mut v_x_4684_: *mut leanh::LeanObject,
    mut v_x_4685_: *mut leanh::LeanObject,
    mut v_x_4686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_360__boxed_4687_: usize = 0;
    let mut v_x_361__boxed_4688_: usize = 0;
    let mut v_res_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_360__boxed_4687_ = leanh::lean_unbox_usize(v_x_4685_);
    leanh::lean_dec(v_x_4685_);
    v_x_361__boxed_4688_ = leanh::lean_unbox_usize(v_x_4686_);
    leanh::lean_dec(v_x_4686_);
    v_res_4689_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(
        v_00_u03b1_4680_,
        v_m_4681_,
        v_inst_4682_,
        v_f_4683_,
        v_x_4684_,
        v_x_360__boxed_4687_,
        v_x_361__boxed_4688_,
    );
    return v_res_4689_;
}
pub unsafe fn l_Lean_PersistentArray_forM___redArg___lam__1(
    mut v_tail_4690_: *mut leanh::LeanObject,
    mut v___x_4691_: *mut leanh::LeanObject,
    mut v_toApplicative_4692_: *mut leanh::LeanObject,
    mut v_inst_4693_: *mut leanh::LeanObject,
    mut v___f_4694_: *mut leanh::LeanObject,
    mut v_____r_4695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: u8 = 0;
    v___x_4696_ = lean_array_get_size(v_tail_4690_);
    v___x_4697_ = leanh::lean_box(0);
    v___x_4698_ = lean_nat_dec_lt(v___x_4691_, v___x_4696_);
    if v___x_4698_ == 0 {
        let mut v_toPure_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_4694_);
        leanh::lean_dec_ref(v_inst_4693_);
        leanh::lean_dec_ref(v_tail_4690_);
        v_toPure_4699_ = leanh::lean_ctor_get(v_toApplicative_4692_, 1);
        leanh::lean_inc(v_toPure_4699_);
        leanh::lean_dec_ref(v_toApplicative_4692_);
        v___x_4700_ =
            leanh::lean_apply_2(v_toPure_4699_, leanh::lean_box(0), v___x_4697_);
        return v___x_4700_;
    } else {
        let mut v___x_4701_: u8 = 0;
        v___x_4701_ = lean_nat_dec_le(v___x_4696_, v___x_4696_);
        if v___x_4701_ == 0 {
            if v___x_4698_ == 0 {
                let mut v_toPure_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___f_4694_);
                leanh::lean_dec_ref(v_inst_4693_);
                leanh::lean_dec_ref(v_tail_4690_);
                v_toPure_4702_ = leanh::lean_ctor_get(v_toApplicative_4692_, 1);
                leanh::lean_inc(v_toPure_4702_);
                leanh::lean_dec_ref(v_toApplicative_4692_);
                v___x_4703_ = leanh::lean_apply_2(
                    v_toPure_4702_,
                    leanh::lean_box(0),
                    v___x_4697_,
                );
                return v___x_4703_;
            } else {
                let mut v___x_4704_: usize = 0;
                let mut v___x_4705_: usize = 0;
                let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_toApplicative_4692_);
                v___x_4704_ = 0usize;
                v___x_4705_ = lean_usize_of_nat(v___x_4696_);
                v___x_4706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_4693_,
                    v___f_4694_,
                    v_tail_4690_,
                    v___x_4704_,
                    v___x_4705_,
                    v___x_4697_,
                );
                return v___x_4706_;
            }
        } else {
            let mut v___x_4707_: usize = 0;
            let mut v___x_4708_: usize = 0;
            let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_toApplicative_4692_);
            v___x_4707_ = 0usize;
            v___x_4708_ = lean_usize_of_nat(v___x_4696_);
            v___x_4709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_4693_,
                v___f_4694_,
                v_tail_4690_,
                v___x_4707_,
                v___x_4708_,
                v___x_4697_,
            );
            return v___x_4709_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forM___redArg___lam__1___boxed(
    mut v_tail_4710_: *mut leanh::LeanObject,
    mut v___x_4711_: *mut leanh::LeanObject,
    mut v_toApplicative_4712_: *mut leanh::LeanObject,
    mut v_inst_4713_: *mut leanh::LeanObject,
    mut v___f_4714_: *mut leanh::LeanObject,
    mut v_____r_4715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4716_ = l_Lean_PersistentArray_forM___redArg___lam__1(
        v_tail_4710_,
        v___x_4711_,
        v_toApplicative_4712_,
        v_inst_4713_,
        v___f_4714_,
        v_____r_4715_,
    );
    leanh::lean_dec(v___x_4711_);
    return v_res_4716_;
}
pub unsafe fn l_Lean_PersistentArray_forM___redArg(
    mut v_inst_4717_: *mut leanh::LeanObject,
    mut v_t_4718_: *mut leanh::LeanObject,
    mut v_f_4719_: *mut leanh::LeanObject,
    mut v_start_4720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: u8 = 0;
    v___x_4721_ = leanh::lean_unsigned_to_nat(0);
    v___x_4722_ = lean_nat_dec_eq(v_start_4720_, v___x_4721_);
    if v___x_4722_ == 0 {
        let mut v_root_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_4725_: usize = 0;
        let mut v_tailOff_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4727_: u8 = 0;
        v_root_4723_ = leanh::lean_ctor_get(v_t_4718_, 0);
        leanh::lean_inc_ref(v_root_4723_);
        v_tail_4724_ = leanh::lean_ctor_get(v_t_4718_, 1);
        leanh::lean_inc_ref(v_tail_4724_);
        v_shift_4725_ = leanh::lean_ctor_get_usize(v_t_4718_, 4);
        v_tailOff_4726_ = leanh::lean_ctor_get(v_t_4718_, 3);
        leanh::lean_inc(v_tailOff_4726_);
        leanh::lean_dec_ref(v_t_4718_);
        v___x_4727_ = lean_nat_dec_le(v_tailOff_4726_, v_start_4720_);
        if v___x_4727_ == 0 {
            let mut v_toApplicative_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4732_: usize = 0;
            let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_tailOff_4726_);
            v_toApplicative_4728_ = leanh::lean_ctor_get(v_inst_4717_, 0);
            v_toBind_4729_ = leanh::lean_ctor_get(v_inst_4717_, 1);
            leanh::lean_inc(v_toBind_4729_);
            leanh::lean_inc(v_f_4719_);
            v___f_4730_ = leanh::lean_alloc_closure(
                l_Lean_PersistentArray_forMFrom0___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                1,
            );
            leanh::lean_closure_set(v___f_4730_, 0, v_f_4719_);
            leanh::lean_inc_ref(v_inst_4717_);
            leanh::lean_inc_ref(v_toApplicative_4728_);
            v___f_4731_ = leanh::lean_alloc_closure(
                l_Lean_PersistentArray_forM___redArg___lam__1___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            leanh::lean_closure_set(v___f_4731_, 0, v_tail_4724_);
            leanh::lean_closure_set(v___f_4731_, 1, v___x_4721_);
            leanh::lean_closure_set(v___f_4731_, 2, v_toApplicative_4728_);
            leanh::lean_closure_set(v___f_4731_, 3, v_inst_4717_);
            leanh::lean_closure_set(v___f_4731_, 4, v___f_4730_);
            v___x_4732_ = lean_usize_of_nat(v_start_4720_);
            v___x_4733_ =
                l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(
                    v_inst_4717_,
                    v_f_4719_,
                    v_root_4723_,
                    v___x_4732_,
                    v_shift_4725_,
                );
            v___x_4734_ = leanh::lean_apply_4(
                v_toBind_4729_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4733_,
                v___f_4731_,
            );
            return v___x_4734_;
        } else {
            let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4738_: u8 = 0;
            leanh::lean_dec_ref(v_root_4723_);
            v___x_4735_ = lean_nat_sub(v_start_4720_, v_tailOff_4726_);
            leanh::lean_dec(v_tailOff_4726_);
            v___x_4736_ = lean_array_get_size(v_tail_4724_);
            v___x_4737_ = leanh::lean_box(0);
            v___x_4738_ = lean_nat_dec_lt(v___x_4735_, v___x_4736_);
            if v___x_4738_ == 0 {
                let mut v_toApplicative_4739_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_4735_);
                leanh::lean_dec_ref(v_tail_4724_);
                leanh::lean_dec(v_f_4719_);
                v_toApplicative_4739_ = leanh::lean_ctor_get(v_inst_4717_, 0);
                leanh::lean_inc_ref(v_toApplicative_4739_);
                leanh::lean_dec_ref(v_inst_4717_);
                v_toPure_4740_ = leanh::lean_ctor_get(v_toApplicative_4739_, 1);
                leanh::lean_inc(v_toPure_4740_);
                leanh::lean_dec_ref(v_toApplicative_4739_);
                v___x_4741_ = leanh::lean_apply_2(
                    v_toPure_4740_,
                    leanh::lean_box(0),
                    v___x_4737_,
                );
                return v___x_4741_;
            } else {
                let mut v___f_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4743_: u8 = 0;
                v___f_4742_ = leanh::lean_alloc_closure(
                    l_Lean_PersistentArray_forMFrom0___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___f_4742_, 0, v_f_4719_);
                v___x_4743_ = lean_nat_dec_le(v___x_4736_, v___x_4736_);
                if v___x_4743_ == 0 {
                    if v___x_4738_ == 0 {
                        let mut v_toApplicative_4744_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toPure_4745_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec_ref(v___f_4742_);
                        leanh::lean_dec(v___x_4735_);
                        leanh::lean_dec_ref(v_tail_4724_);
                        v_toApplicative_4744_ = leanh::lean_ctor_get(v_inst_4717_, 0);
                        leanh::lean_inc_ref(v_toApplicative_4744_);
                        leanh::lean_dec_ref(v_inst_4717_);
                        v_toPure_4745_ = leanh::lean_ctor_get(v_toApplicative_4744_, 1);
                        leanh::lean_inc(v_toPure_4745_);
                        leanh::lean_dec_ref(v_toApplicative_4744_);
                        v___x_4746_ = leanh::lean_apply_2(
                            v_toPure_4745_,
                            leanh::lean_box(0),
                            v___x_4737_,
                        );
                        return v___x_4746_;
                    } else {
                        let mut v___x_4747_: usize = 0;
                        let mut v___x_4748_: usize = 0;
                        let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_4747_ = lean_usize_of_nat(v___x_4735_);
                        leanh::lean_dec(v___x_4735_);
                        v___x_4748_ = lean_usize_of_nat(v___x_4736_);
                        v___x_4749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v_inst_4717_,
                            v___f_4742_,
                            v_tail_4724_,
                            v___x_4747_,
                            v___x_4748_,
                            v___x_4737_,
                        );
                        return v___x_4749_;
                    }
                } else {
                    let mut v___x_4750_: usize = 0;
                    let mut v___x_4751_: usize = 0;
                    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4750_ = lean_usize_of_nat(v___x_4735_);
                    leanh::lean_dec(v___x_4735_);
                    v___x_4751_ = lean_usize_of_nat(v___x_4736_);
                    v___x_4752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_4717_,
                        v___f_4742_,
                        v_tail_4724_,
                        v___x_4750_,
                        v___x_4751_,
                        v___x_4737_,
                    );
                    return v___x_4752_;
                }
            }
        }
    } else {
        let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4753_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_4717_, v_t_4718_, v_f_4719_);
        return v___x_4753_;
    }
}
pub unsafe fn l_Lean_PersistentArray_forM___redArg___boxed(
    mut v_inst_4754_: *mut leanh::LeanObject,
    mut v_t_4755_: *mut leanh::LeanObject,
    mut v_f_4756_: *mut leanh::LeanObject,
    mut v_start_4757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4758_ =
        l_Lean_PersistentArray_forM___redArg(v_inst_4754_, v_t_4755_, v_f_4756_, v_start_4757_);
    leanh::lean_dec(v_start_4757_);
    return v_res_4758_;
}
pub unsafe fn l_Lean_PersistentArray_forM(
    mut v_00_u03b1_4759_: *mut leanh::LeanObject,
    mut v_m_4760_: *mut leanh::LeanObject,
    mut v_inst_4761_: *mut leanh::LeanObject,
    mut v_t_4762_: *mut leanh::LeanObject,
    mut v_f_4763_: *mut leanh::LeanObject,
    mut v_start_4764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4765_ =
        l_Lean_PersistentArray_forM___redArg(v_inst_4761_, v_t_4762_, v_f_4763_, v_start_4764_);
    return v___x_4765_;
}
pub unsafe fn l_Lean_PersistentArray_forM___boxed(
    mut v_00_u03b1_4766_: *mut leanh::LeanObject,
    mut v_m_4767_: *mut leanh::LeanObject,
    mut v_inst_4768_: *mut leanh::LeanObject,
    mut v_t_4769_: *mut leanh::LeanObject,
    mut v_f_4770_: *mut leanh::LeanObject,
    mut v_start_4771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4772_ = l_Lean_PersistentArray_forM(
        v_00_u03b1_4766_,
        v_m_4767_,
        v_inst_4768_,
        v_t_4769_,
        v_f_4770_,
        v_start_4771_,
    );
    leanh::lean_dec(v_start_4771_);
    return v_res_4772_;
}
pub unsafe fn l_Lean_PersistentArray_foldl___redArg___lam__0(
    mut v_f_4773_: *mut leanh::LeanObject,
    mut v_x1_4774_: *mut leanh::LeanObject,
    mut v_x2_4775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4776_ = leanh::lean_apply_2(v_f_4773_, v_x1_4774_, v_x2_4775_);
    return v___x_4776_;
}
pub unsafe fn l_Lean_PersistentArray_foldl___redArg(
    mut v_t_4796_: *mut leanh::LeanObject,
    mut v_f_4797_: *mut leanh::LeanObject,
    mut v_init_4798_: *mut leanh::LeanObject,
    mut v_start_4799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4800_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4800_, 0, v_f_4797_);
    v___x_4801_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_4802_ = l_Lean_PersistentArray_foldlM___redArg(
        v___x_4801_,
        v_t_4796_,
        v___f_4800_,
        v_init_4798_,
        v_start_4799_,
    );
    return v___x_4802_;
}
pub unsafe fn l_Lean_PersistentArray_foldl___redArg___boxed(
    mut v_t_4803_: *mut leanh::LeanObject,
    mut v_f_4804_: *mut leanh::LeanObject,
    mut v_init_4805_: *mut leanh::LeanObject,
    mut v_start_4806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4807_ =
        l_Lean_PersistentArray_foldl___redArg(v_t_4803_, v_f_4804_, v_init_4805_, v_start_4806_);
    leanh::lean_dec(v_start_4806_);
    return v_res_4807_;
}
pub unsafe fn l_Lean_PersistentArray_foldl(
    mut v_00_u03b1_4808_: *mut leanh::LeanObject,
    mut v_00_u03b2_4809_: *mut leanh::LeanObject,
    mut v_t_4810_: *mut leanh::LeanObject,
    mut v_f_4811_: *mut leanh::LeanObject,
    mut v_init_4812_: *mut leanh::LeanObject,
    mut v_start_4813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4814_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4814_, 0, v_f_4811_);
    v___x_4815_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_4816_ = l_Lean_PersistentArray_foldlM___redArg(
        v___x_4815_,
        v_t_4810_,
        v___f_4814_,
        v_init_4812_,
        v_start_4813_,
    );
    return v___x_4816_;
}
pub unsafe fn l_Lean_PersistentArray_foldl___boxed(
    mut v_00_u03b1_4817_: *mut leanh::LeanObject,
    mut v_00_u03b2_4818_: *mut leanh::LeanObject,
    mut v_t_4819_: *mut leanh::LeanObject,
    mut v_f_4820_: *mut leanh::LeanObject,
    mut v_init_4821_: *mut leanh::LeanObject,
    mut v_start_4822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4823_ = l_Lean_PersistentArray_foldl(
        v_00_u03b1_4817_,
        v_00_u03b2_4818_,
        v_t_4819_,
        v_f_4820_,
        v_init_4821_,
        v_start_4822_,
    );
    leanh::lean_dec(v_start_4822_);
    return v_res_4823_;
}
pub unsafe fn l_Lean_PersistentArray_foldr___redArg(
    mut v_t_4824_: *mut leanh::LeanObject,
    mut v_f_4825_: *mut leanh::LeanObject,
    mut v_init_4826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4827_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4827_, 0, v_f_4825_);
    v___x_4828_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_4829_ =
        l_Lean_PersistentArray_foldrM___redArg(v___x_4828_, v_t_4824_, v___f_4827_, v_init_4826_);
    return v___x_4829_;
}
pub unsafe fn l_Lean_PersistentArray_foldr(
    mut v_00_u03b1_4830_: *mut leanh::LeanObject,
    mut v_00_u03b2_4831_: *mut leanh::LeanObject,
    mut v_t_4832_: *mut leanh::LeanObject,
    mut v_f_4833_: *mut leanh::LeanObject,
    mut v_init_4834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4835_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4835_, 0, v_f_4833_);
    v___x_4836_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_4837_ =
        l_Lean_PersistentArray_foldrM___redArg(v___x_4836_, v_t_4832_, v___f_4835_, v_init_4834_);
    return v___x_4837_;
}
pub unsafe fn l_Lean_PersistentArray_filter___redArg___lam__0(
    mut v_p_4838_: *mut leanh::LeanObject,
    mut v_x1_4839_: *mut leanh::LeanObject,
    mut v_x2_4840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: u8 = 0;
    leanh::lean_inc(v_x2_4840_);
    v___x_4841_ = leanh::lean_apply_1(v_p_4838_, v_x2_4840_);
    v___x_4842_ = (leanh::lean_unbox(v___x_4841_) as u8);
    if v___x_4842_ == 0 {
        leanh::lean_dec(v_x2_4840_);
        return v_x1_4839_;
    } else {
        let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4843_ = l_Lean_PersistentArray_push___redArg(v_x1_4839_, v_x2_4840_);
        return v___x_4843_;
    }
}
pub unsafe fn l_Lean_PersistentArray_filter___redArg(
    mut v_as_4844_: *mut leanh::LeanObject,
    mut v_p_4845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4846_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_filter___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4846_, 0, v_p_4845_);
    v___x_4847_ = leanh::lean_unsigned_to_nat(32);
    v___x_4848_ = lean_mk_empty_array_with_capacity(v___x_4847_);
    leanh::lean_dec_ref(v___x_4848_);
    v___x_4849_ = leanh::lean_unsigned_to_nat(0);
    v___x_4850_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__1_once),
        _init_l_Lean_instInhabitedPersistentArray_default___closed__1,
    );
    v___x_4851_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_4852_ = l_Lean_PersistentArray_foldlM___redArg(
        v___x_4851_,
        v_as_4844_,
        v___f_4846_,
        v___x_4850_,
        v___x_4849_,
    );
    return v___x_4852_;
}
pub unsafe fn l_Lean_PersistentArray_filter(
    mut v_00_u03b1_4853_: *mut leanh::LeanObject,
    mut v_as_4854_: *mut leanh::LeanObject,
    mut v_p_4855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4856_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_filter___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4856_, 0, v_p_4855_);
    v___x_4857_ = leanh::lean_unsigned_to_nat(32);
    v___x_4858_ = lean_mk_empty_array_with_capacity(v___x_4857_);
    leanh::lean_dec_ref(v___x_4858_);
    v___x_4859_ = leanh::lean_unsigned_to_nat(0);
    v___x_4860_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__1_once),
        _init_l_Lean_instInhabitedPersistentArray_default___closed__1,
    );
    v___x_4861_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_4862_ = l_Lean_PersistentArray_foldlM___redArg(
        v___x_4861_,
        v_as_4854_,
        v___f_4856_,
        v___x_4860_,
        v___x_4859_,
    );
    return v___x_4862_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(
    mut v_as_4863_: *mut leanh::LeanObject,
    mut v_i_4864_: usize,
    mut v_stop_4865_: usize,
    mut v_b_4866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4867_: u8 = 0;
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: usize = 0;
    let mut v___x_4871_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4867_ = lean_usize_dec_eq(v_i_4864_, v_stop_4865_);
                if v___x_4867_ == 0 {
                    v___x_4868_ = lean_array_uget_borrowed(v_as_4863_, v_i_4864_);
                    leanh::lean_inc(v___x_4868_);
                    v___x_4869_ = lean_array_push(v_b_4866_, v___x_4868_);
                    v___x_4870_ = 1usize;
                    v___x_4871_ = lean_usize_add(v_i_4864_, v___x_4870_);
                    v_i_4864_ = v___x_4871_;
                    v_b_4866_ = v___x_4869_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4866_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg___boxed(
    mut v_as_4873_: *mut leanh::LeanObject,
    mut v_i_4874_: *mut leanh::LeanObject,
    mut v_stop_4875_: *mut leanh::LeanObject,
    mut v_b_4876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4877_: usize = 0;
    let mut v_stop_boxed_4878_: usize = 0;
    let mut v_res_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4877_ = leanh::lean_unbox_usize(v_i_4874_);
    leanh::lean_dec(v_i_4874_);
    v_stop_boxed_4878_ = leanh::lean_unbox_usize(v_stop_4875_);
    leanh::lean_dec(v_stop_4875_);
    v_res_4879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_4873_, v_i_boxed_4877_, v_stop_boxed_4878_, v_b_4876_);
    leanh::lean_dec_ref(v_as_4873_);
    return v_res_4879_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(
    mut v_x_4880_: *mut leanh::LeanObject,
    mut v_x_4881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4880_) == 0 {
        let mut v_cs_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4885_: u8 = 0;
        v_cs_4882_ = leanh::lean_ctor_get(v_x_4880_, 0);
        v___x_4883_ = leanh::lean_unsigned_to_nat(0);
        v___x_4884_ = lean_array_get_size(v_cs_4882_);
        v___x_4885_ = lean_nat_dec_lt(v___x_4883_, v___x_4884_);
        if v___x_4885_ == 0 {
            return v_x_4881_;
        } else {
            let mut v___x_4886_: u8 = 0;
            v___x_4886_ = lean_nat_dec_le(v___x_4884_, v___x_4884_);
            if v___x_4886_ == 0 {
                if v___x_4885_ == 0 {
                    return v_x_4881_;
                } else {
                    let mut v___x_4887_: usize = 0;
                    let mut v___x_4888_: usize = 0;
                    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4887_ = 0usize;
                    v___x_4888_ = lean_usize_of_nat(v___x_4884_);
                    v___x_4889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_4882_, v___x_4887_, v___x_4888_, v_x_4881_);
                    return v___x_4889_;
                }
            } else {
                let mut v___x_4890_: usize = 0;
                let mut v___x_4891_: usize = 0;
                let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4890_ = 0usize;
                v___x_4891_ = lean_usize_of_nat(v___x_4884_);
                v___x_4892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_4882_, v___x_4890_, v___x_4891_, v_x_4881_);
                return v___x_4892_;
            }
        }
    } else {
        let mut v_vs_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4896_: u8 = 0;
        v_vs_4893_ = leanh::lean_ctor_get(v_x_4880_, 0);
        v___x_4894_ = leanh::lean_unsigned_to_nat(0);
        v___x_4895_ = lean_array_get_size(v_vs_4893_);
        v___x_4896_ = lean_nat_dec_lt(v___x_4894_, v___x_4895_);
        if v___x_4896_ == 0 {
            return v_x_4881_;
        } else {
            let mut v___x_4897_: u8 = 0;
            v___x_4897_ = lean_nat_dec_le(v___x_4895_, v___x_4895_);
            if v___x_4897_ == 0 {
                if v___x_4896_ == 0 {
                    return v_x_4881_;
                } else {
                    let mut v___x_4898_: usize = 0;
                    let mut v___x_4899_: usize = 0;
                    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4898_ = 0usize;
                    v___x_4899_ = lean_usize_of_nat(v___x_4895_);
                    v___x_4900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_4893_, v___x_4898_, v___x_4899_, v_x_4881_);
                    return v___x_4900_;
                }
            } else {
                let mut v___x_4901_: usize = 0;
                let mut v___x_4902_: usize = 0;
                let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4901_ = 0usize;
                v___x_4902_ = lean_usize_of_nat(v___x_4895_);
                v___x_4903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_4893_, v___x_4901_, v___x_4902_, v_x_4881_);
                return v___x_4903_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(
    mut v_as_4904_: *mut leanh::LeanObject,
    mut v_i_4905_: usize,
    mut v_stop_4906_: usize,
    mut v_b_4907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4908_: u8 = 0;
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: usize = 0;
    let mut v___x_4912_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4908_ = lean_usize_dec_eq(v_i_4905_, v_stop_4906_);
                if v___x_4908_ == 0 {
                    v___x_4909_ = lean_array_uget_borrowed(v_as_4904_, v_i_4905_);
                    v___x_4910_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v___x_4909_, v_b_4907_);
                    v___x_4911_ = 1usize;
                    v___x_4912_ = lean_usize_add(v_i_4905_, v___x_4911_);
                    v_i_4905_ = v___x_4912_;
                    v_b_4907_ = v___x_4910_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4907_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_as_4914_: *mut leanh::LeanObject,
    mut v_i_4915_: *mut leanh::LeanObject,
    mut v_stop_4916_: *mut leanh::LeanObject,
    mut v_b_4917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4918_: usize = 0;
    let mut v_stop_boxed_4919_: usize = 0;
    let mut v_res_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4918_ = leanh::lean_unbox_usize(v_i_4915_);
    leanh::lean_dec(v_i_4915_);
    v_stop_boxed_4919_ = leanh::lean_unbox_usize(v_stop_4916_);
    leanh::lean_dec(v_stop_4916_);
    v_res_4920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_4914_, v_i_boxed_4918_, v_stop_boxed_4919_, v_b_4917_);
    leanh::lean_dec_ref(v_as_4914_);
    return v_res_4920_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg___boxed(
    mut v_x_4921_: *mut leanh::LeanObject,
    mut v_x_4922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4923_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_4921_, v_x_4922_);
    leanh::lean_dec_ref(v_x_4921_);
    return v_res_4923_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(
    mut v_x_4924_: *mut leanh::LeanObject,
    mut v_x_4925_: usize,
    mut v_x_4926_: usize,
    mut v_x_4927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4924_) == 0 {
        let mut v_cs_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4930_: usize = 0;
        let mut v_j_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4933_: usize = 0;
        let mut v___x_4934_: usize = 0;
        let mut v___x_4935_: usize = 0;
        let mut v___x_4936_: usize = 0;
        let mut v___x_4937_: usize = 0;
        let mut v___x_4938_: usize = 0;
        let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4943_: u8 = 0;
        v_cs_4928_ = leanh::lean_ctor_get(v_x_4924_, 0);
        v___x_4929_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0),
            core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0_once),
            _init_l_Lean_instInhabitedPersistentArrayNode___closed__0,
        );
        v___x_4930_ = lean_usize_shift_right(v_x_4925_, v_x_4926_);
        v_j_4931_ = lean_usize_to_nat(v___x_4930_);
        v___x_4932_ = lean_array_get_borrowed(v___x_4929_, v_cs_4928_, v_j_4931_);
        v___x_4933_ = 1usize;
        v___x_4934_ = lean_usize_shift_left(v___x_4933_, v_x_4926_);
        v___x_4935_ = lean_usize_sub(v___x_4934_, v___x_4933_);
        v___x_4936_ = lean_usize_land(v_x_4925_, v___x_4935_);
        v___x_4937_ = 5usize;
        v___x_4938_ = lean_usize_sub(v_x_4926_, v___x_4937_);
        v___x_4939_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v___x_4932_, v___x_4936_, v___x_4938_, v_x_4927_);
        v___x_4940_ = leanh::lean_unsigned_to_nat(1);
        v___x_4941_ = lean_nat_add(v_j_4931_, v___x_4940_);
        leanh::lean_dec(v_j_4931_);
        v___x_4942_ = lean_array_get_size(v_cs_4928_);
        v___x_4943_ = lean_nat_dec_lt(v___x_4941_, v___x_4942_);
        if v___x_4943_ == 0 {
            leanh::lean_dec(v___x_4941_);
            return v___x_4939_;
        } else {
            let mut v___x_4944_: u8 = 0;
            v___x_4944_ = lean_nat_dec_le(v___x_4942_, v___x_4942_);
            if v___x_4944_ == 0 {
                if v___x_4943_ == 0 {
                    leanh::lean_dec(v___x_4941_);
                    return v___x_4939_;
                } else {
                    let mut v___x_4945_: usize = 0;
                    let mut v___x_4946_: usize = 0;
                    let mut v___x_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4945_ = lean_usize_of_nat(v___x_4941_);
                    leanh::lean_dec(v___x_4941_);
                    v___x_4946_ = lean_usize_of_nat(v___x_4942_);
                    v___x_4947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_4928_, v___x_4945_, v___x_4946_, v___x_4939_);
                    return v___x_4947_;
                }
            } else {
                let mut v___x_4948_: usize = 0;
                let mut v___x_4949_: usize = 0;
                let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4948_ = lean_usize_of_nat(v___x_4941_);
                leanh::lean_dec(v___x_4941_);
                v___x_4949_ = lean_usize_of_nat(v___x_4942_);
                v___x_4950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_4928_, v___x_4948_, v___x_4949_, v___x_4939_);
                return v___x_4950_;
            }
        }
    } else {
        let mut v_vs_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4954_: u8 = 0;
        v_vs_4951_ = leanh::lean_ctor_get(v_x_4924_, 0);
        v___x_4952_ = lean_usize_to_nat(v_x_4925_);
        v___x_4953_ = lean_array_get_size(v_vs_4951_);
        v___x_4954_ = lean_nat_dec_lt(v___x_4952_, v___x_4953_);
        if v___x_4954_ == 0 {
            leanh::lean_dec(v___x_4952_);
            return v_x_4927_;
        } else {
            let mut v___x_4955_: u8 = 0;
            v___x_4955_ = lean_nat_dec_le(v___x_4953_, v___x_4953_);
            if v___x_4955_ == 0 {
                if v___x_4954_ == 0 {
                    leanh::lean_dec(v___x_4952_);
                    return v_x_4927_;
                } else {
                    let mut v___x_4956_: usize = 0;
                    let mut v___x_4957_: usize = 0;
                    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4956_ = lean_usize_of_nat(v___x_4952_);
                    leanh::lean_dec(v___x_4952_);
                    v___x_4957_ = lean_usize_of_nat(v___x_4953_);
                    v___x_4958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_4951_, v___x_4956_, v___x_4957_, v_x_4927_);
                    return v___x_4958_;
                }
            } else {
                let mut v___x_4959_: usize = 0;
                let mut v___x_4960_: usize = 0;
                let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4959_ = lean_usize_of_nat(v___x_4952_);
                leanh::lean_dec(v___x_4952_);
                v___x_4960_ = lean_usize_of_nat(v___x_4953_);
                v___x_4961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_4951_, v___x_4959_, v___x_4960_, v_x_4927_);
                return v___x_4961_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg___boxed(
    mut v_x_4962_: *mut leanh::LeanObject,
    mut v_x_4963_: *mut leanh::LeanObject,
    mut v_x_4964_: *mut leanh::LeanObject,
    mut v_x_4965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1497__boxed_4966_: usize = 0;
    let mut v_x_1498__boxed_4967_: usize = 0;
    let mut v_res_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1497__boxed_4966_ = leanh::lean_unbox_usize(v_x_4963_);
    leanh::lean_dec(v_x_4963_);
    v_x_1498__boxed_4967_ = leanh::lean_unbox_usize(v_x_4964_);
    leanh::lean_dec(v_x_4964_);
    v_res_4968_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_4962_, v_x_1497__boxed_4966_, v_x_1498__boxed_4967_, v_x_4965_);
    leanh::lean_dec_ref(v_x_4962_);
    return v_res_4968_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(
    mut v_t_4969_: *mut leanh::LeanObject,
    mut v_init_4970_: *mut leanh::LeanObject,
    mut v_start_4971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: u8 = 0;
    v___x_4972_ = leanh::lean_unsigned_to_nat(0);
    v___x_4973_ = lean_nat_dec_eq(v_start_4971_, v___x_4972_);
    if v___x_4973_ == 0 {
        let mut v_root_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_4976_: usize = 0;
        let mut v_tailOff_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4978_: u8 = 0;
        v_root_4974_ = leanh::lean_ctor_get(v_t_4969_, 0);
        v_tail_4975_ = leanh::lean_ctor_get(v_t_4969_, 1);
        v_shift_4976_ = leanh::lean_ctor_get_usize(v_t_4969_, 4);
        v_tailOff_4977_ = leanh::lean_ctor_get(v_t_4969_, 3);
        v___x_4978_ = lean_nat_dec_le(v_tailOff_4977_, v_start_4971_);
        if v___x_4978_ == 0 {
            let mut v___x_4979_: usize = 0;
            let mut v___x_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4982_: u8 = 0;
            v___x_4979_ = lean_usize_of_nat(v_start_4971_);
            v___x_4980_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_root_4974_, v___x_4979_, v_shift_4976_, v_init_4970_);
            v___x_4981_ = lean_array_get_size(v_tail_4975_);
            v___x_4982_ = lean_nat_dec_lt(v___x_4972_, v___x_4981_);
            if v___x_4982_ == 0 {
                return v___x_4980_;
            } else {
                let mut v___x_4983_: u8 = 0;
                v___x_4983_ = lean_nat_dec_le(v___x_4981_, v___x_4981_);
                if v___x_4983_ == 0 {
                    if v___x_4982_ == 0 {
                        return v___x_4980_;
                    } else {
                        let mut v___x_4984_: usize = 0;
                        let mut v___x_4985_: usize = 0;
                        let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_4984_ = 0usize;
                        v___x_4985_ = lean_usize_of_nat(v___x_4981_);
                        v___x_4986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_4975_, v___x_4984_, v___x_4985_, v___x_4980_);
                        return v___x_4986_;
                    }
                } else {
                    let mut v___x_4987_: usize = 0;
                    let mut v___x_4988_: usize = 0;
                    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4987_ = 0usize;
                    v___x_4988_ = lean_usize_of_nat(v___x_4981_);
                    v___x_4989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_4975_, v___x_4987_, v___x_4988_, v___x_4980_);
                    return v___x_4989_;
                }
            }
        } else {
            let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4992_: u8 = 0;
            v___x_4990_ = lean_nat_sub(v_start_4971_, v_tailOff_4977_);
            v___x_4991_ = lean_array_get_size(v_tail_4975_);
            v___x_4992_ = lean_nat_dec_lt(v___x_4990_, v___x_4991_);
            if v___x_4992_ == 0 {
                leanh::lean_dec(v___x_4990_);
                return v_init_4970_;
            } else {
                let mut v___x_4993_: u8 = 0;
                v___x_4993_ = lean_nat_dec_le(v___x_4991_, v___x_4991_);
                if v___x_4993_ == 0 {
                    if v___x_4992_ == 0 {
                        leanh::lean_dec(v___x_4990_);
                        return v_init_4970_;
                    } else {
                        let mut v___x_4994_: usize = 0;
                        let mut v___x_4995_: usize = 0;
                        let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_4994_ = lean_usize_of_nat(v___x_4990_);
                        leanh::lean_dec(v___x_4990_);
                        v___x_4995_ = lean_usize_of_nat(v___x_4991_);
                        v___x_4996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_4975_, v___x_4994_, v___x_4995_, v_init_4970_);
                        return v___x_4996_;
                    }
                } else {
                    let mut v___x_4997_: usize = 0;
                    let mut v___x_4998_: usize = 0;
                    let mut v___x_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4997_ = lean_usize_of_nat(v___x_4990_);
                    leanh::lean_dec(v___x_4990_);
                    v___x_4998_ = lean_usize_of_nat(v___x_4991_);
                    v___x_4999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_4975_, v___x_4997_, v___x_4998_, v_init_4970_);
                    return v___x_4999_;
                }
            }
        }
    } else {
        let mut v_root_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5004_: u8 = 0;
        v_root_5000_ = leanh::lean_ctor_get(v_t_4969_, 0);
        v_tail_5001_ = leanh::lean_ctor_get(v_t_4969_, 1);
        v___x_5002_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_root_5000_, v_init_4970_);
        v___x_5003_ = lean_array_get_size(v_tail_5001_);
        v___x_5004_ = lean_nat_dec_lt(v___x_4972_, v___x_5003_);
        if v___x_5004_ == 0 {
            return v___x_5002_;
        } else {
            let mut v___x_5005_: u8 = 0;
            v___x_5005_ = lean_nat_dec_le(v___x_5003_, v___x_5003_);
            if v___x_5005_ == 0 {
                if v___x_5004_ == 0 {
                    return v___x_5002_;
                } else {
                    let mut v___x_5006_: usize = 0;
                    let mut v___x_5007_: usize = 0;
                    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5006_ = 0usize;
                    v___x_5007_ = lean_usize_of_nat(v___x_5003_);
                    v___x_5008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_5001_, v___x_5006_, v___x_5007_, v___x_5002_);
                    return v___x_5008_;
                }
            } else {
                let mut v___x_5009_: usize = 0;
                let mut v___x_5010_: usize = 0;
                let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5009_ = 0usize;
                v___x_5010_ = lean_usize_of_nat(v___x_5003_);
                v___x_5011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_5001_, v___x_5009_, v___x_5010_, v___x_5002_);
                return v___x_5011_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg___boxed(
    mut v_t_5012_: *mut leanh::LeanObject,
    mut v_init_5013_: *mut leanh::LeanObject,
    mut v_start_5014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5015_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(
            v_t_5012_,
            v_init_5013_,
            v_start_5014_,
        );
    leanh::lean_dec(v_start_5014_);
    leanh::lean_dec_ref(v_t_5012_);
    return v_res_5015_;
}
pub unsafe fn l_Lean_PersistentArray_toArray___redArg(
    mut v_t_5016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5017_ = leanh::lean_unsigned_to_nat(0);
    v___x_5018_ = l_Lean_PersistentArray_mkNewTail___redArg___closed__0;
    v___x_5019_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(
            v_t_5016_,
            v___x_5018_,
            v___x_5017_,
        );
    return v___x_5019_;
}
pub unsafe fn l_Lean_PersistentArray_toArray___redArg___boxed(
    mut v_t_5020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5021_ = l_Lean_PersistentArray_toArray___redArg(v_t_5020_);
    leanh::lean_dec_ref(v_t_5020_);
    return v_res_5021_;
}
pub unsafe fn l_Lean_PersistentArray_toArray(
    mut v_00_u03b1_5022_: *mut leanh::LeanObject,
    mut v_t_5023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5024_ = l_Lean_PersistentArray_toArray___redArg(v_t_5023_);
    return v___x_5024_;
}
pub unsafe fn l_Lean_PersistentArray_toArray___boxed(
    mut v_00_u03b1_5025_: *mut leanh::LeanObject,
    mut v_t_5026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5027_ = l_Lean_PersistentArray_toArray(v_00_u03b1_5025_, v_t_5026_);
    leanh::lean_dec_ref(v_t_5026_);
    return v_res_5027_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(
    mut v_00_u03b1_5028_: *mut leanh::LeanObject,
    mut v_t_5029_: *mut leanh::LeanObject,
    mut v_init_5030_: *mut leanh::LeanObject,
    mut v_start_5031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5032_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(
            v_t_5029_,
            v_init_5030_,
            v_start_5031_,
        );
    return v___x_5032_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___boxed(
    mut v_00_u03b1_5033_: *mut leanh::LeanObject,
    mut v_t_5034_: *mut leanh::LeanObject,
    mut v_init_5035_: *mut leanh::LeanObject,
    mut v_start_5036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5037_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(
        v_00_u03b1_5033_,
        v_t_5034_,
        v_init_5035_,
        v_start_5036_,
    );
    leanh::lean_dec(v_start_5036_);
    leanh::lean_dec_ref(v_t_5034_);
    return v_res_5037_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(
    mut v_00_u03b1_5038_: *mut leanh::LeanObject,
    mut v_x_5039_: *mut leanh::LeanObject,
    mut v_x_5040_: usize,
    mut v_x_5041_: usize,
    mut v_x_5042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5043_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_5039_, v_x_5040_, v_x_5041_, v_x_5042_);
    return v___x_5043_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___boxed(
    mut v_00_u03b1_5044_: *mut leanh::LeanObject,
    mut v_x_5045_: *mut leanh::LeanObject,
    mut v_x_5046_: *mut leanh::LeanObject,
    mut v_x_5047_: *mut leanh::LeanObject,
    mut v_x_5048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1655__boxed_5049_: usize = 0;
    let mut v_x_1656__boxed_5050_: usize = 0;
    let mut v_res_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1655__boxed_5049_ = leanh::lean_unbox_usize(v_x_5046_);
    leanh::lean_dec(v_x_5046_);
    v_x_1656__boxed_5050_ = leanh::lean_unbox_usize(v_x_5047_);
    leanh::lean_dec(v_x_5047_);
    v_res_5051_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(v_00_u03b1_5044_, v_x_5045_, v_x_1655__boxed_5049_, v_x_1656__boxed_5050_, v_x_5048_);
    leanh::lean_dec_ref(v_x_5045_);
    return v_res_5051_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(
    mut v_00_u03b1_5052_: *mut leanh::LeanObject,
    mut v_as_5053_: *mut leanh::LeanObject,
    mut v_i_5054_: usize,
    mut v_stop_5055_: usize,
    mut v_b_5056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_5053_, v_i_5054_, v_stop_5055_, v_b_5056_);
    return v___x_5057_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___boxed(
    mut v_00_u03b1_5058_: *mut leanh::LeanObject,
    mut v_as_5059_: *mut leanh::LeanObject,
    mut v_i_5060_: *mut leanh::LeanObject,
    mut v_stop_5061_: *mut leanh::LeanObject,
    mut v_b_5062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5063_: usize = 0;
    let mut v_stop_boxed_5064_: usize = 0;
    let mut v_res_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5063_ = leanh::lean_unbox_usize(v_i_5060_);
    leanh::lean_dec(v_i_5060_);
    v_stop_boxed_5064_ = leanh::lean_unbox_usize(v_stop_5061_);
    leanh::lean_dec(v_stop_5061_);
    v_res_5065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(v_00_u03b1_5058_, v_as_5059_, v_i_boxed_5063_, v_stop_boxed_5064_, v_b_5062_);
    leanh::lean_dec_ref(v_as_5059_);
    return v_res_5065_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(
    mut v_00_u03b1_5066_: *mut leanh::LeanObject,
    mut v_x_5067_: *mut leanh::LeanObject,
    mut v_x_5068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5069_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_5067_, v_x_5068_);
    return v___x_5069_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___boxed(
    mut v_00_u03b1_5070_: *mut leanh::LeanObject,
    mut v_x_5071_: *mut leanh::LeanObject,
    mut v_x_5072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5073_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(v_00_u03b1_5070_, v_x_5071_, v_x_5072_);
    leanh::lean_dec_ref(v_x_5071_);
    return v_res_5073_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(
    mut v_00_u03b1_5074_: *mut leanh::LeanObject,
    mut v_as_5075_: *mut leanh::LeanObject,
    mut v_i_5076_: usize,
    mut v_stop_5077_: usize,
    mut v_b_5078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_5075_, v_i_5076_, v_stop_5077_, v_b_5078_);
    return v___x_5079_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_5080_: *mut leanh::LeanObject,
    mut v_as_5081_: *mut leanh::LeanObject,
    mut v_i_5082_: *mut leanh::LeanObject,
    mut v_stop_5083_: *mut leanh::LeanObject,
    mut v_b_5084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5085_: usize = 0;
    let mut v_stop_boxed_5086_: usize = 0;
    let mut v_res_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5085_ = leanh::lean_unbox_usize(v_i_5082_);
    leanh::lean_dec(v_i_5082_);
    v_stop_boxed_5086_ = leanh::lean_unbox_usize(v_stop_5083_);
    leanh::lean_dec(v_stop_5083_);
    v_res_5087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(v_00_u03b1_5080_, v_as_5081_, v_i_boxed_5085_, v_stop_boxed_5086_, v_b_5084_);
    leanh::lean_dec_ref(v_as_5081_);
    return v_res_5087_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(
    mut v_as_5088_: *mut leanh::LeanObject,
    mut v_i_5089_: usize,
    mut v_stop_5090_: usize,
    mut v_b_5091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5092_: u8 = 0;
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: usize = 0;
    let mut v___x_5096_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5092_ = lean_usize_dec_eq(v_i_5089_, v_stop_5090_);
                if v___x_5092_ == 0 {
                    v___x_5093_ = lean_array_uget_borrowed(v_as_5088_, v_i_5089_);
                    leanh::lean_inc(v___x_5093_);
                    v___x_5094_ = l_Lean_PersistentArray_push___redArg(v_b_5091_, v___x_5093_);
                    v___x_5095_ = 1usize;
                    v___x_5096_ = lean_usize_add(v_i_5089_, v___x_5095_);
                    v_i_5089_ = v___x_5096_;
                    v_b_5091_ = v___x_5094_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5091_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg___boxed(
    mut v_as_5098_: *mut leanh::LeanObject,
    mut v_i_5099_: *mut leanh::LeanObject,
    mut v_stop_5100_: *mut leanh::LeanObject,
    mut v_b_5101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5102_: usize = 0;
    let mut v_stop_boxed_5103_: usize = 0;
    let mut v_res_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5102_ = leanh::lean_unbox_usize(v_i_5099_);
    leanh::lean_dec(v_i_5099_);
    v_stop_boxed_5103_ = leanh::lean_unbox_usize(v_stop_5100_);
    leanh::lean_dec(v_stop_5100_);
    v_res_5104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_5098_, v_i_boxed_5102_, v_stop_boxed_5103_, v_b_5101_);
    leanh::lean_dec_ref(v_as_5098_);
    return v_res_5104_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(
    mut v_x_5105_: *mut leanh::LeanObject,
    mut v_x_5106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5105_) == 0 {
        let mut v_cs_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5110_: u8 = 0;
        v_cs_5107_ = leanh::lean_ctor_get(v_x_5105_, 0);
        v___x_5108_ = leanh::lean_unsigned_to_nat(0);
        v___x_5109_ = lean_array_get_size(v_cs_5107_);
        v___x_5110_ = lean_nat_dec_lt(v___x_5108_, v___x_5109_);
        if v___x_5110_ == 0 {
            return v_x_5106_;
        } else {
            let mut v___x_5111_: u8 = 0;
            v___x_5111_ = lean_nat_dec_le(v___x_5109_, v___x_5109_);
            if v___x_5111_ == 0 {
                if v___x_5110_ == 0 {
                    return v_x_5106_;
                } else {
                    let mut v___x_5112_: usize = 0;
                    let mut v___x_5113_: usize = 0;
                    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5112_ = 0usize;
                    v___x_5113_ = lean_usize_of_nat(v___x_5109_);
                    v___x_5114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_5107_, v___x_5112_, v___x_5113_, v_x_5106_);
                    return v___x_5114_;
                }
            } else {
                let mut v___x_5115_: usize = 0;
                let mut v___x_5116_: usize = 0;
                let mut v___x_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5115_ = 0usize;
                v___x_5116_ = lean_usize_of_nat(v___x_5109_);
                v___x_5117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_5107_, v___x_5115_, v___x_5116_, v_x_5106_);
                return v___x_5117_;
            }
        }
    } else {
        let mut v_vs_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5121_: u8 = 0;
        v_vs_5118_ = leanh::lean_ctor_get(v_x_5105_, 0);
        v___x_5119_ = leanh::lean_unsigned_to_nat(0);
        v___x_5120_ = lean_array_get_size(v_vs_5118_);
        v___x_5121_ = lean_nat_dec_lt(v___x_5119_, v___x_5120_);
        if v___x_5121_ == 0 {
            return v_x_5106_;
        } else {
            let mut v___x_5122_: u8 = 0;
            v___x_5122_ = lean_nat_dec_le(v___x_5120_, v___x_5120_);
            if v___x_5122_ == 0 {
                if v___x_5121_ == 0 {
                    return v_x_5106_;
                } else {
                    let mut v___x_5123_: usize = 0;
                    let mut v___x_5124_: usize = 0;
                    let mut v___x_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5123_ = 0usize;
                    v___x_5124_ = lean_usize_of_nat(v___x_5120_);
                    v___x_5125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_5118_, v___x_5123_, v___x_5124_, v_x_5106_);
                    return v___x_5125_;
                }
            } else {
                let mut v___x_5126_: usize = 0;
                let mut v___x_5127_: usize = 0;
                let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5126_ = 0usize;
                v___x_5127_ = lean_usize_of_nat(v___x_5120_);
                v___x_5128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_5118_, v___x_5126_, v___x_5127_, v_x_5106_);
                return v___x_5128_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(
    mut v_as_5129_: *mut leanh::LeanObject,
    mut v_i_5130_: usize,
    mut v_stop_5131_: usize,
    mut v_b_5132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5133_: u8 = 0;
    let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: usize = 0;
    let mut v___x_5137_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5133_ = lean_usize_dec_eq(v_i_5130_, v_stop_5131_);
                if v___x_5133_ == 0 {
                    v___x_5134_ = lean_array_uget_borrowed(v_as_5129_, v_i_5130_);
                    v___x_5135_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v___x_5134_, v_b_5132_);
                    v___x_5136_ = 1usize;
                    v___x_5137_ = lean_usize_add(v_i_5130_, v___x_5136_);
                    v_i_5130_ = v___x_5137_;
                    v_b_5132_ = v___x_5135_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5132_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_as_5139_: *mut leanh::LeanObject,
    mut v_i_5140_: *mut leanh::LeanObject,
    mut v_stop_5141_: *mut leanh::LeanObject,
    mut v_b_5142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5143_: usize = 0;
    let mut v_stop_boxed_5144_: usize = 0;
    let mut v_res_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5143_ = leanh::lean_unbox_usize(v_i_5140_);
    leanh::lean_dec(v_i_5140_);
    v_stop_boxed_5144_ = leanh::lean_unbox_usize(v_stop_5141_);
    leanh::lean_dec(v_stop_5141_);
    v_res_5145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_5139_, v_i_boxed_5143_, v_stop_boxed_5144_, v_b_5142_);
    leanh::lean_dec_ref(v_as_5139_);
    return v_res_5145_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg___boxed(
    mut v_x_5146_: *mut leanh::LeanObject,
    mut v_x_5147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5148_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_5146_, v_x_5147_);
    leanh::lean_dec_ref(v_x_5146_);
    return v_res_5148_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(
    mut v_x_5149_: *mut leanh::LeanObject,
    mut v_x_5150_: usize,
    mut v_x_5151_: usize,
    mut v_x_5152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5149_) == 0 {
        let mut v_cs_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5155_: usize = 0;
        let mut v_j_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5158_: usize = 0;
        let mut v___x_5159_: usize = 0;
        let mut v___x_5160_: usize = 0;
        let mut v___x_5161_: usize = 0;
        let mut v___x_5162_: usize = 0;
        let mut v___x_5163_: usize = 0;
        let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5168_: u8 = 0;
        v_cs_5153_ = leanh::lean_ctor_get(v_x_5149_, 0);
        v___x_5154_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0),
            core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0_once),
            _init_l_Lean_instInhabitedPersistentArrayNode___closed__0,
        );
        v___x_5155_ = lean_usize_shift_right(v_x_5150_, v_x_5151_);
        v_j_5156_ = lean_usize_to_nat(v___x_5155_);
        v___x_5157_ = lean_array_get_borrowed(v___x_5154_, v_cs_5153_, v_j_5156_);
        v___x_5158_ = 1usize;
        v___x_5159_ = lean_usize_shift_left(v___x_5158_, v_x_5151_);
        v___x_5160_ = lean_usize_sub(v___x_5159_, v___x_5158_);
        v___x_5161_ = lean_usize_land(v_x_5150_, v___x_5160_);
        v___x_5162_ = 5usize;
        v___x_5163_ = lean_usize_sub(v_x_5151_, v___x_5162_);
        v___x_5164_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v___x_5157_, v___x_5161_, v___x_5163_, v_x_5152_);
        v___x_5165_ = leanh::lean_unsigned_to_nat(1);
        v___x_5166_ = lean_nat_add(v_j_5156_, v___x_5165_);
        leanh::lean_dec(v_j_5156_);
        v___x_5167_ = lean_array_get_size(v_cs_5153_);
        v___x_5168_ = lean_nat_dec_lt(v___x_5166_, v___x_5167_);
        if v___x_5168_ == 0 {
            leanh::lean_dec(v___x_5166_);
            return v___x_5164_;
        } else {
            let mut v___x_5169_: u8 = 0;
            v___x_5169_ = lean_nat_dec_le(v___x_5167_, v___x_5167_);
            if v___x_5169_ == 0 {
                if v___x_5168_ == 0 {
                    leanh::lean_dec(v___x_5166_);
                    return v___x_5164_;
                } else {
                    let mut v___x_5170_: usize = 0;
                    let mut v___x_5171_: usize = 0;
                    let mut v___x_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5170_ = lean_usize_of_nat(v___x_5166_);
                    leanh::lean_dec(v___x_5166_);
                    v___x_5171_ = lean_usize_of_nat(v___x_5167_);
                    v___x_5172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_5153_, v___x_5170_, v___x_5171_, v___x_5164_);
                    return v___x_5172_;
                }
            } else {
                let mut v___x_5173_: usize = 0;
                let mut v___x_5174_: usize = 0;
                let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5173_ = lean_usize_of_nat(v___x_5166_);
                leanh::lean_dec(v___x_5166_);
                v___x_5174_ = lean_usize_of_nat(v___x_5167_);
                v___x_5175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_5153_, v___x_5173_, v___x_5174_, v___x_5164_);
                return v___x_5175_;
            }
        }
    } else {
        let mut v_vs_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5179_: u8 = 0;
        v_vs_5176_ = leanh::lean_ctor_get(v_x_5149_, 0);
        v___x_5177_ = lean_usize_to_nat(v_x_5150_);
        v___x_5178_ = lean_array_get_size(v_vs_5176_);
        v___x_5179_ = lean_nat_dec_lt(v___x_5177_, v___x_5178_);
        if v___x_5179_ == 0 {
            leanh::lean_dec(v___x_5177_);
            return v_x_5152_;
        } else {
            let mut v___x_5180_: u8 = 0;
            v___x_5180_ = lean_nat_dec_le(v___x_5178_, v___x_5178_);
            if v___x_5180_ == 0 {
                if v___x_5179_ == 0 {
                    leanh::lean_dec(v___x_5177_);
                    return v_x_5152_;
                } else {
                    let mut v___x_5181_: usize = 0;
                    let mut v___x_5182_: usize = 0;
                    let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5181_ = lean_usize_of_nat(v___x_5177_);
                    leanh::lean_dec(v___x_5177_);
                    v___x_5182_ = lean_usize_of_nat(v___x_5178_);
                    v___x_5183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_5176_, v___x_5181_, v___x_5182_, v_x_5152_);
                    return v___x_5183_;
                }
            } else {
                let mut v___x_5184_: usize = 0;
                let mut v___x_5185_: usize = 0;
                let mut v___x_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5184_ = lean_usize_of_nat(v___x_5177_);
                leanh::lean_dec(v___x_5177_);
                v___x_5185_ = lean_usize_of_nat(v___x_5178_);
                v___x_5186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_5176_, v___x_5184_, v___x_5185_, v_x_5152_);
                return v___x_5186_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg___boxed(
    mut v_x_5187_: *mut leanh::LeanObject,
    mut v_x_5188_: *mut leanh::LeanObject,
    mut v_x_5189_: *mut leanh::LeanObject,
    mut v_x_5190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1523__boxed_5191_: usize = 0;
    let mut v_x_1524__boxed_5192_: usize = 0;
    let mut v_res_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1523__boxed_5191_ = leanh::lean_unbox_usize(v_x_5188_);
    leanh::lean_dec(v_x_5188_);
    v_x_1524__boxed_5192_ = leanh::lean_unbox_usize(v_x_5189_);
    leanh::lean_dec(v_x_5189_);
    v_res_5193_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_5187_, v_x_1523__boxed_5191_, v_x_1524__boxed_5192_, v_x_5190_);
    leanh::lean_dec_ref(v_x_5187_);
    return v_res_5193_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(
    mut v_t_5194_: *mut leanh::LeanObject,
    mut v_init_5195_: *mut leanh::LeanObject,
    mut v_start_5196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: u8 = 0;
    v___x_5197_ = leanh::lean_unsigned_to_nat(0);
    v___x_5198_ = lean_nat_dec_eq(v_start_5196_, v___x_5197_);
    if v___x_5198_ == 0 {
        let mut v_root_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_5201_: usize = 0;
        let mut v_tailOff_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5203_: u8 = 0;
        v_root_5199_ = leanh::lean_ctor_get(v_t_5194_, 0);
        v_tail_5200_ = leanh::lean_ctor_get(v_t_5194_, 1);
        v_shift_5201_ = leanh::lean_ctor_get_usize(v_t_5194_, 4);
        v_tailOff_5202_ = leanh::lean_ctor_get(v_t_5194_, 3);
        v___x_5203_ = lean_nat_dec_le(v_tailOff_5202_, v_start_5196_);
        if v___x_5203_ == 0 {
            let mut v___x_5204_: usize = 0;
            let mut v___x_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5207_: u8 = 0;
            v___x_5204_ = lean_usize_of_nat(v_start_5196_);
            v___x_5205_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_root_5199_, v___x_5204_, v_shift_5201_, v_init_5195_);
            v___x_5206_ = lean_array_get_size(v_tail_5200_);
            v___x_5207_ = lean_nat_dec_lt(v___x_5197_, v___x_5206_);
            if v___x_5207_ == 0 {
                return v___x_5205_;
            } else {
                let mut v___x_5208_: u8 = 0;
                v___x_5208_ = lean_nat_dec_le(v___x_5206_, v___x_5206_);
                if v___x_5208_ == 0 {
                    if v___x_5207_ == 0 {
                        return v___x_5205_;
                    } else {
                        let mut v___x_5209_: usize = 0;
                        let mut v___x_5210_: usize = 0;
                        let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_5209_ = 0usize;
                        v___x_5210_ = lean_usize_of_nat(v___x_5206_);
                        v___x_5211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_5200_, v___x_5209_, v___x_5210_, v___x_5205_);
                        return v___x_5211_;
                    }
                } else {
                    let mut v___x_5212_: usize = 0;
                    let mut v___x_5213_: usize = 0;
                    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5212_ = 0usize;
                    v___x_5213_ = lean_usize_of_nat(v___x_5206_);
                    v___x_5214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_5200_, v___x_5212_, v___x_5213_, v___x_5205_);
                    return v___x_5214_;
                }
            }
        } else {
            let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5217_: u8 = 0;
            v___x_5215_ = lean_nat_sub(v_start_5196_, v_tailOff_5202_);
            v___x_5216_ = lean_array_get_size(v_tail_5200_);
            v___x_5217_ = lean_nat_dec_lt(v___x_5215_, v___x_5216_);
            if v___x_5217_ == 0 {
                leanh::lean_dec(v___x_5215_);
                return v_init_5195_;
            } else {
                let mut v___x_5218_: u8 = 0;
                v___x_5218_ = lean_nat_dec_le(v___x_5216_, v___x_5216_);
                if v___x_5218_ == 0 {
                    if v___x_5217_ == 0 {
                        leanh::lean_dec(v___x_5215_);
                        return v_init_5195_;
                    } else {
                        let mut v___x_5219_: usize = 0;
                        let mut v___x_5220_: usize = 0;
                        let mut v___x_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_5219_ = lean_usize_of_nat(v___x_5215_);
                        leanh::lean_dec(v___x_5215_);
                        v___x_5220_ = lean_usize_of_nat(v___x_5216_);
                        v___x_5221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_5200_, v___x_5219_, v___x_5220_, v_init_5195_);
                        return v___x_5221_;
                    }
                } else {
                    let mut v___x_5222_: usize = 0;
                    let mut v___x_5223_: usize = 0;
                    let mut v___x_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5222_ = lean_usize_of_nat(v___x_5215_);
                    leanh::lean_dec(v___x_5215_);
                    v___x_5223_ = lean_usize_of_nat(v___x_5216_);
                    v___x_5224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_5200_, v___x_5222_, v___x_5223_, v_init_5195_);
                    return v___x_5224_;
                }
            }
        }
    } else {
        let mut v_root_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5229_: u8 = 0;
        v_root_5225_ = leanh::lean_ctor_get(v_t_5194_, 0);
        v_tail_5226_ = leanh::lean_ctor_get(v_t_5194_, 1);
        v___x_5227_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_root_5225_, v_init_5195_);
        v___x_5228_ = lean_array_get_size(v_tail_5226_);
        v___x_5229_ = lean_nat_dec_lt(v___x_5197_, v___x_5228_);
        if v___x_5229_ == 0 {
            return v___x_5227_;
        } else {
            let mut v___x_5230_: u8 = 0;
            v___x_5230_ = lean_nat_dec_le(v___x_5228_, v___x_5228_);
            if v___x_5230_ == 0 {
                if v___x_5229_ == 0 {
                    return v___x_5227_;
                } else {
                    let mut v___x_5231_: usize = 0;
                    let mut v___x_5232_: usize = 0;
                    let mut v___x_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5231_ = 0usize;
                    v___x_5232_ = lean_usize_of_nat(v___x_5228_);
                    v___x_5233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_5226_, v___x_5231_, v___x_5232_, v___x_5227_);
                    return v___x_5233_;
                }
            } else {
                let mut v___x_5234_: usize = 0;
                let mut v___x_5235_: usize = 0;
                let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5234_ = 0usize;
                v___x_5235_ = lean_usize_of_nat(v___x_5228_);
                v___x_5236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_5226_, v___x_5234_, v___x_5235_, v___x_5227_);
                return v___x_5236_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg___boxed(
    mut v_t_5237_: *mut leanh::LeanObject,
    mut v_init_5238_: *mut leanh::LeanObject,
    mut v_start_5239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5240_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(
            v_t_5237_,
            v_init_5238_,
            v_start_5239_,
        );
    leanh::lean_dec(v_start_5239_);
    leanh::lean_dec_ref(v_t_5237_);
    return v_res_5240_;
}
pub unsafe fn l_Lean_PersistentArray_append___redArg(
    mut v_t_u2081_5241_: *mut leanh::LeanObject,
    mut v_t_u2082_5242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5243_: u8 = 0;
    v___x_5243_ = l_Lean_PersistentArray_isEmpty___redArg(v_t_u2081_5241_);
    if v___x_5243_ == 0 {
        let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5244_ = leanh::lean_unsigned_to_nat(0);
        v___x_5245_ =
            l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(
                v_t_u2082_5242_,
                v_t_u2081_5241_,
                v___x_5244_,
            );
        return v___x_5245_;
    } else {
        leanh::lean_dec_ref(v_t_u2081_5241_);
        leanh::lean_inc_ref(v_t_u2082_5242_);
        return v_t_u2082_5242_;
    }
}
pub unsafe fn l_Lean_PersistentArray_append___redArg___boxed(
    mut v_t_u2081_5246_: *mut leanh::LeanObject,
    mut v_t_u2082_5247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5248_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_5246_, v_t_u2082_5247_);
    leanh::lean_dec_ref(v_t_u2082_5247_);
    return v_res_5248_;
}
pub unsafe fn l_Lean_PersistentArray_append(
    mut v_00_u03b1_5249_: *mut leanh::LeanObject,
    mut v_t_u2081_5250_: *mut leanh::LeanObject,
    mut v_t_u2082_5251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5252_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_5250_, v_t_u2082_5251_);
    return v___x_5252_;
}
pub unsafe fn l_Lean_PersistentArray_append___boxed(
    mut v_00_u03b1_5253_: *mut leanh::LeanObject,
    mut v_t_u2081_5254_: *mut leanh::LeanObject,
    mut v_t_u2082_5255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5256_ = l_Lean_PersistentArray_append(v_00_u03b1_5253_, v_t_u2081_5254_, v_t_u2082_5255_);
    leanh::lean_dec_ref(v_t_u2082_5255_);
    return v_res_5256_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(
    mut v_00_u03b1_5257_: *mut leanh::LeanObject,
    mut v_t_5258_: *mut leanh::LeanObject,
    mut v_init_5259_: *mut leanh::LeanObject,
    mut v_start_5260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5261_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(
            v_t_5258_,
            v_init_5259_,
            v_start_5260_,
        );
    return v___x_5261_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___boxed(
    mut v_00_u03b1_5262_: *mut leanh::LeanObject,
    mut v_t_5263_: *mut leanh::LeanObject,
    mut v_init_5264_: *mut leanh::LeanObject,
    mut v_start_5265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5266_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(
        v_00_u03b1_5262_,
        v_t_5263_,
        v_init_5264_,
        v_start_5265_,
    );
    leanh::lean_dec(v_start_5265_);
    leanh::lean_dec_ref(v_t_5263_);
    return v_res_5266_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(
    mut v_00_u03b1_5267_: *mut leanh::LeanObject,
    mut v_x_5268_: *mut leanh::LeanObject,
    mut v_x_5269_: usize,
    mut v_x_5270_: usize,
    mut v_x_5271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5272_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_5268_, v_x_5269_, v_x_5270_, v_x_5271_);
    return v___x_5272_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___boxed(
    mut v_00_u03b1_5273_: *mut leanh::LeanObject,
    mut v_x_5274_: *mut leanh::LeanObject,
    mut v_x_5275_: *mut leanh::LeanObject,
    mut v_x_5276_: *mut leanh::LeanObject,
    mut v_x_5277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1679__boxed_5278_: usize = 0;
    let mut v_x_1680__boxed_5279_: usize = 0;
    let mut v_res_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1679__boxed_5278_ = leanh::lean_unbox_usize(v_x_5275_);
    leanh::lean_dec(v_x_5275_);
    v_x_1680__boxed_5279_ = leanh::lean_unbox_usize(v_x_5276_);
    leanh::lean_dec(v_x_5276_);
    v_res_5280_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(v_00_u03b1_5273_, v_x_5274_, v_x_1679__boxed_5278_, v_x_1680__boxed_5279_, v_x_5277_);
    leanh::lean_dec_ref(v_x_5274_);
    return v_res_5280_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(
    mut v_00_u03b1_5281_: *mut leanh::LeanObject,
    mut v_as_5282_: *mut leanh::LeanObject,
    mut v_i_5283_: usize,
    mut v_stop_5284_: usize,
    mut v_b_5285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_5282_, v_i_5283_, v_stop_5284_, v_b_5285_);
    return v___x_5286_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___boxed(
    mut v_00_u03b1_5287_: *mut leanh::LeanObject,
    mut v_as_5288_: *mut leanh::LeanObject,
    mut v_i_5289_: *mut leanh::LeanObject,
    mut v_stop_5290_: *mut leanh::LeanObject,
    mut v_b_5291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5292_: usize = 0;
    let mut v_stop_boxed_5293_: usize = 0;
    let mut v_res_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5292_ = leanh::lean_unbox_usize(v_i_5289_);
    leanh::lean_dec(v_i_5289_);
    v_stop_boxed_5293_ = leanh::lean_unbox_usize(v_stop_5290_);
    leanh::lean_dec(v_stop_5290_);
    v_res_5294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(v_00_u03b1_5287_, v_as_5288_, v_i_boxed_5292_, v_stop_boxed_5293_, v_b_5291_);
    leanh::lean_dec_ref(v_as_5288_);
    return v_res_5294_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(
    mut v_00_u03b1_5295_: *mut leanh::LeanObject,
    mut v_x_5296_: *mut leanh::LeanObject,
    mut v_x_5297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5298_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_5296_, v_x_5297_);
    return v___x_5298_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___boxed(
    mut v_00_u03b1_5299_: *mut leanh::LeanObject,
    mut v_x_5300_: *mut leanh::LeanObject,
    mut v_x_5301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5302_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(v_00_u03b1_5299_, v_x_5300_, v_x_5301_);
    leanh::lean_dec_ref(v_x_5300_);
    return v_res_5302_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(
    mut v_00_u03b1_5303_: *mut leanh::LeanObject,
    mut v_as_5304_: *mut leanh::LeanObject,
    mut v_i_5305_: usize,
    mut v_stop_5306_: usize,
    mut v_b_5307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_5304_, v_i_5305_, v_stop_5306_, v_b_5307_);
    return v___x_5308_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_5309_: *mut leanh::LeanObject,
    mut v_as_5310_: *mut leanh::LeanObject,
    mut v_i_5311_: *mut leanh::LeanObject,
    mut v_stop_5312_: *mut leanh::LeanObject,
    mut v_b_5313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5314_: usize = 0;
    let mut v_stop_boxed_5315_: usize = 0;
    let mut v_res_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5314_ = leanh::lean_unbox_usize(v_i_5311_);
    leanh::lean_dec(v_i_5311_);
    v_stop_boxed_5315_ = leanh::lean_unbox_usize(v_stop_5312_);
    leanh::lean_dec(v_stop_5312_);
    v_res_5316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(v_00_u03b1_5309_, v_as_5310_, v_i_boxed_5314_, v_stop_boxed_5315_, v_b_5313_);
    leanh::lean_dec_ref(v_as_5310_);
    return v_res_5316_;
}
pub unsafe fn l_Lean_PersistentArray_instAppend(
    mut v_00_u03b1_5318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5319_ = l_Lean_PersistentArray_instAppend___closed__0;
    return v___x_5319_;
}
pub unsafe fn l_Lean_PersistentArray_findSome_x3f___redArg___lam__0(
    mut v_f_5320_: *mut leanh::LeanObject,
    mut v_x_5321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5322_ = leanh::lean_apply_1(v_f_5320_, v_x_5321_);
    return v___x_5322_;
}
pub unsafe fn l_Lean_PersistentArray_findSome_x3f___redArg(
    mut v_t_5323_: *mut leanh::LeanObject,
    mut v_f_5324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5325_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_findSome_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5325_, 0, v_f_5324_);
    v___x_5326_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5327_ =
        l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_5326_, v_t_5323_, v___f_5325_);
    return v___x_5327_;
}
pub unsafe fn l_Lean_PersistentArray_findSome_x3f(
    mut v_00_u03b1_5328_: *mut leanh::LeanObject,
    mut v_00_u03b2_5329_: *mut leanh::LeanObject,
    mut v_t_5330_: *mut leanh::LeanObject,
    mut v_f_5331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5332_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_findSome_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5332_, 0, v_f_5331_);
    v___x_5333_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5334_ =
        l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_5333_, v_t_5330_, v___f_5332_);
    return v___x_5334_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRev_x3f___redArg(
    mut v_t_5335_: *mut leanh::LeanObject,
    mut v_f_5336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5337_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_findSome_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5337_, 0, v_f_5336_);
    v___x_5338_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5339_ =
        l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_5338_, v_t_5335_, v___f_5337_);
    return v___x_5339_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRev_x3f(
    mut v_00_u03b1_5340_: *mut leanh::LeanObject,
    mut v_00_u03b2_5341_: *mut leanh::LeanObject,
    mut v_t_5342_: *mut leanh::LeanObject,
    mut v_f_5343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5344_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_findSome_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5344_, 0, v_f_5343_);
    v___x_5345_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5346_ =
        l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_5345_, v_t_5342_, v___f_5344_);
    return v___x_5346_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(
    mut v_as_5347_: *mut leanh::LeanObject,
    mut v_i_5348_: usize,
    mut v_stop_5349_: usize,
    mut v_b_5350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5351_: u8 = 0;
    let mut v___x_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: usize = 0;
    let mut v___x_5355_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5351_ = lean_usize_dec_eq(v_i_5348_, v_stop_5349_);
                if v___x_5351_ == 0 {
                    v___x_5352_ = lean_array_uget_borrowed(v_as_5347_, v_i_5348_);
                    leanh::lean_inc(v___x_5352_);
                    v___x_5353_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5353_, 0, v___x_5352_);
                    leanh::lean_ctor_set(v___x_5353_, 1, v_b_5350_);
                    v___x_5354_ = 1usize;
                    v___x_5355_ = lean_usize_add(v_i_5348_, v___x_5354_);
                    v_i_5348_ = v___x_5355_;
                    v_b_5350_ = v___x_5353_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5350_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg___boxed(
    mut v_as_5357_: *mut leanh::LeanObject,
    mut v_i_5358_: *mut leanh::LeanObject,
    mut v_stop_5359_: *mut leanh::LeanObject,
    mut v_b_5360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5361_: usize = 0;
    let mut v_stop_boxed_5362_: usize = 0;
    let mut v_res_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5361_ = leanh::lean_unbox_usize(v_i_5358_);
    leanh::lean_dec(v_i_5358_);
    v_stop_boxed_5362_ = leanh::lean_unbox_usize(v_stop_5359_);
    leanh::lean_dec(v_stop_5359_);
    v_res_5363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_5357_, v_i_boxed_5361_, v_stop_boxed_5362_, v_b_5360_);
    leanh::lean_dec_ref(v_as_5357_);
    return v_res_5363_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(
    mut v_x_5364_: *mut leanh::LeanObject,
    mut v_x_5365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5364_) == 0 {
        let mut v_cs_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5369_: u8 = 0;
        v_cs_5366_ = leanh::lean_ctor_get(v_x_5364_, 0);
        v___x_5367_ = leanh::lean_unsigned_to_nat(0);
        v___x_5368_ = lean_array_get_size(v_cs_5366_);
        v___x_5369_ = lean_nat_dec_lt(v___x_5367_, v___x_5368_);
        if v___x_5369_ == 0 {
            return v_x_5365_;
        } else {
            let mut v___x_5370_: u8 = 0;
            v___x_5370_ = lean_nat_dec_le(v___x_5368_, v___x_5368_);
            if v___x_5370_ == 0 {
                if v___x_5369_ == 0 {
                    return v_x_5365_;
                } else {
                    let mut v___x_5371_: usize = 0;
                    let mut v___x_5372_: usize = 0;
                    let mut v___x_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5371_ = 0usize;
                    v___x_5372_ = lean_usize_of_nat(v___x_5368_);
                    v___x_5373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_5366_, v___x_5371_, v___x_5372_, v_x_5365_);
                    return v___x_5373_;
                }
            } else {
                let mut v___x_5374_: usize = 0;
                let mut v___x_5375_: usize = 0;
                let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5374_ = 0usize;
                v___x_5375_ = lean_usize_of_nat(v___x_5368_);
                v___x_5376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_5366_, v___x_5374_, v___x_5375_, v_x_5365_);
                return v___x_5376_;
            }
        }
    } else {
        let mut v_vs_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5380_: u8 = 0;
        v_vs_5377_ = leanh::lean_ctor_get(v_x_5364_, 0);
        v___x_5378_ = leanh::lean_unsigned_to_nat(0);
        v___x_5379_ = lean_array_get_size(v_vs_5377_);
        v___x_5380_ = lean_nat_dec_lt(v___x_5378_, v___x_5379_);
        if v___x_5380_ == 0 {
            return v_x_5365_;
        } else {
            let mut v___x_5381_: u8 = 0;
            v___x_5381_ = lean_nat_dec_le(v___x_5379_, v___x_5379_);
            if v___x_5381_ == 0 {
                if v___x_5380_ == 0 {
                    return v_x_5365_;
                } else {
                    let mut v___x_5382_: usize = 0;
                    let mut v___x_5383_: usize = 0;
                    let mut v___x_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5382_ = 0usize;
                    v___x_5383_ = lean_usize_of_nat(v___x_5379_);
                    v___x_5384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_5377_, v___x_5382_, v___x_5383_, v_x_5365_);
                    return v___x_5384_;
                }
            } else {
                let mut v___x_5385_: usize = 0;
                let mut v___x_5386_: usize = 0;
                let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5385_ = 0usize;
                v___x_5386_ = lean_usize_of_nat(v___x_5379_);
                v___x_5387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_5377_, v___x_5385_, v___x_5386_, v_x_5365_);
                return v___x_5387_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(
    mut v_as_5388_: *mut leanh::LeanObject,
    mut v_i_5389_: usize,
    mut v_stop_5390_: usize,
    mut v_b_5391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5392_: u8 = 0;
    let mut v___x_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: usize = 0;
    let mut v___x_5396_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5392_ = lean_usize_dec_eq(v_i_5389_, v_stop_5390_);
                if v___x_5392_ == 0 {
                    v___x_5393_ = lean_array_uget_borrowed(v_as_5388_, v_i_5389_);
                    v___x_5394_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v___x_5393_, v_b_5391_);
                    v___x_5395_ = 1usize;
                    v___x_5396_ = lean_usize_add(v_i_5389_, v___x_5395_);
                    v_i_5389_ = v___x_5396_;
                    v_b_5391_ = v___x_5394_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5391_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_as_5398_: *mut leanh::LeanObject,
    mut v_i_5399_: *mut leanh::LeanObject,
    mut v_stop_5400_: *mut leanh::LeanObject,
    mut v_b_5401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5402_: usize = 0;
    let mut v_stop_boxed_5403_: usize = 0;
    let mut v_res_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5402_ = leanh::lean_unbox_usize(v_i_5399_);
    leanh::lean_dec(v_i_5399_);
    v_stop_boxed_5403_ = leanh::lean_unbox_usize(v_stop_5400_);
    leanh::lean_dec(v_stop_5400_);
    v_res_5404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_5398_, v_i_boxed_5402_, v_stop_boxed_5403_, v_b_5401_);
    leanh::lean_dec_ref(v_as_5398_);
    return v_res_5404_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg___boxed(
    mut v_x_5405_: *mut leanh::LeanObject,
    mut v_x_5406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5407_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_5405_, v_x_5406_);
    leanh::lean_dec_ref(v_x_5405_);
    return v_res_5407_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(
    mut v_x_5408_: *mut leanh::LeanObject,
    mut v_x_5409_: usize,
    mut v_x_5410_: usize,
    mut v_x_5411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5408_) == 0 {
        let mut v_cs_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5414_: usize = 0;
        let mut v_j_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5417_: usize = 0;
        let mut v___x_5418_: usize = 0;
        let mut v___x_5419_: usize = 0;
        let mut v___x_5420_: usize = 0;
        let mut v___x_5421_: usize = 0;
        let mut v___x_5422_: usize = 0;
        let mut v___x_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5427_: u8 = 0;
        v_cs_5412_ = leanh::lean_ctor_get(v_x_5408_, 0);
        v___x_5413_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0),
            core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0_once),
            _init_l_Lean_instInhabitedPersistentArrayNode___closed__0,
        );
        v___x_5414_ = lean_usize_shift_right(v_x_5409_, v_x_5410_);
        v_j_5415_ = lean_usize_to_nat(v___x_5414_);
        v___x_5416_ = lean_array_get_borrowed(v___x_5413_, v_cs_5412_, v_j_5415_);
        v___x_5417_ = 1usize;
        v___x_5418_ = lean_usize_shift_left(v___x_5417_, v_x_5410_);
        v___x_5419_ = lean_usize_sub(v___x_5418_, v___x_5417_);
        v___x_5420_ = lean_usize_land(v_x_5409_, v___x_5419_);
        v___x_5421_ = 5usize;
        v___x_5422_ = lean_usize_sub(v_x_5410_, v___x_5421_);
        v___x_5423_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v___x_5416_, v___x_5420_, v___x_5422_, v_x_5411_);
        v___x_5424_ = leanh::lean_unsigned_to_nat(1);
        v___x_5425_ = lean_nat_add(v_j_5415_, v___x_5424_);
        leanh::lean_dec(v_j_5415_);
        v___x_5426_ = lean_array_get_size(v_cs_5412_);
        v___x_5427_ = lean_nat_dec_lt(v___x_5425_, v___x_5426_);
        if v___x_5427_ == 0 {
            leanh::lean_dec(v___x_5425_);
            return v___x_5423_;
        } else {
            let mut v___x_5428_: u8 = 0;
            v___x_5428_ = lean_nat_dec_le(v___x_5426_, v___x_5426_);
            if v___x_5428_ == 0 {
                if v___x_5427_ == 0 {
                    leanh::lean_dec(v___x_5425_);
                    return v___x_5423_;
                } else {
                    let mut v___x_5429_: usize = 0;
                    let mut v___x_5430_: usize = 0;
                    let mut v___x_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5429_ = lean_usize_of_nat(v___x_5425_);
                    leanh::lean_dec(v___x_5425_);
                    v___x_5430_ = lean_usize_of_nat(v___x_5426_);
                    v___x_5431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_5412_, v___x_5429_, v___x_5430_, v___x_5423_);
                    return v___x_5431_;
                }
            } else {
                let mut v___x_5432_: usize = 0;
                let mut v___x_5433_: usize = 0;
                let mut v___x_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5432_ = lean_usize_of_nat(v___x_5425_);
                leanh::lean_dec(v___x_5425_);
                v___x_5433_ = lean_usize_of_nat(v___x_5426_);
                v___x_5434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_5412_, v___x_5432_, v___x_5433_, v___x_5423_);
                return v___x_5434_;
            }
        }
    } else {
        let mut v_vs_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5438_: u8 = 0;
        v_vs_5435_ = leanh::lean_ctor_get(v_x_5408_, 0);
        v___x_5436_ = lean_usize_to_nat(v_x_5409_);
        v___x_5437_ = lean_array_get_size(v_vs_5435_);
        v___x_5438_ = lean_nat_dec_lt(v___x_5436_, v___x_5437_);
        if v___x_5438_ == 0 {
            leanh::lean_dec(v___x_5436_);
            return v_x_5411_;
        } else {
            let mut v___x_5439_: u8 = 0;
            v___x_5439_ = lean_nat_dec_le(v___x_5437_, v___x_5437_);
            if v___x_5439_ == 0 {
                if v___x_5438_ == 0 {
                    leanh::lean_dec(v___x_5436_);
                    return v_x_5411_;
                } else {
                    let mut v___x_5440_: usize = 0;
                    let mut v___x_5441_: usize = 0;
                    let mut v___x_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5440_ = lean_usize_of_nat(v___x_5436_);
                    leanh::lean_dec(v___x_5436_);
                    v___x_5441_ = lean_usize_of_nat(v___x_5437_);
                    v___x_5442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_5435_, v___x_5440_, v___x_5441_, v_x_5411_);
                    return v___x_5442_;
                }
            } else {
                let mut v___x_5443_: usize = 0;
                let mut v___x_5444_: usize = 0;
                let mut v___x_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5443_ = lean_usize_of_nat(v___x_5436_);
                leanh::lean_dec(v___x_5436_);
                v___x_5444_ = lean_usize_of_nat(v___x_5437_);
                v___x_5445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_5435_, v___x_5443_, v___x_5444_, v_x_5411_);
                return v___x_5445_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg___boxed(
    mut v_x_5446_: *mut leanh::LeanObject,
    mut v_x_5447_: *mut leanh::LeanObject,
    mut v_x_5448_: *mut leanh::LeanObject,
    mut v_x_5449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1497__boxed_5450_: usize = 0;
    let mut v_x_1498__boxed_5451_: usize = 0;
    let mut v_res_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1497__boxed_5450_ = leanh::lean_unbox_usize(v_x_5447_);
    leanh::lean_dec(v_x_5447_);
    v_x_1498__boxed_5451_ = leanh::lean_unbox_usize(v_x_5448_);
    leanh::lean_dec(v_x_5448_);
    v_res_5452_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_5446_, v_x_1497__boxed_5450_, v_x_1498__boxed_5451_, v_x_5449_);
    leanh::lean_dec_ref(v_x_5446_);
    return v_res_5452_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(
    mut v_t_5453_: *mut leanh::LeanObject,
    mut v_init_5454_: *mut leanh::LeanObject,
    mut v_start_5455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: u8 = 0;
    v___x_5456_ = leanh::lean_unsigned_to_nat(0);
    v___x_5457_ = lean_nat_dec_eq(v_start_5455_, v___x_5456_);
    if v___x_5457_ == 0 {
        let mut v_root_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_5460_: usize = 0;
        let mut v_tailOff_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5462_: u8 = 0;
        v_root_5458_ = leanh::lean_ctor_get(v_t_5453_, 0);
        v_tail_5459_ = leanh::lean_ctor_get(v_t_5453_, 1);
        v_shift_5460_ = leanh::lean_ctor_get_usize(v_t_5453_, 4);
        v_tailOff_5461_ = leanh::lean_ctor_get(v_t_5453_, 3);
        v___x_5462_ = lean_nat_dec_le(v_tailOff_5461_, v_start_5455_);
        if v___x_5462_ == 0 {
            let mut v___x_5463_: usize = 0;
            let mut v___x_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5466_: u8 = 0;
            v___x_5463_ = lean_usize_of_nat(v_start_5455_);
            v___x_5464_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_root_5458_, v___x_5463_, v_shift_5460_, v_init_5454_);
            v___x_5465_ = lean_array_get_size(v_tail_5459_);
            v___x_5466_ = lean_nat_dec_lt(v___x_5456_, v___x_5465_);
            if v___x_5466_ == 0 {
                return v___x_5464_;
            } else {
                let mut v___x_5467_: u8 = 0;
                v___x_5467_ = lean_nat_dec_le(v___x_5465_, v___x_5465_);
                if v___x_5467_ == 0 {
                    if v___x_5466_ == 0 {
                        return v___x_5464_;
                    } else {
                        let mut v___x_5468_: usize = 0;
                        let mut v___x_5469_: usize = 0;
                        let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_5468_ = 0usize;
                        v___x_5469_ = lean_usize_of_nat(v___x_5465_);
                        v___x_5470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_5459_, v___x_5468_, v___x_5469_, v___x_5464_);
                        return v___x_5470_;
                    }
                } else {
                    let mut v___x_5471_: usize = 0;
                    let mut v___x_5472_: usize = 0;
                    let mut v___x_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5471_ = 0usize;
                    v___x_5472_ = lean_usize_of_nat(v___x_5465_);
                    v___x_5473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_5459_, v___x_5471_, v___x_5472_, v___x_5464_);
                    return v___x_5473_;
                }
            }
        } else {
            let mut v___x_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5476_: u8 = 0;
            v___x_5474_ = lean_nat_sub(v_start_5455_, v_tailOff_5461_);
            v___x_5475_ = lean_array_get_size(v_tail_5459_);
            v___x_5476_ = lean_nat_dec_lt(v___x_5474_, v___x_5475_);
            if v___x_5476_ == 0 {
                leanh::lean_dec(v___x_5474_);
                return v_init_5454_;
            } else {
                let mut v___x_5477_: u8 = 0;
                v___x_5477_ = lean_nat_dec_le(v___x_5475_, v___x_5475_);
                if v___x_5477_ == 0 {
                    if v___x_5476_ == 0 {
                        leanh::lean_dec(v___x_5474_);
                        return v_init_5454_;
                    } else {
                        let mut v___x_5478_: usize = 0;
                        let mut v___x_5479_: usize = 0;
                        let mut v___x_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_5478_ = lean_usize_of_nat(v___x_5474_);
                        leanh::lean_dec(v___x_5474_);
                        v___x_5479_ = lean_usize_of_nat(v___x_5475_);
                        v___x_5480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_5459_, v___x_5478_, v___x_5479_, v_init_5454_);
                        return v___x_5480_;
                    }
                } else {
                    let mut v___x_5481_: usize = 0;
                    let mut v___x_5482_: usize = 0;
                    let mut v___x_5483_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5481_ = lean_usize_of_nat(v___x_5474_);
                    leanh::lean_dec(v___x_5474_);
                    v___x_5482_ = lean_usize_of_nat(v___x_5475_);
                    v___x_5483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_5459_, v___x_5481_, v___x_5482_, v_init_5454_);
                    return v___x_5483_;
                }
            }
        }
    } else {
        let mut v_root_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5488_: u8 = 0;
        v_root_5484_ = leanh::lean_ctor_get(v_t_5453_, 0);
        v_tail_5485_ = leanh::lean_ctor_get(v_t_5453_, 1);
        v___x_5486_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_root_5484_, v_init_5454_);
        v___x_5487_ = lean_array_get_size(v_tail_5485_);
        v___x_5488_ = lean_nat_dec_lt(v___x_5456_, v___x_5487_);
        if v___x_5488_ == 0 {
            return v___x_5486_;
        } else {
            let mut v___x_5489_: u8 = 0;
            v___x_5489_ = lean_nat_dec_le(v___x_5487_, v___x_5487_);
            if v___x_5489_ == 0 {
                if v___x_5488_ == 0 {
                    return v___x_5486_;
                } else {
                    let mut v___x_5490_: usize = 0;
                    let mut v___x_5491_: usize = 0;
                    let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5490_ = 0usize;
                    v___x_5491_ = lean_usize_of_nat(v___x_5487_);
                    v___x_5492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_5485_, v___x_5490_, v___x_5491_, v___x_5486_);
                    return v___x_5492_;
                }
            } else {
                let mut v___x_5493_: usize = 0;
                let mut v___x_5494_: usize = 0;
                let mut v___x_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5493_ = 0usize;
                v___x_5494_ = lean_usize_of_nat(v___x_5487_);
                v___x_5495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_5485_, v___x_5493_, v___x_5494_, v___x_5486_);
                return v___x_5495_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg___boxed(
    mut v_t_5496_: *mut leanh::LeanObject,
    mut v_init_5497_: *mut leanh::LeanObject,
    mut v_start_5498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5499_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(
            v_t_5496_,
            v_init_5497_,
            v_start_5498_,
        );
    leanh::lean_dec(v_start_5498_);
    leanh::lean_dec_ref(v_t_5496_);
    return v_res_5499_;
}
pub unsafe fn l_Lean_PersistentArray_toList___redArg(
    mut v_t_5500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5501_ = leanh::lean_box(0);
    v___x_5502_ = leanh::lean_unsigned_to_nat(0);
    v___x_5503_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(
            v_t_5500_,
            v___x_5501_,
            v___x_5502_,
        );
    v___x_5504_ = l_List_reverse___redArg(v___x_5503_);
    return v___x_5504_;
}
pub unsafe fn l_Lean_PersistentArray_toList___redArg___boxed(
    mut v_t_5505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5506_ = l_Lean_PersistentArray_toList___redArg(v_t_5505_);
    leanh::lean_dec_ref(v_t_5505_);
    return v_res_5506_;
}
pub unsafe fn l_Lean_PersistentArray_toList(
    mut v_00_u03b1_5507_: *mut leanh::LeanObject,
    mut v_t_5508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5509_ = l_Lean_PersistentArray_toList___redArg(v_t_5508_);
    return v___x_5509_;
}
pub unsafe fn l_Lean_PersistentArray_toList___boxed(
    mut v_00_u03b1_5510_: *mut leanh::LeanObject,
    mut v_t_5511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5512_ = l_Lean_PersistentArray_toList(v_00_u03b1_5510_, v_t_5511_);
    leanh::lean_dec_ref(v_t_5511_);
    return v_res_5512_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(
    mut v_00_u03b1_5513_: *mut leanh::LeanObject,
    mut v_t_5514_: *mut leanh::LeanObject,
    mut v_init_5515_: *mut leanh::LeanObject,
    mut v_start_5516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5517_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(
            v_t_5514_,
            v_init_5515_,
            v_start_5516_,
        );
    return v___x_5517_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___boxed(
    mut v_00_u03b1_5518_: *mut leanh::LeanObject,
    mut v_t_5519_: *mut leanh::LeanObject,
    mut v_init_5520_: *mut leanh::LeanObject,
    mut v_start_5521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5522_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(
        v_00_u03b1_5518_,
        v_t_5519_,
        v_init_5520_,
        v_start_5521_,
    );
    leanh::lean_dec(v_start_5521_);
    leanh::lean_dec_ref(v_t_5519_);
    return v_res_5522_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(
    mut v_00_u03b1_5523_: *mut leanh::LeanObject,
    mut v_x_5524_: *mut leanh::LeanObject,
    mut v_x_5525_: usize,
    mut v_x_5526_: usize,
    mut v_x_5527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5528_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_5524_, v_x_5525_, v_x_5526_, v_x_5527_);
    return v___x_5528_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___boxed(
    mut v_00_u03b1_5529_: *mut leanh::LeanObject,
    mut v_x_5530_: *mut leanh::LeanObject,
    mut v_x_5531_: *mut leanh::LeanObject,
    mut v_x_5532_: *mut leanh::LeanObject,
    mut v_x_5533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1655__boxed_5534_: usize = 0;
    let mut v_x_1656__boxed_5535_: usize = 0;
    let mut v_res_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1655__boxed_5534_ = leanh::lean_unbox_usize(v_x_5531_);
    leanh::lean_dec(v_x_5531_);
    v_x_1656__boxed_5535_ = leanh::lean_unbox_usize(v_x_5532_);
    leanh::lean_dec(v_x_5532_);
    v_res_5536_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(v_00_u03b1_5529_, v_x_5530_, v_x_1655__boxed_5534_, v_x_1656__boxed_5535_, v_x_5533_);
    leanh::lean_dec_ref(v_x_5530_);
    return v_res_5536_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(
    mut v_00_u03b1_5537_: *mut leanh::LeanObject,
    mut v_as_5538_: *mut leanh::LeanObject,
    mut v_i_5539_: usize,
    mut v_stop_5540_: usize,
    mut v_b_5541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_5538_, v_i_5539_, v_stop_5540_, v_b_5541_);
    return v___x_5542_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___boxed(
    mut v_00_u03b1_5543_: *mut leanh::LeanObject,
    mut v_as_5544_: *mut leanh::LeanObject,
    mut v_i_5545_: *mut leanh::LeanObject,
    mut v_stop_5546_: *mut leanh::LeanObject,
    mut v_b_5547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5548_: usize = 0;
    let mut v_stop_boxed_5549_: usize = 0;
    let mut v_res_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5548_ = leanh::lean_unbox_usize(v_i_5545_);
    leanh::lean_dec(v_i_5545_);
    v_stop_boxed_5549_ = leanh::lean_unbox_usize(v_stop_5546_);
    leanh::lean_dec(v_stop_5546_);
    v_res_5550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(v_00_u03b1_5543_, v_as_5544_, v_i_boxed_5548_, v_stop_boxed_5549_, v_b_5547_);
    leanh::lean_dec_ref(v_as_5544_);
    return v_res_5550_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(
    mut v_00_u03b1_5551_: *mut leanh::LeanObject,
    mut v_x_5552_: *mut leanh::LeanObject,
    mut v_x_5553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5554_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_5552_, v_x_5553_);
    return v___x_5554_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___boxed(
    mut v_00_u03b1_5555_: *mut leanh::LeanObject,
    mut v_x_5556_: *mut leanh::LeanObject,
    mut v_x_5557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5558_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(v_00_u03b1_5555_, v_x_5556_, v_x_5557_);
    leanh::lean_dec_ref(v_x_5556_);
    return v_res_5558_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(
    mut v_00_u03b1_5559_: *mut leanh::LeanObject,
    mut v_as_5560_: *mut leanh::LeanObject,
    mut v_i_5561_: usize,
    mut v_stop_5562_: usize,
    mut v_b_5563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_5560_, v_i_5561_, v_stop_5562_, v_b_5563_);
    return v___x_5564_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_5565_: *mut leanh::LeanObject,
    mut v_as_5566_: *mut leanh::LeanObject,
    mut v_i_5567_: *mut leanh::LeanObject,
    mut v_stop_5568_: *mut leanh::LeanObject,
    mut v_b_5569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5570_: usize = 0;
    let mut v_stop_boxed_5571_: usize = 0;
    let mut v_res_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5570_ = leanh::lean_unbox_usize(v_i_5567_);
    leanh::lean_dec(v_i_5567_);
    v_stop_boxed_5571_ = leanh::lean_unbox_usize(v_stop_5568_);
    leanh::lean_dec(v_stop_5568_);
    v_res_5572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(v_00_u03b1_5565_, v_as_5566_, v_i_boxed_5570_, v_stop_boxed_5571_, v_b_5569_);
    leanh::lean_dec_ref(v_as_5566_);
    return v_res_5572_;
}
pub unsafe fn l_Lean_PersistentArray_anyMAux___redArg(
    mut v_inst_5573_: *mut leanh::LeanObject,
    mut v_p_5574_: *mut leanh::LeanObject,
    mut v_x_5575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5575_) == 0 {
        let mut v_cs_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5577_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5578_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5579_: u8 = 0;
        v_cs_5576_ = leanh::lean_ctor_get(v_x_5575_, 0);
        leanh::lean_inc_ref(v_cs_5576_);
        leanh::lean_dec_ref_known(v_x_5575_, 1);
        v___x_5577_ = leanh::lean_unsigned_to_nat(0);
        v___x_5578_ = lean_array_get_size(v_cs_5576_);
        v___x_5579_ = lean_nat_dec_lt(v___x_5577_, v___x_5578_);
        if v___x_5579_ == 0 {
            let mut v_toApplicative_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5582_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_cs_5576_);
            leanh::lean_dec(v_p_5574_);
            v_toApplicative_5580_ = leanh::lean_ctor_get(v_inst_5573_, 0);
            leanh::lean_inc_ref(v_toApplicative_5580_);
            leanh::lean_dec_ref(v_inst_5573_);
            v_toPure_5581_ = leanh::lean_ctor_get(v_toApplicative_5580_, 1);
            leanh::lean_inc(v_toPure_5581_);
            leanh::lean_dec_ref(v_toApplicative_5580_);
            v___x_5582_ = leanh::lean_box((v___x_5579_) as usize);
            v___x_5583_ =
                leanh::lean_apply_2(v_toPure_5581_, leanh::lean_box(0), v___x_5582_);
            return v___x_5583_;
        } else {
            if v___x_5579_ == 0 {
                let mut v_toApplicative_5584_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_cs_5576_);
                leanh::lean_dec(v_p_5574_);
                v_toApplicative_5584_ = leanh::lean_ctor_get(v_inst_5573_, 0);
                leanh::lean_inc_ref(v_toApplicative_5584_);
                leanh::lean_dec_ref(v_inst_5573_);
                v_toPure_5585_ = leanh::lean_ctor_get(v_toApplicative_5584_, 1);
                leanh::lean_inc(v_toPure_5585_);
                leanh::lean_dec_ref(v_toApplicative_5584_);
                v___x_5586_ = leanh::lean_box((v___x_5579_) as usize);
                v___x_5587_ = leanh::lean_apply_2(
                    v_toPure_5585_,
                    leanh::lean_box(0),
                    v___x_5586_,
                );
                return v___x_5587_;
            } else {
                let mut v___f_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5589_: usize = 0;
                let mut v___x_5590_: usize = 0;
                let mut v___x_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc_ref(v_inst_5573_);
                v___f_5588_ = leanh::lean_alloc_closure(
                    l_Lean_PersistentArray_anyMAux___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_5588_, 0, v_inst_5573_);
                leanh::lean_closure_set(v___f_5588_, 1, v_p_5574_);
                v___x_5589_ = 0usize;
                v___x_5590_ = lean_usize_of_nat(v___x_5578_);
                v___x_5591_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_5573_,
                    v___f_5588_,
                    v_cs_5576_,
                    v___x_5589_,
                    v___x_5590_,
                );
                return v___x_5591_;
            }
        }
    } else {
        let mut v_vs_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5595_: u8 = 0;
        v_vs_5592_ = leanh::lean_ctor_get(v_x_5575_, 0);
        leanh::lean_inc_ref(v_vs_5592_);
        leanh::lean_dec_ref_known(v_x_5575_, 1);
        v___x_5593_ = leanh::lean_unsigned_to_nat(0);
        v___x_5594_ = lean_array_get_size(v_vs_5592_);
        v___x_5595_ = lean_nat_dec_lt(v___x_5593_, v___x_5594_);
        if v___x_5595_ == 0 {
            let mut v_toApplicative_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_vs_5592_);
            leanh::lean_dec(v_p_5574_);
            v_toApplicative_5596_ = leanh::lean_ctor_get(v_inst_5573_, 0);
            leanh::lean_inc_ref(v_toApplicative_5596_);
            leanh::lean_dec_ref(v_inst_5573_);
            v_toPure_5597_ = leanh::lean_ctor_get(v_toApplicative_5596_, 1);
            leanh::lean_inc(v_toPure_5597_);
            leanh::lean_dec_ref(v_toApplicative_5596_);
            v___x_5598_ = leanh::lean_box((v___x_5595_) as usize);
            v___x_5599_ =
                leanh::lean_apply_2(v_toPure_5597_, leanh::lean_box(0), v___x_5598_);
            return v___x_5599_;
        } else {
            if v___x_5595_ == 0 {
                let mut v_toApplicative_5600_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_vs_5592_);
                leanh::lean_dec(v_p_5574_);
                v_toApplicative_5600_ = leanh::lean_ctor_get(v_inst_5573_, 0);
                leanh::lean_inc_ref(v_toApplicative_5600_);
                leanh::lean_dec_ref(v_inst_5573_);
                v_toPure_5601_ = leanh::lean_ctor_get(v_toApplicative_5600_, 1);
                leanh::lean_inc(v_toPure_5601_);
                leanh::lean_dec_ref(v_toApplicative_5600_);
                v___x_5602_ = leanh::lean_box((v___x_5595_) as usize);
                v___x_5603_ = leanh::lean_apply_2(
                    v_toPure_5601_,
                    leanh::lean_box(0),
                    v___x_5602_,
                );
                return v___x_5603_;
            } else {
                let mut v___x_5604_: usize = 0;
                let mut v___x_5605_: usize = 0;
                let mut v___x_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5604_ = 0usize;
                v___x_5605_ = lean_usize_of_nat(v___x_5594_);
                v___x_5606_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_5573_,
                    v_p_5574_,
                    v_vs_5592_,
                    v___x_5604_,
                    v___x_5605_,
                );
                return v___x_5606_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_anyMAux___redArg___lam__0(
    mut v_inst_5607_: *mut leanh::LeanObject,
    mut v_p_5608_: *mut leanh::LeanObject,
    mut v_c_5609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5610_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_5607_, v_p_5608_, v_c_5609_);
    return v___x_5610_;
}
pub unsafe fn l_Lean_PersistentArray_anyMAux(
    mut v_00_u03b1_5611_: *mut leanh::LeanObject,
    mut v_m_5612_: *mut leanh::LeanObject,
    mut v_inst_5613_: *mut leanh::LeanObject,
    mut v_p_5614_: *mut leanh::LeanObject,
    mut v_x_5615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5616_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_5613_, v_p_5614_, v_x_5615_);
    return v___x_5616_;
}
pub unsafe fn l_Lean_PersistentArray_anyM___redArg___lam__0(
    mut v_tail_5617_: *mut leanh::LeanObject,
    mut v_toPure_5618_: *mut leanh::LeanObject,
    mut v_inst_5619_: *mut leanh::LeanObject,
    mut v_p_5620_: *mut leanh::LeanObject,
    mut v_b_5621_: u8,
) -> *mut leanh::LeanObject {
    if v_b_5621_ == 0 {
        let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5624_: u8 = 0;
        v___x_5622_ = leanh::lean_unsigned_to_nat(0);
        v___x_5623_ = lean_array_get_size(v_tail_5617_);
        v___x_5624_ = lean_nat_dec_lt(v___x_5622_, v___x_5623_);
        if v___x_5624_ == 0 {
            let mut v___x_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_p_5620_);
            leanh::lean_dec_ref(v_inst_5619_);
            leanh::lean_dec_ref(v_tail_5617_);
            v___x_5625_ = leanh::lean_box((v_b_5621_) as usize);
            v___x_5626_ =
                leanh::lean_apply_2(v_toPure_5618_, leanh::lean_box(0), v___x_5625_);
            return v___x_5626_;
        } else {
            if v___x_5624_ == 0 {
                let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_p_5620_);
                leanh::lean_dec_ref(v_inst_5619_);
                leanh::lean_dec_ref(v_tail_5617_);
                v___x_5627_ = leanh::lean_box((v_b_5621_) as usize);
                v___x_5628_ = leanh::lean_apply_2(
                    v_toPure_5618_,
                    leanh::lean_box(0),
                    v___x_5627_,
                );
                return v___x_5628_;
            } else {
                let mut v___x_5629_: usize = 0;
                let mut v___x_5630_: usize = 0;
                let mut v___x_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_toPure_5618_);
                v___x_5629_ = 0usize;
                v___x_5630_ = lean_usize_of_nat(v___x_5623_);
                v___x_5631_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_5619_,
                    v_p_5620_,
                    v_tail_5617_,
                    v___x_5629_,
                    v___x_5630_,
                );
                return v___x_5631_;
            }
        }
    } else {
        let mut v___x_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_p_5620_);
        leanh::lean_dec_ref(v_inst_5619_);
        leanh::lean_dec_ref(v_tail_5617_);
        v___x_5632_ = leanh::lean_box((v_b_5621_) as usize);
        v___x_5633_ =
            leanh::lean_apply_2(v_toPure_5618_, leanh::lean_box(0), v___x_5632_);
        return v___x_5633_;
    }
}
pub unsafe fn l_Lean_PersistentArray_anyM___redArg___lam__0___boxed(
    mut v_tail_5634_: *mut leanh::LeanObject,
    mut v_toPure_5635_: *mut leanh::LeanObject,
    mut v_inst_5636_: *mut leanh::LeanObject,
    mut v_p_5637_: *mut leanh::LeanObject,
    mut v_b_5638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_5639_: u8 = 0;
    let mut v_res_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_5639_ = (leanh::lean_unbox(v_b_5638_) as u8);
    v_res_5640_ = l_Lean_PersistentArray_anyM___redArg___lam__0(
        v_tail_5634_,
        v_toPure_5635_,
        v_inst_5636_,
        v_p_5637_,
        v_b_boxed_5639_,
    );
    return v_res_5640_;
}
pub unsafe fn l_Lean_PersistentArray_anyM___redArg(
    mut v_inst_5641_: *mut leanh::LeanObject,
    mut v_t_5642_: *mut leanh::LeanObject,
    mut v_p_5643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5644_ = leanh::lean_ctor_get(v_inst_5641_, 0);
    v_toBind_5645_ = leanh::lean_ctor_get(v_inst_5641_, 1);
    leanh::lean_inc(v_toBind_5645_);
    v_root_5646_ = leanh::lean_ctor_get(v_t_5642_, 0);
    leanh::lean_inc_ref(v_root_5646_);
    v_tail_5647_ = leanh::lean_ctor_get(v_t_5642_, 1);
    leanh::lean_inc_ref(v_tail_5647_);
    leanh::lean_dec_ref(v_t_5642_);
    v_toPure_5648_ = leanh::lean_ctor_get(v_toApplicative_5644_, 1);
    leanh::lean_inc(v_toPure_5648_);
    leanh::lean_inc(v_p_5643_);
    leanh::lean_inc_ref(v_inst_5641_);
    v___x_5649_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_5641_, v_p_5643_, v_root_5646_);
    v___f_5650_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_anyM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_5650_, 0, v_tail_5647_);
    leanh::lean_closure_set(v___f_5650_, 1, v_toPure_5648_);
    leanh::lean_closure_set(v___f_5650_, 2, v_inst_5641_);
    leanh::lean_closure_set(v___f_5650_, 3, v_p_5643_);
    v___x_5651_ = leanh::lean_apply_4(
        v_toBind_5645_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5649_,
        v___f_5650_,
    );
    return v___x_5651_;
}
pub unsafe fn l_Lean_PersistentArray_anyM(
    mut v_00_u03b1_5652_: *mut leanh::LeanObject,
    mut v_m_5653_: *mut leanh::LeanObject,
    mut v_inst_5654_: *mut leanh::LeanObject,
    mut v_t_5655_: *mut leanh::LeanObject,
    mut v_p_5656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5657_ = l_Lean_PersistentArray_anyM___redArg(v_inst_5654_, v_t_5655_, v_p_5656_);
    return v___x_5657_;
}
pub unsafe fn l_Lean_PersistentArray_allM___redArg___lam__0(
    mut v_toPure_5658_: *mut leanh::LeanObject,
    mut v_b_5659_: u8,
) -> *mut leanh::LeanObject {
    if v_b_5659_ == 0 {
        let mut v___x_5660_: u8 = 0;
        let mut v___x_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5660_ = 1;
        v___x_5661_ = leanh::lean_box((v___x_5660_) as usize);
        v___x_5662_ =
            leanh::lean_apply_2(v_toPure_5658_, leanh::lean_box(0), v___x_5661_);
        return v___x_5662_;
    } else {
        let mut v___x_5663_: u8 = 0;
        let mut v___x_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5663_ = 0;
        v___x_5664_ = leanh::lean_box((v___x_5663_) as usize);
        v___x_5665_ =
            leanh::lean_apply_2(v_toPure_5658_, leanh::lean_box(0), v___x_5664_);
        return v___x_5665_;
    }
}
pub unsafe fn l_Lean_PersistentArray_allM___redArg___lam__0___boxed(
    mut v_toPure_5666_: *mut leanh::LeanObject,
    mut v_b_5667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_5668_: u8 = 0;
    let mut v_res_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_5668_ = (leanh::lean_unbox(v_b_5667_) as u8);
    v_res_5669_ = l_Lean_PersistentArray_allM___redArg___lam__0(v_toPure_5666_, v_b_boxed_5668_);
    return v_res_5669_;
}
pub unsafe fn l_Lean_PersistentArray_allM___redArg___lam__1(
    mut v_p_5670_: *mut leanh::LeanObject,
    mut v_toBind_5671_: *mut leanh::LeanObject,
    mut v___f_5672_: *mut leanh::LeanObject,
    mut v_v_5673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5674_ = leanh::lean_apply_1(v_p_5670_, v_v_5673_);
    v___x_5675_ = leanh::lean_apply_4(
        v_toBind_5671_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5674_,
        v___f_5672_,
    );
    return v___x_5675_;
}
pub unsafe fn l_Lean_PersistentArray_allM___redArg(
    mut v_inst_5676_: *mut leanh::LeanObject,
    mut v_a_5677_: *mut leanh::LeanObject,
    mut v_p_5678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5679_ = leanh::lean_ctor_get(v_inst_5676_, 0);
    v_toBind_5680_ = leanh::lean_ctor_get(v_inst_5676_, 1);
    leanh::lean_inc_n(v_toBind_5680_, 2);
    v_toPure_5681_ = leanh::lean_ctor_get(v_toApplicative_5679_, 1);
    leanh::lean_inc(v_toPure_5681_);
    v___f_5682_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_allM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5682_, 0, v_toPure_5681_);
    leanh::lean_inc_ref(v___f_5682_);
    v___f_5683_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_allM___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_5683_, 0, v_p_5678_);
    leanh::lean_closure_set(v___f_5683_, 1, v_toBind_5680_);
    leanh::lean_closure_set(v___f_5683_, 2, v___f_5682_);
    v___x_5684_ = l_Lean_PersistentArray_anyM___redArg(v_inst_5676_, v_a_5677_, v___f_5683_);
    v___x_5685_ = leanh::lean_apply_4(
        v_toBind_5680_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5684_,
        v___f_5682_,
    );
    return v___x_5685_;
}
pub unsafe fn l_Lean_PersistentArray_allM(
    mut v_00_u03b1_5686_: *mut leanh::LeanObject,
    mut v_m_5687_: *mut leanh::LeanObject,
    mut v_inst_5688_: *mut leanh::LeanObject,
    mut v_a_5689_: *mut leanh::LeanObject,
    mut v_p_5690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5691_ = leanh::lean_ctor_get(v_inst_5688_, 0);
    v_toBind_5692_ = leanh::lean_ctor_get(v_inst_5688_, 1);
    leanh::lean_inc_n(v_toBind_5692_, 2);
    v_toPure_5693_ = leanh::lean_ctor_get(v_toApplicative_5691_, 1);
    leanh::lean_inc(v_toPure_5693_);
    v___f_5694_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_allM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5694_, 0, v_toPure_5693_);
    leanh::lean_inc_ref(v___f_5694_);
    v___f_5695_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_allM___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_5695_, 0, v_p_5690_);
    leanh::lean_closure_set(v___f_5695_, 1, v_toBind_5692_);
    leanh::lean_closure_set(v___f_5695_, 2, v___f_5694_);
    v___x_5696_ = l_Lean_PersistentArray_anyM___redArg(v_inst_5688_, v_a_5689_, v___f_5695_);
    v___x_5697_ = leanh::lean_apply_4(
        v_toBind_5692_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5696_,
        v___f_5694_,
    );
    return v___x_5697_;
}
pub unsafe fn l_Lean_PersistentArray_any___redArg___lam__0(
    mut v_p_5698_: *mut leanh::LeanObject,
    mut v_x_5699_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: u8 = 0;
    v___x_5700_ = leanh::lean_apply_1(v_p_5698_, v_x_5699_);
    v___x_5701_ = (leanh::lean_unbox(v___x_5700_) as u8);
    return v___x_5701_;
}
pub unsafe fn l_Lean_PersistentArray_any___redArg___lam__0___boxed(
    mut v_p_5702_: *mut leanh::LeanObject,
    mut v_x_5703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5704_: u8 = 0;
    let mut v_r_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5704_ = l_Lean_PersistentArray_any___redArg___lam__0(v_p_5702_, v_x_5703_);
    v_r_5705_ = leanh::lean_box((v_res_5704_) as usize);
    return v_r_5705_;
}
pub unsafe fn l_Lean_PersistentArray_any___redArg(
    mut v_a_5706_: *mut leanh::LeanObject,
    mut v_p_5707_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: u8 = 0;
    v___f_5708_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5708_, 0, v_p_5707_);
    v___x_5709_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5710_ = l_Lean_PersistentArray_anyM___redArg(v___x_5709_, v_a_5706_, v___f_5708_);
    v___x_5711_ = (leanh::lean_unbox(v___x_5710_) as u8);
    leanh::lean_dec(v___x_5710_);
    return v___x_5711_;
}
pub unsafe fn l_Lean_PersistentArray_any___redArg___boxed(
    mut v_a_5712_: *mut leanh::LeanObject,
    mut v_p_5713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5714_: u8 = 0;
    let mut v_r_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5714_ = l_Lean_PersistentArray_any___redArg(v_a_5712_, v_p_5713_);
    v_r_5715_ = leanh::lean_box((v_res_5714_) as usize);
    return v_r_5715_;
}
pub unsafe fn l_Lean_PersistentArray_any(
    mut v_00_u03b1_5716_: *mut leanh::LeanObject,
    mut v_a_5717_: *mut leanh::LeanObject,
    mut v_p_5718_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: u8 = 0;
    v___f_5719_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5719_, 0, v_p_5718_);
    v___x_5720_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5721_ = l_Lean_PersistentArray_anyM___redArg(v___x_5720_, v_a_5717_, v___f_5719_);
    v___x_5722_ = (leanh::lean_unbox(v___x_5721_) as u8);
    leanh::lean_dec(v___x_5721_);
    return v___x_5722_;
}
pub unsafe fn l_Lean_PersistentArray_any___boxed(
    mut v_00_u03b1_5723_: *mut leanh::LeanObject,
    mut v_a_5724_: *mut leanh::LeanObject,
    mut v_p_5725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5726_: u8 = 0;
    let mut v_r_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5726_ = l_Lean_PersistentArray_any(v_00_u03b1_5723_, v_a_5724_, v_p_5725_);
    v_r_5727_ = leanh::lean_box((v_res_5726_) as usize);
    return v_r_5727_;
}
pub unsafe fn l_Lean_PersistentArray_all___redArg___lam__0(
    mut v_p_5728_: *mut leanh::LeanObject,
    mut v_x_5729_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: u8 = 0;
    v___x_5730_ = leanh::lean_apply_1(v_p_5728_, v_x_5729_);
    v___x_5731_ = (leanh::lean_unbox(v___x_5730_) as u8);
    if v___x_5731_ == 0 {
        let mut v___x_5732_: u8 = 0;
        v___x_5732_ = 1;
        return v___x_5732_;
    } else {
        let mut v___x_5733_: u8 = 0;
        v___x_5733_ = 0;
        return v___x_5733_;
    }
}
pub unsafe fn l_Lean_PersistentArray_all___redArg___lam__0___boxed(
    mut v_p_5734_: *mut leanh::LeanObject,
    mut v_x_5735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5736_: u8 = 0;
    let mut v_r_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5736_ = l_Lean_PersistentArray_all___redArg___lam__0(v_p_5734_, v_x_5735_);
    v_r_5737_ = leanh::lean_box((v_res_5736_) as usize);
    return v_r_5737_;
}
pub unsafe fn l_Lean_PersistentArray_all___redArg(
    mut v_a_5738_: *mut leanh::LeanObject,
    mut v_p_5739_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: u8 = 0;
    v___f_5740_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5740_, 0, v_p_5739_);
    v___x_5741_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5742_ = l_Lean_PersistentArray_anyM___redArg(v___x_5741_, v_a_5738_, v___f_5740_);
    v___x_5743_ = (leanh::lean_unbox(v___x_5742_) as u8);
    leanh::lean_dec(v___x_5742_);
    if v___x_5743_ == 0 {
        let mut v___x_5744_: u8 = 0;
        v___x_5744_ = 1;
        return v___x_5744_;
    } else {
        let mut v___x_5745_: u8 = 0;
        v___x_5745_ = 0;
        return v___x_5745_;
    }
}
pub unsafe fn l_Lean_PersistentArray_all___redArg___boxed(
    mut v_a_5746_: *mut leanh::LeanObject,
    mut v_p_5747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5748_: u8 = 0;
    let mut v_r_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5748_ = l_Lean_PersistentArray_all___redArg(v_a_5746_, v_p_5747_);
    v_r_5749_ = leanh::lean_box((v_res_5748_) as usize);
    return v_r_5749_;
}
pub unsafe fn l_Lean_PersistentArray_all(
    mut v_00_u03b1_5750_: *mut leanh::LeanObject,
    mut v_a_5751_: *mut leanh::LeanObject,
    mut v_p_5752_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: u8 = 0;
    v___f_5753_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5753_, 0, v_p_5752_);
    v___x_5754_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5755_ = l_Lean_PersistentArray_anyM___redArg(v___x_5754_, v_a_5751_, v___f_5753_);
    v___x_5756_ = (leanh::lean_unbox(v___x_5755_) as u8);
    leanh::lean_dec(v___x_5755_);
    if v___x_5756_ == 0 {
        let mut v___x_5757_: u8 = 0;
        v___x_5757_ = 1;
        return v___x_5757_;
    } else {
        let mut v___x_5758_: u8 = 0;
        v___x_5758_ = 0;
        return v___x_5758_;
    }
}
pub unsafe fn l_Lean_PersistentArray_all___boxed(
    mut v_00_u03b1_5759_: *mut leanh::LeanObject,
    mut v_a_5760_: *mut leanh::LeanObject,
    mut v_p_5761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5762_: u8 = 0;
    let mut v_r_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5762_ = l_Lean_PersistentArray_all(v_00_u03b1_5759_, v_a_5760_, v_p_5761_);
    v_r_5763_ = leanh::lean_box((v_res_5762_) as usize);
    return v_r_5763_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___redArg___lam__0(
    mut v_cs_5764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5765_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5765_, 0, v_cs_5764_);
    return v___x_5765_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___redArg___lam__2(
    mut v_vs_5766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5767_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5767_, 0, v_vs_5766_);
    return v___x_5767_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___redArg(
    mut v_inst_5770_: *mut leanh::LeanObject,
    mut v_f_5771_: *mut leanh::LeanObject,
    mut v_x_5772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5772_) == 0 {
        let mut v_toApplicative_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toFunctor_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_cs_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_5779_: usize = 0;
        let mut v___x_5780_: usize = 0;
        let mut v___x_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_5773_ = leanh::lean_ctor_get(v_inst_5770_, 0);
        v_toFunctor_5774_ = leanh::lean_ctor_get(v_toApplicative_5773_, 0);
        v_cs_5775_ = leanh::lean_ctor_get(v_x_5772_, 0);
        leanh::lean_inc_ref(v_cs_5775_);
        leanh::lean_dec_ref_known(v_x_5772_, 1);
        v_map_5776_ = leanh::lean_ctor_get(v_toFunctor_5774_, 0);
        leanh::lean_inc(v_map_5776_);
        v___f_5777_ = l_Lean_PersistentArray_mapMAux___redArg___closed__0;
        leanh::lean_inc_ref(v_inst_5770_);
        v___f_5778_ = leanh::lean_alloc_closure(
            l_Lean_PersistentArray_mapMAux___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_5778_, 0, v_inst_5770_);
        leanh::lean_closure_set(v___f_5778_, 1, v_f_5771_);
        v_sz_5779_ = lean_array_size(v_cs_5775_);
        v___x_5780_ = 0usize;
        v___x_5781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_5770_,
            v___f_5778_,
            v_sz_5779_,
            v___x_5780_,
            v_cs_5775_,
        );
        v___x_5782_ = leanh::lean_apply_4(
            v_map_5776_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_5777_,
            v___x_5781_,
        );
        return v___x_5782_;
    } else {
        let mut v_toApplicative_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toFunctor_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_5788_: usize = 0;
        let mut v___x_5789_: usize = 0;
        let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_5783_ = leanh::lean_ctor_get(v_inst_5770_, 0);
        v_toFunctor_5784_ = leanh::lean_ctor_get(v_toApplicative_5783_, 0);
        v_vs_5785_ = leanh::lean_ctor_get(v_x_5772_, 0);
        leanh::lean_inc_ref(v_vs_5785_);
        leanh::lean_dec_ref_known(v_x_5772_, 1);
        v_map_5786_ = leanh::lean_ctor_get(v_toFunctor_5784_, 0);
        leanh::lean_inc(v_map_5786_);
        v___f_5787_ = l_Lean_PersistentArray_mapMAux___redArg___closed__1;
        v_sz_5788_ = lean_array_size(v_vs_5785_);
        v___x_5789_ = 0usize;
        v___x_5790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_5770_,
            v_f_5771_,
            v_sz_5788_,
            v___x_5789_,
            v_vs_5785_,
        );
        v___x_5791_ = leanh::lean_apply_4(
            v_map_5786_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_5787_,
            v___x_5790_,
        );
        return v___x_5791_;
    }
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___redArg___lam__1(
    mut v_inst_5792_: *mut leanh::LeanObject,
    mut v_f_5793_: *mut leanh::LeanObject,
    mut v_c_5794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5795_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_5792_, v_f_5793_, v_c_5794_);
    return v___x_5795_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux(
    mut v_00_u03b1_5796_: *mut leanh::LeanObject,
    mut v_m_5797_: *mut leanh::LeanObject,
    mut v_inst_5798_: *mut leanh::LeanObject,
    mut v_00_u03b2_5799_: *mut leanh::LeanObject,
    mut v_f_5800_: *mut leanh::LeanObject,
    mut v_x_5801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5802_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_5798_, v_f_5800_, v_x_5801_);
    return v___x_5802_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___redArg___lam__0(
    mut v_root_5803_: *mut leanh::LeanObject,
    mut v_size_5804_: *mut leanh::LeanObject,
    mut v_shift_5805_: usize,
    mut v_tailOff_5806_: *mut leanh::LeanObject,
    mut v_toPure_5807_: *mut leanh::LeanObject,
    mut v_tail_5808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5809_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_5809_, 0, v_root_5803_);
    leanh::lean_ctor_set(v___x_5809_, 1, v_tail_5808_);
    leanh::lean_ctor_set(v___x_5809_, 2, v_size_5804_);
    leanh::lean_ctor_set(v___x_5809_, 3, v_tailOff_5806_);
    leanh::lean_ctor_set_usize(v___x_5809_, 4, v_shift_5805_);
    v___x_5810_ =
        leanh::lean_apply_2(v_toPure_5807_, leanh::lean_box(0), v___x_5809_);
    return v___x_5810_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___redArg___lam__0___boxed(
    mut v_root_5811_: *mut leanh::LeanObject,
    mut v_size_5812_: *mut leanh::LeanObject,
    mut v_shift_5813_: *mut leanh::LeanObject,
    mut v_tailOff_5814_: *mut leanh::LeanObject,
    mut v_toPure_5815_: *mut leanh::LeanObject,
    mut v_tail_5816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_shift_boxed_5817_: usize = 0;
    let mut v_res_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_shift_boxed_5817_ = leanh::lean_unbox_usize(v_shift_5813_);
    leanh::lean_dec(v_shift_5813_);
    v_res_5818_ = l_Lean_PersistentArray_mapM___redArg___lam__0(
        v_root_5811_,
        v_size_5812_,
        v_shift_boxed_5817_,
        v_tailOff_5814_,
        v_toPure_5815_,
        v_tail_5816_,
    );
    return v_res_5818_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___redArg___lam__1(
    mut v_size_5819_: *mut leanh::LeanObject,
    mut v_shift_5820_: usize,
    mut v_tailOff_5821_: *mut leanh::LeanObject,
    mut v_toPure_5822_: *mut leanh::LeanObject,
    mut v_tail_5823_: *mut leanh::LeanObject,
    mut v_inst_5824_: *mut leanh::LeanObject,
    mut v_f_5825_: *mut leanh::LeanObject,
    mut v_toBind_5826_: *mut leanh::LeanObject,
    mut v_root_5827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5830_: usize = 0;
    let mut v___x_5831_: usize = 0;
    let mut v___x_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5828_ = leanh::lean_box_usize(v_shift_5820_);
    v___f_5829_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_mapM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_5829_, 0, v_root_5827_);
    leanh::lean_closure_set(v___f_5829_, 1, v_size_5819_);
    leanh::lean_closure_set(v___f_5829_, 2, v___x_5828_);
    leanh::lean_closure_set(v___f_5829_, 3, v_tailOff_5821_);
    leanh::lean_closure_set(v___f_5829_, 4, v_toPure_5822_);
    v_sz_5830_ = lean_array_size(v_tail_5823_);
    v___x_5831_ = 0usize;
    v___x_5832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_5824_,
        v_f_5825_,
        v_sz_5830_,
        v___x_5831_,
        v_tail_5823_,
    );
    v___x_5833_ = leanh::lean_apply_4(
        v_toBind_5826_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5832_,
        v___f_5829_,
    );
    return v___x_5833_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___redArg___lam__1___boxed(
    mut v_size_5834_: *mut leanh::LeanObject,
    mut v_shift_5835_: *mut leanh::LeanObject,
    mut v_tailOff_5836_: *mut leanh::LeanObject,
    mut v_toPure_5837_: *mut leanh::LeanObject,
    mut v_tail_5838_: *mut leanh::LeanObject,
    mut v_inst_5839_: *mut leanh::LeanObject,
    mut v_f_5840_: *mut leanh::LeanObject,
    mut v_toBind_5841_: *mut leanh::LeanObject,
    mut v_root_5842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_shift_boxed_5843_: usize = 0;
    let mut v_res_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_shift_boxed_5843_ = leanh::lean_unbox_usize(v_shift_5835_);
    leanh::lean_dec(v_shift_5835_);
    v_res_5844_ = l_Lean_PersistentArray_mapM___redArg___lam__1(
        v_size_5834_,
        v_shift_boxed_5843_,
        v_tailOff_5836_,
        v_toPure_5837_,
        v_tail_5838_,
        v_inst_5839_,
        v_f_5840_,
        v_toBind_5841_,
        v_root_5842_,
    );
    return v_res_5844_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___redArg(
    mut v_inst_5845_: *mut leanh::LeanObject,
    mut v_f_5846_: *mut leanh::LeanObject,
    mut v_t_5847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_5853_: usize = 0;
    let mut v_tailOff_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5848_ = leanh::lean_ctor_get(v_inst_5845_, 0);
    v_toBind_5849_ = leanh::lean_ctor_get(v_inst_5845_, 1);
    leanh::lean_inc_n(v_toBind_5849_, 2);
    v_root_5850_ = leanh::lean_ctor_get(v_t_5847_, 0);
    leanh::lean_inc_ref(v_root_5850_);
    v_tail_5851_ = leanh::lean_ctor_get(v_t_5847_, 1);
    leanh::lean_inc_ref(v_tail_5851_);
    v_size_5852_ = leanh::lean_ctor_get(v_t_5847_, 2);
    leanh::lean_inc(v_size_5852_);
    v_shift_5853_ = leanh::lean_ctor_get_usize(v_t_5847_, 4);
    v_tailOff_5854_ = leanh::lean_ctor_get(v_t_5847_, 3);
    leanh::lean_inc(v_tailOff_5854_);
    leanh::lean_dec_ref(v_t_5847_);
    v_toPure_5855_ = leanh::lean_ctor_get(v_toApplicative_5848_, 1);
    leanh::lean_inc(v_toPure_5855_);
    leanh::lean_inc(v_f_5846_);
    leanh::lean_inc_ref(v_inst_5845_);
    v___x_5856_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_5845_, v_f_5846_, v_root_5850_);
    v___x_5857_ = leanh::lean_box_usize(v_shift_5853_);
    v___f_5858_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_mapM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_5858_, 0, v_size_5852_);
    leanh::lean_closure_set(v___f_5858_, 1, v___x_5857_);
    leanh::lean_closure_set(v___f_5858_, 2, v_tailOff_5854_);
    leanh::lean_closure_set(v___f_5858_, 3, v_toPure_5855_);
    leanh::lean_closure_set(v___f_5858_, 4, v_tail_5851_);
    leanh::lean_closure_set(v___f_5858_, 5, v_inst_5845_);
    leanh::lean_closure_set(v___f_5858_, 6, v_f_5846_);
    leanh::lean_closure_set(v___f_5858_, 7, v_toBind_5849_);
    v___x_5859_ = leanh::lean_apply_4(
        v_toBind_5849_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5856_,
        v___f_5858_,
    );
    return v___x_5859_;
}
pub unsafe fn l_Lean_PersistentArray_mapM(
    mut v_00_u03b1_5860_: *mut leanh::LeanObject,
    mut v_m_5861_: *mut leanh::LeanObject,
    mut v_inst_5862_: *mut leanh::LeanObject,
    mut v_00_u03b2_5863_: *mut leanh::LeanObject,
    mut v_f_5864_: *mut leanh::LeanObject,
    mut v_t_5865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5866_ = l_Lean_PersistentArray_mapM___redArg(v_inst_5862_, v_f_5864_, v_t_5865_);
    return v___x_5866_;
}
pub unsafe fn l_Lean_PersistentArray_map___redArg___lam__0(
    mut v_f_5867_: *mut leanh::LeanObject,
    mut v_x_5868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5869_ = leanh::lean_apply_1(v_f_5867_, v_x_5868_);
    return v___x_5869_;
}
pub unsafe fn l_Lean_PersistentArray_map___redArg(
    mut v_f_5870_: *mut leanh::LeanObject,
    mut v_t_5871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5872_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5872_, 0, v_f_5870_);
    v___x_5873_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5874_ = l_Lean_PersistentArray_mapM___redArg(v___x_5873_, v___f_5872_, v_t_5871_);
    return v___x_5874_;
}
pub unsafe fn l_Lean_PersistentArray_map(
    mut v_00_u03b1_5875_: *mut leanh::LeanObject,
    mut v_00_u03b2_5876_: *mut leanh::LeanObject,
    mut v_f_5877_: *mut leanh::LeanObject,
    mut v_t_5878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5879_ = leanh::lean_alloc_closure(
        l_Lean_PersistentArray_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5879_, 0, v_f_5877_);
    v___x_5880_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5881_ = l_Lean_PersistentArray_mapM___redArg(v___x_5880_, v___f_5879_, v_t_5878_);
    return v___x_5881_;
}
pub unsafe fn l_Lean_PersistentArray_collectStats___redArg(
    mut v_x_5882_: *mut leanh::LeanObject,
    mut v_x_5883_: *mut leanh::LeanObject,
    mut v_x_5884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNodes_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tailSize_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5891_: u8 = 0;
    let mut v___x_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: u8 = 0;
    let mut v___x_5901_: u8 = 0;
    let mut v___x_5902_: usize = 0;
    let mut v___x_5903_: usize = 0;
    let mut v___x_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: usize = 0;
    let mut v___x_5906_: usize = 0;
    let mut v___x_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: u8 = 0;
    let mut v_isSharedCheck_5910_: u8 = 0;
    let mut v_numNodes_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tailSize_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v___x_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: u8 = 0;
    let mut v___x_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5882_) == 0 {
                    v_cs_5885_ = leanh::lean_ctor_get(v_x_5882_, 0);
                    v_numNodes_5886_ = leanh::lean_ctor_get(v_x_5883_, 0);
                    v_depth_5887_ = leanh::lean_ctor_get(v_x_5883_, 1);
                    v_tailSize_5888_ = leanh::lean_ctor_get(v_x_5883_, 2);
                    v_isSharedCheck_5910_ = (!leanh::lean_is_exclusive(v_x_5883_)) as u8;
                    if v_isSharedCheck_5910_ == 0 {
                        v___x_5890_ = v_x_5883_;
                        v_isShared_5891_ = v_isSharedCheck_5910_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tailSize_5888_);
                        leanh::lean_inc(v_depth_5887_);
                        leanh::lean_inc(v_numNodes_5886_);
                        leanh::lean_dec(v_x_5883_);
                        v___x_5890_ = leanh::lean_box(0);
                        v_isShared_5891_ = v_isSharedCheck_5910_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_numNodes_5911_ = leanh::lean_ctor_get(v_x_5883_, 0);
                    v_depth_5912_ = leanh::lean_ctor_get(v_x_5883_, 1);
                    v_tailSize_5913_ = leanh::lean_ctor_get(v_x_5883_, 2);
                    v_isSharedCheck_5926_ = (!leanh::lean_is_exclusive(v_x_5883_)) as u8;
                    if v_isSharedCheck_5926_ == 0 {
                        v___x_5915_ = v_x_5883_;
                        v_isShared_5916_ = v_isSharedCheck_5926_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_tailSize_5913_);
                        leanh::lean_inc(v_depth_5912_);
                        leanh::lean_inc(v_numNodes_5911_);
                        leanh::lean_dec(v_x_5883_);
                        v___x_5915_ = leanh::lean_box(0);
                        v_isShared_5916_ = v_isSharedCheck_5926_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5892_ = leanh::lean_unsigned_to_nat(1);
                v___x_5893_ = lean_nat_add(v_numNodes_5886_, v___x_5892_);
                leanh::lean_dec(v_numNodes_5886_);
                v___x_5909_ = lean_nat_dec_le(v_x_5884_, v_depth_5887_);
                if v___x_5909_ == 0 {
                    leanh::lean_dec(v_depth_5887_);
                    leanh::lean_inc(v_x_5884_);
                    v___y_5895_ = v_x_5884_;
                    state = 2;
                    continue;
                } else {
                    v___y_5895_ = v_depth_5887_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5891_ == 0 {
                    leanh::lean_ctor_set(v___x_5890_, 1, v___y_5895_);
                    leanh::lean_ctor_set(v___x_5890_, 0, v___x_5893_);
                    v___x_5897_ = v___x_5890_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5908_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5908_, 0, v___x_5893_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5908_, 1, v___y_5895_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5908_, 2, v_tailSize_5888_);
                    v___x_5897_ = v_reuseFailAlloc_5908_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5898_ = leanh::lean_unsigned_to_nat(0);
                v___x_5899_ = lean_array_get_size(v_cs_5885_);
                v___x_5900_ = lean_nat_dec_lt(v___x_5898_, v___x_5899_);
                if v___x_5900_ == 0 {
                    leanh::lean_dec(v_x_5884_);
                    return v___x_5897_;
                } else {
                    v___x_5901_ = lean_nat_dec_le(v___x_5899_, v___x_5899_);
                    if v___x_5901_ == 0 {
                        if v___x_5900_ == 0 {
                            leanh::lean_dec(v_x_5884_);
                            return v___x_5897_;
                        } else {
                            v___x_5902_ = 0usize;
                            v___x_5903_ = lean_usize_of_nat(v___x_5899_);
                            v___x_5904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_5884_, v_cs_5885_, v___x_5902_, v___x_5903_, v___x_5897_);
                            leanh::lean_dec(v_x_5884_);
                            return v___x_5904_;
                        }
                    } else {
                        v___x_5905_ = 0usize;
                        v___x_5906_ = lean_usize_of_nat(v___x_5899_);
                        v___x_5907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_5884_, v_cs_5885_, v___x_5905_, v___x_5906_, v___x_5897_);
                        leanh::lean_dec(v_x_5884_);
                        return v___x_5907_;
                    }
                }
            }
            4 => {
                v___x_5917_ = leanh::lean_unsigned_to_nat(1);
                v___x_5918_ = lean_nat_add(v_numNodes_5911_, v___x_5917_);
                leanh::lean_dec(v_numNodes_5911_);
                v___x_5919_ = lean_nat_dec_le(v_x_5884_, v_depth_5912_);
                if v___x_5919_ == 0 {
                    leanh::lean_dec(v_depth_5912_);
                    if v_isShared_5916_ == 0 {
                        leanh::lean_ctor_set(v___x_5915_, 1, v_x_5884_);
                        leanh::lean_ctor_set(v___x_5915_, 0, v___x_5918_);
                        v___x_5921_ = v___x_5915_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5922_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5922_, 0, v___x_5918_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5922_, 1, v_x_5884_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5922_, 2, v_tailSize_5913_);
                        v___x_5921_ = v_reuseFailAlloc_5922_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_x_5884_);
                    if v_isShared_5916_ == 0 {
                        leanh::lean_ctor_set(v___x_5915_, 0, v___x_5918_);
                        v___x_5924_ = v___x_5915_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5925_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5925_, 0, v___x_5918_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5925_, 1, v_depth_5912_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5925_, 2, v_tailSize_5913_);
                        v___x_5924_ = v_reuseFailAlloc_5925_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_5921_;
            }
            6 => {
                return v___x_5924_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(
    mut v_x_5927_: *mut leanh::LeanObject,
    mut v_as_5928_: *mut leanh::LeanObject,
    mut v_i_5929_: usize,
    mut v_stop_5930_: usize,
    mut v_b_5931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5932_: u8 = 0;
    let mut v___x_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: usize = 0;
    let mut v___x_5938_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5932_ = lean_usize_dec_eq(v_i_5929_, v_stop_5930_);
                if v___x_5932_ == 0 {
                    v___x_5933_ = lean_array_uget_borrowed(v_as_5928_, v_i_5929_);
                    v___x_5934_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5935_ = lean_nat_add(v_x_5927_, v___x_5934_);
                    v___x_5936_ = l_Lean_PersistentArray_collectStats___redArg(
                        v___x_5933_,
                        v_b_5931_,
                        v___x_5935_,
                    );
                    v___x_5937_ = 1usize;
                    v___x_5938_ = lean_usize_add(v_i_5929_, v___x_5937_);
                    v_i_5929_ = v___x_5938_;
                    v_b_5931_ = v___x_5936_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5931_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg___boxed(
    mut v_x_5940_: *mut leanh::LeanObject,
    mut v_as_5941_: *mut leanh::LeanObject,
    mut v_i_5942_: *mut leanh::LeanObject,
    mut v_stop_5943_: *mut leanh::LeanObject,
    mut v_b_5944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5945_: usize = 0;
    let mut v_stop_boxed_5946_: usize = 0;
    let mut v_res_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5945_ = leanh::lean_unbox_usize(v_i_5942_);
    leanh::lean_dec(v_i_5942_);
    v_stop_boxed_5946_ = leanh::lean_unbox_usize(v_stop_5943_);
    leanh::lean_dec(v_stop_5943_);
    v_res_5947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_5940_, v_as_5941_, v_i_boxed_5945_, v_stop_boxed_5946_, v_b_5944_);
    leanh::lean_dec_ref(v_as_5941_);
    leanh::lean_dec(v_x_5940_);
    return v_res_5947_;
}
pub unsafe fn l_Lean_PersistentArray_collectStats___redArg___boxed(
    mut v_x_5948_: *mut leanh::LeanObject,
    mut v_x_5949_: *mut leanh::LeanObject,
    mut v_x_5950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5951_ = l_Lean_PersistentArray_collectStats___redArg(v_x_5948_, v_x_5949_, v_x_5950_);
    leanh::lean_dec_ref(v_x_5948_);
    return v_res_5951_;
}
pub unsafe fn l_Lean_PersistentArray_collectStats(
    mut v_00_u03b1_5952_: *mut leanh::LeanObject,
    mut v_x_5953_: *mut leanh::LeanObject,
    mut v_x_5954_: *mut leanh::LeanObject,
    mut v_x_5955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5956_ = l_Lean_PersistentArray_collectStats___redArg(v_x_5953_, v_x_5954_, v_x_5955_);
    return v___x_5956_;
}
pub unsafe fn l_Lean_PersistentArray_collectStats___boxed(
    mut v_00_u03b1_5957_: *mut leanh::LeanObject,
    mut v_x_5958_: *mut leanh::LeanObject,
    mut v_x_5959_: *mut leanh::LeanObject,
    mut v_x_5960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5961_ =
        l_Lean_PersistentArray_collectStats(v_00_u03b1_5957_, v_x_5958_, v_x_5959_, v_x_5960_);
    leanh::lean_dec_ref(v_x_5958_);
    return v_res_5961_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(
    mut v_00_u03b1_5962_: *mut leanh::LeanObject,
    mut v_x_5963_: *mut leanh::LeanObject,
    mut v_as_5964_: *mut leanh::LeanObject,
    mut v_i_5965_: usize,
    mut v_stop_5966_: usize,
    mut v_b_5967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_5963_, v_as_5964_, v_i_5965_, v_stop_5966_, v_b_5967_);
    return v___x_5968_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___boxed(
    mut v_00_u03b1_5969_: *mut leanh::LeanObject,
    mut v_x_5970_: *mut leanh::LeanObject,
    mut v_as_5971_: *mut leanh::LeanObject,
    mut v_i_5972_: *mut leanh::LeanObject,
    mut v_stop_5973_: *mut leanh::LeanObject,
    mut v_b_5974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5975_: usize = 0;
    let mut v_stop_boxed_5976_: usize = 0;
    let mut v_res_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5975_ = leanh::lean_unbox_usize(v_i_5972_);
    leanh::lean_dec(v_i_5972_);
    v_stop_boxed_5976_ = leanh::lean_unbox_usize(v_stop_5973_);
    leanh::lean_dec(v_stop_5973_);
    v_res_5977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(v_00_u03b1_5969_, v_x_5970_, v_as_5971_, v_i_boxed_5975_, v_stop_boxed_5976_, v_b_5974_);
    leanh::lean_dec_ref(v_as_5971_);
    leanh::lean_dec(v_x_5970_);
    return v_res_5977_;
}
pub unsafe fn l_Lean_PersistentArray_stats___redArg(
    mut v_r_5978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_root_5979_ = leanh::lean_ctor_get(v_r_5978_, 0);
    v_tail_5980_ = leanh::lean_ctor_get(v_r_5978_, 1);
    v___x_5981_ = leanh::lean_unsigned_to_nat(0);
    v___x_5982_ = lean_array_get_size(v_tail_5980_);
    v___x_5983_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_5983_, 0, v___x_5981_);
    leanh::lean_ctor_set(v___x_5983_, 1, v___x_5981_);
    leanh::lean_ctor_set(v___x_5983_, 2, v___x_5982_);
    v___x_5984_ =
        l_Lean_PersistentArray_collectStats___redArg(v_root_5979_, v___x_5983_, v___x_5981_);
    return v___x_5984_;
}
pub unsafe fn l_Lean_PersistentArray_stats___redArg___boxed(
    mut v_r_5985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5986_ = l_Lean_PersistentArray_stats___redArg(v_r_5985_);
    leanh::lean_dec_ref(v_r_5985_);
    return v_res_5986_;
}
pub unsafe fn l_Lean_PersistentArray_stats(
    mut v_00_u03b1_5987_: *mut leanh::LeanObject,
    mut v_r_5988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5989_ = l_Lean_PersistentArray_stats___redArg(v_r_5988_);
    return v___x_5989_;
}
pub unsafe fn l_Lean_PersistentArray_stats___boxed(
    mut v_00_u03b1_5990_: *mut leanh::LeanObject,
    mut v_r_5991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5992_ = l_Lean_PersistentArray_stats(v_00_u03b1_5990_, v_r_5991_);
    leanh::lean_dec_ref(v_r_5991_);
    return v_res_5992_;
}
pub unsafe fn l_Lean_PersistentArray_Stats_toString(
    mut v_s_5997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numNodes_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tailSize_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_numNodes_5998_ = leanh::lean_ctor_get(v_s_5997_, 0);
    leanh::lean_inc(v_numNodes_5998_);
    v_depth_5999_ = leanh::lean_ctor_get(v_s_5997_, 1);
    leanh::lean_inc(v_depth_5999_);
    v_tailSize_6000_ = leanh::lean_ctor_get(v_s_5997_, 2);
    leanh::lean_inc(v_tailSize_6000_);
    leanh::lean_dec_ref(v_s_5997_);
    v___x_6001_ = l_Lean_PersistentArray_Stats_toString___closed__0;
    v___x_6002_ = l_Nat_reprFast(v_numNodes_5998_);
    v___x_6003_ = lean_string_append(v___x_6001_, v___x_6002_);
    leanh::lean_dec_ref(v___x_6002_);
    v___x_6004_ = l_Lean_PersistentArray_Stats_toString___closed__1;
    v___x_6005_ = lean_string_append(v___x_6003_, v___x_6004_);
    v___x_6006_ = l_Nat_reprFast(v_depth_5999_);
    v___x_6007_ = lean_string_append(v___x_6005_, v___x_6006_);
    leanh::lean_dec_ref(v___x_6006_);
    v___x_6008_ = l_Lean_PersistentArray_Stats_toString___closed__2;
    v___x_6009_ = lean_string_append(v___x_6007_, v___x_6008_);
    v___x_6010_ = l_Nat_reprFast(v_tailSize_6000_);
    v___x_6011_ = lean_string_append(v___x_6009_, v___x_6010_);
    leanh::lean_dec_ref(v___x_6010_);
    v___x_6012_ = l_Lean_PersistentArray_Stats_toString___closed__3;
    v___x_6013_ = lean_string_append(v___x_6011_, v___x_6012_);
    return v___x_6013_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(
    mut v_v_6016_: *mut leanh::LeanObject,
    mut v_j_6017_: *mut leanh::LeanObject,
    mut v_a_6018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6020_: u8 = 0;
    let mut v_one_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6019_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_6020_ = lean_nat_dec_eq(v_j_6017_, v_zero_6019_);
                if v_isZero_6020_ == 1 {
                    leanh::lean_dec(v_j_6017_);
                    leanh::lean_dec(v_v_6016_);
                    return v_a_6018_;
                } else {
                    v_one_6021_ = leanh::lean_unsigned_to_nat(1);
                    v_n_6022_ = lean_nat_sub(v_j_6017_, v_one_6021_);
                    leanh::lean_dec(v_j_6017_);
                    leanh::lean_inc(v_v_6016_);
                    v___x_6023_ = l_Lean_PersistentArray_push___redArg(v_a_6018_, v_v_6016_);
                    v_j_6017_ = v_n_6022_;
                    v_a_6018_ = v___x_6023_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_mkPersistentArray___redArg___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6025_ = l_Lean_PersistentArray_empty(leanh::lean_box(0));
    return v___x_6025_;
}
pub unsafe fn l_Lean_mkPersistentArray___redArg(
    mut v_n_6026_: *mut leanh::LeanObject,
    mut v_v_6027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6028_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkPersistentArray___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_mkPersistentArray___redArg___closed__0_once),
        _init_l_Lean_mkPersistentArray___redArg___closed__0,
    );
    v___x_6029_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_6027_, v_n_6026_, v___x_6028_);
    return v___x_6029_;
}
pub unsafe fn l_Lean_mkPersistentArray(
    mut v_00_u03b1_6030_: *mut leanh::LeanObject,
    mut v_n_6031_: *mut leanh::LeanObject,
    mut v_v_6032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6033_ = l_Lean_mkPersistentArray___redArg(v_n_6031_, v_v_6032_);
    return v___x_6033_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(
    mut v_00_u03b1_6034_: *mut leanh::LeanObject,
    mut v_v_6035_: *mut leanh::LeanObject,
    mut v_n_6036_: *mut leanh::LeanObject,
    mut v_j_6037_: *mut leanh::LeanObject,
    mut v_a_6038_: *mut leanh::LeanObject,
    mut v_a_6039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6040_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_6035_, v_j_6037_, v_a_6039_);
    return v___x_6040_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___boxed(
    mut v_00_u03b1_6041_: *mut leanh::LeanObject,
    mut v_v_6042_: *mut leanh::LeanObject,
    mut v_n_6043_: *mut leanh::LeanObject,
    mut v_j_6044_: *mut leanh::LeanObject,
    mut v_a_6045_: *mut leanh::LeanObject,
    mut v_a_6046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6047_ =
        l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(
            v_00_u03b1_6041_,
            v_v_6042_,
            v_n_6043_,
            v_j_6044_,
            v_a_6045_,
            v_a_6046_,
        );
    leanh::lean_dec(v_n_6043_);
    return v_res_6047_;
}
pub unsafe fn l_Lean_mkPArray___redArg(
    mut v_n_6048_: *mut leanh::LeanObject,
    mut v_v_6049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6050_ = l_Lean_mkPersistentArray___redArg(v_n_6048_, v_v_6049_);
    return v___x_6050_;
}
pub unsafe fn l_Lean_mkPArray(
    mut v_00_u03b1_6051_: *mut leanh::LeanObject,
    mut v_n_6052_: *mut leanh::LeanObject,
    mut v_v_6053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6054_ = l_Lean_mkPersistentArray___redArg(v_n_6052_, v_v_6053_);
    return v___x_6054_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(
    mut v_a_6055_: *mut leanh::LeanObject,
    mut v_a_6056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_6057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_6055_) == 0 {
                    return v_a_6056_;
                } else {
                    v_head_6057_ = leanh::lean_ctor_get(v_a_6055_, 0);
                    leanh::lean_inc(v_head_6057_);
                    v_tail_6058_ = leanh::lean_ctor_get(v_a_6055_, 1);
                    leanh::lean_inc(v_tail_6058_);
                    leanh::lean_dec_ref_known(v_a_6055_, 2);
                    v___x_6059_ = l_Lean_PersistentArray_push___redArg(v_a_6056_, v_head_6057_);
                    v_a_6055_ = v_tail_6058_;
                    v_a_6056_ = v___x_6059_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop(
    mut v_00_u03b1_6061_: *mut leanh::LeanObject,
    mut v_a_6062_: *mut leanh::LeanObject,
    mut v_a_6063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6064_ = l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(
        v_a_6062_, v_a_6063_,
    );
    return v___x_6064_;
}
pub unsafe fn l_List_toPArray_x27___redArg(
    mut v_xs_6065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6066_ = leanh::lean_unsigned_to_nat(32);
    v___x_6067_ = lean_mk_empty_array_with_capacity(v___x_6066_);
    leanh::lean_dec_ref(v___x_6067_);
    v___x_6068_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__1_once),
        _init_l_Lean_instInhabitedPersistentArray_default___closed__1,
    );
    v___x_6069_ = l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(
        v_xs_6065_,
        v___x_6068_,
    );
    return v___x_6069_;
}
pub unsafe fn l_List_toPArray_x27(
    mut v_00_u03b1_6070_: *mut leanh::LeanObject,
    mut v_xs_6071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6072_ = l_List_toPArray_x27___redArg(v_xs_6071_);
    return v___x_6072_;
}
pub unsafe fn l_Array_toPArray_x27___redArg(
    mut v_xs_6073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: u8 = 0;
    v___x_6074_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkPersistentArray___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_mkPersistentArray___redArg___closed__0_once),
        _init_l_Lean_mkPersistentArray___redArg___closed__0,
    );
    v___x_6075_ = leanh::lean_unsigned_to_nat(0);
    v___x_6076_ = lean_array_get_size(v_xs_6073_);
    v___x_6077_ = lean_nat_dec_lt(v___x_6075_, v___x_6076_);
    if v___x_6077_ == 0 {
        return v___x_6074_;
    } else {
        let mut v___x_6078_: u8 = 0;
        v___x_6078_ = lean_nat_dec_le(v___x_6076_, v___x_6076_);
        if v___x_6078_ == 0 {
            if v___x_6077_ == 0 {
                return v___x_6074_;
            } else {
                let mut v___x_6079_: usize = 0;
                let mut v___x_6080_: usize = 0;
                let mut v___x_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6079_ = 0usize;
                v___x_6080_ = lean_usize_of_nat(v___x_6076_);
                v___x_6081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_6073_, v___x_6079_, v___x_6080_, v___x_6074_);
                return v___x_6081_;
            }
        } else {
            let mut v___x_6082_: usize = 0;
            let mut v___x_6083_: usize = 0;
            let mut v___x_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6082_ = 0usize;
            v___x_6083_ = lean_usize_of_nat(v___x_6076_);
            v___x_6084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_6073_, v___x_6082_, v___x_6083_, v___x_6074_);
            return v___x_6084_;
        }
    }
}
pub unsafe fn l_Array_toPArray_x27___redArg___boxed(
    mut v_xs_6085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6086_ = l_Array_toPArray_x27___redArg(v_xs_6085_);
    leanh::lean_dec_ref(v_xs_6085_);
    return v_res_6086_;
}
pub unsafe fn l_Array_toPArray_x27(
    mut v_00_u03b1_6087_: *mut leanh::LeanObject,
    mut v_xs_6088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6089_ = l_Array_toPArray_x27___redArg(v_xs_6088_);
    return v___x_6089_;
}
pub unsafe fn l_Array_toPArray_x27___boxed(
    mut v_00_u03b1_6090_: *mut leanh::LeanObject,
    mut v_xs_6091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6092_ = l_Array_toPArray_x27(v_00_u03b1_6090_, v_xs_6091_);
    leanh::lean_dec_ref(v_xs_6091_);
    return v_res_6092_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_PersistentArray(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Fold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_PersistentArray_initShift = _init_l_Lean_PersistentArray_initShift();
    l_Lean_PersistentArray_branching = _init_l_Lean_PersistentArray_branching();
    l_Lean_PersistentArray_tooBig = _init_l_Lean_PersistentArray_tooBig();
    leanh::lean_mark_persistent(l_Lean_PersistentArray_tooBig);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_PersistentArray(
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
pub unsafe fn initialize_Lean_Data_PersistentArray(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Fold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_PersistentArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_PersistentArray(builtin);
}