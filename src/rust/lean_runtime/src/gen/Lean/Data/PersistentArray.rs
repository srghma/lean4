// Lean compiler output
// Module: Lean.Data.PersistentArray
// Imports: Init.Data.Nat.Fold Init.Data.UInt.Basic Init.Data.String.Defs Init.Data.ToString.Macro Init.Omega
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_pop, lean_array_size, lean_array_uget_borrowed,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_pow, lean_nat_sub,
    lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_box_usize, lean_closure_set, lean_ctor_get,
    lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_Lean_instInhabitedPersistentArrayNode_default___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_instInhabitedPersistentArrayNode_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPersistentArrayNode_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instInhabitedPersistentArrayNode_default___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instInhabitedPersistentArrayNode_default___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instInhabitedPersistentArrayNode_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPersistentArrayNode_default___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_instInhabitedPersistentArrayNode___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedPersistentArrayNode___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_PersistentArray_initShift: usize = 0;
pub static mut l_Lean_PersistentArray_branching: usize = 0;
static mut l_Lean_instInhabitedPersistentArray_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedPersistentArray_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedPersistentArray_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedPersistentArray_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedPersistentArray___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedPersistentArray___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentArray_mkNewPath___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PersistentArray_mkNewPath___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PersistentArray_mkNewTail___redArg___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_PersistentArray_mkNewTail___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_mkNewTail___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_PersistentArray_mkNewTail___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PersistentArray_mkNewTail___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentArray_tooBig___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PersistentArray_tooBig___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentArray_tooBig___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PersistentArray_tooBig___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_PersistentArray_tooBig: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentArray_popLeaf___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PersistentArray_popLeaf___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentArray_popLeaf___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PersistentArray_popLeaf___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PersistentArray_findSomeMAux___redArg___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_PersistentArray_findSomeMAux___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
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
static mut l_Lean_PersistentArray_foldl___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
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
static mut l_Lean_PersistentArray_foldl___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
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
static mut l_Lean_PersistentArray_foldl___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
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
static mut l_Lean_PersistentArray_foldl___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__4_value: LeanClosureObject<0> =
    LeanClosureObject {
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
static mut l_Lean_PersistentArray_foldl___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__5_value: LeanClosureObject<0> =
    LeanClosureObject {
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
static mut l_Lean_PersistentArray_foldl___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__6_value: LeanClosureObject<0> =
    LeanClosureObject {
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
static mut l_Lean_PersistentArray_foldl___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__7_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_PersistentArray_foldl___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__8_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_PersistentArray_foldl___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_foldl___redArg___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_PersistentArray_foldl___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_foldl___redArg___closed__9_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_instAppend___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PersistentArray_append___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_PersistentArray_instAppend___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_instAppend___closed__0_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_mapMAux___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PersistentArray_mapMAux___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PersistentArray_mapMAux___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_mapMAux___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_PersistentArray_mapMAux___redArg___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PersistentArray_mapMAux___redArg___lam__2 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PersistentArray_mapMAux___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_mapMAux___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_PersistentArray_Stats_toString___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_PersistentArray_Stats_toString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_Stats_toString___closed__0_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_Stats_toString___closed__1_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_PersistentArray_Stats_toString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_Stats_toString___closed__1_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_Stats_toString___closed__2_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_PersistentArray_Stats_toString___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_Stats_toString___closed__2_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_Stats_toString___closed__3_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_PersistentArray_Stats_toString___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_Stats_toString___closed__3_value) as *mut LeanObject;
pub static l_Lean_PersistentArray_instToStringStats___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PersistentArray_Stats_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PersistentArray_instToStringStats___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_instToStringStats___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_PersistentArray_instToStringStats: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentArray_instToStringStats___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_mkPersistentArray___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkPersistentArray___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_PersistentArrayNode_ctorIdx___redArg(
    mut v_x_3047_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3047_) == 0 {
        let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
        v___x_3048_ = lean_unsigned_to_nat(0);
        return v___x_3048_;
    } else {
        let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
        v___x_3049_ = lean_unsigned_to_nat(1);
        return v___x_3049_;
    }
}
pub unsafe fn l_Lean_PersistentArrayNode_ctorIdx___redArg___boxed(
    mut v_x_3050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3051_: *mut LeanObject = core::ptr::null_mut();
    v_res_3051_ = l_Lean_PersistentArrayNode_ctorIdx___redArg(v_x_3050_);
    lean_dec_ref(v_x_3050_);
    return v_res_3051_;
}
pub unsafe fn l_Lean_PersistentArrayNode_ctorIdx(
    mut v_00_u03b1_3052_: *mut LeanObject,
    mut v_x_3053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    v___x_3054_ = l_Lean_PersistentArrayNode_ctorIdx___redArg(v_x_3053_);
    return v___x_3054_;
}
pub unsafe fn l_Lean_PersistentArrayNode_ctorIdx___boxed(
    mut v_00_u03b1_3055_: *mut LeanObject,
    mut v_x_3056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3057_: *mut LeanObject = core::ptr::null_mut();
    v_res_3057_ = l_Lean_PersistentArrayNode_ctorIdx(v_00_u03b1_3055_, v_x_3056_);
    lean_dec_ref(v_x_3056_);
    return v_res_3057_;
}
pub unsafe fn l_Lean_PersistentArrayNode_ctorElim___redArg(
    mut v_t_3058_: *mut LeanObject,
    mut v_k_3059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    v_cs_3060_ = lean_ctor_get(v_t_3058_, 0);
    lean_inc_ref(v_cs_3060_);
    lean_dec_ref(v_t_3058_);
    v___x_3061_ = lean_apply_1(v_k_3059_, v_cs_3060_);
    return v___x_3061_;
}
pub unsafe fn l_Lean_PersistentArrayNode_ctorElim(
    mut v_00_u03b1_3062_: *mut LeanObject,
    mut v_motive__1_3063_: *mut LeanObject,
    mut v_ctorIdx_3064_: *mut LeanObject,
    mut v_t_3065_: *mut LeanObject,
    mut v_h_3066_: *mut LeanObject,
    mut v_k_3067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    v___x_3068_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_3065_, v_k_3067_);
    return v___x_3068_;
}
pub unsafe fn l_Lean_PersistentArrayNode_ctorElim___boxed(
    mut v_00_u03b1_3069_: *mut LeanObject,
    mut v_motive__1_3070_: *mut LeanObject,
    mut v_ctorIdx_3071_: *mut LeanObject,
    mut v_t_3072_: *mut LeanObject,
    mut v_h_3073_: *mut LeanObject,
    mut v_k_3074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3075_: *mut LeanObject = core::ptr::null_mut();
    v_res_3075_ = l_Lean_PersistentArrayNode_ctorElim(
        v_00_u03b1_3069_,
        v_motive__1_3070_,
        v_ctorIdx_3071_,
        v_t_3072_,
        v_h_3073_,
        v_k_3074_,
    );
    lean_dec(v_ctorIdx_3071_);
    return v_res_3075_;
}
pub unsafe fn l_Lean_PersistentArrayNode_node_elim___redArg(
    mut v_t_3076_: *mut LeanObject,
    mut v_node_3077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    v___x_3078_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_3076_, v_node_3077_);
    return v___x_3078_;
}
pub unsafe fn l_Lean_PersistentArrayNode_node_elim(
    mut v_00_u03b1_3079_: *mut LeanObject,
    mut v_motive__1_3080_: *mut LeanObject,
    mut v_t_3081_: *mut LeanObject,
    mut v_h_3082_: *mut LeanObject,
    mut v_node_3083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    v___x_3084_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_3081_, v_node_3083_);
    return v___x_3084_;
}
pub unsafe fn l_Lean_PersistentArrayNode_leaf_elim___redArg(
    mut v_t_3085_: *mut LeanObject,
    mut v_leaf_3086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    v___x_3087_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_3085_, v_leaf_3086_);
    return v___x_3087_;
}
pub unsafe fn l_Lean_PersistentArrayNode_leaf_elim(
    mut v_00_u03b1_3088_: *mut LeanObject,
    mut v_motive__1_3089_: *mut LeanObject,
    mut v_t_3090_: *mut LeanObject,
    mut v_h_3091_: *mut LeanObject,
    mut v_leaf_3092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    v___x_3093_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_3090_, v_leaf_3092_);
    return v___x_3093_;
}
pub unsafe fn l_Lean_instInhabitedPersistentArrayNode_default(
    mut v_00_u03b1_3098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    v___x_3099_ = l_Lean_instInhabitedPersistentArrayNode_default___closed__1;
    return v___x_3099_;
}
pub unsafe fn _init_l_Lean_instInhabitedPersistentArrayNode___closed__0() -> *mut LeanObject {
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    v___x_3100_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
    return v___x_3100_;
}
pub unsafe fn l_Lean_instInhabitedPersistentArrayNode(
    mut v_a_3101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    v___x_3102_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0_once),
        _init_l_Lean_instInhabitedPersistentArrayNode___closed__0,
    );
    return v___x_3102_;
}
pub unsafe fn l_Lean_PersistentArrayNode_isNode___redArg(mut v_x_3103_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_3103_) == 0 {
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
    mut v_x_3106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3107_: u8 = 0;
    let mut v_r_3108_: *mut LeanObject = core::ptr::null_mut();
    v_res_3107_ = l_Lean_PersistentArrayNode_isNode___redArg(v_x_3106_);
    lean_dec_ref(v_x_3106_);
    v_r_3108_ = lean_box((v_res_3107_) as usize);
    return v_r_3108_;
}
pub unsafe fn l_Lean_PersistentArrayNode_isNode(
    mut v_00_u03b1_3109_: *mut LeanObject,
    mut v_x_3110_: *mut LeanObject,
) -> u8 {
    let mut v___x_3111_: u8 = 0;
    v___x_3111_ = l_Lean_PersistentArrayNode_isNode___redArg(v_x_3110_);
    return v___x_3111_;
}
pub unsafe fn l_Lean_PersistentArrayNode_isNode___boxed(
    mut v_00_u03b1_3112_: *mut LeanObject,
    mut v_x_3113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3114_: u8 = 0;
    let mut v_r_3115_: *mut LeanObject = core::ptr::null_mut();
    v_res_3114_ = l_Lean_PersistentArrayNode_isNode(v_00_u03b1_3112_, v_x_3113_);
    lean_dec_ref(v_x_3113_);
    v_r_3115_ = lean_box((v_res_3114_) as usize);
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
pub unsafe fn _init_l_Lean_instInhabitedPersistentArray_default___closed__0() -> *mut LeanObject {
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    v___x_3118_ = lean_unsigned_to_nat(32);
    v___x_3119_ = lean_mk_empty_array_with_capacity(v___x_3118_);
    v___x_3120_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3120_, 0, v___x_3119_);
    return v___x_3120_;
}
pub unsafe fn _init_l_Lean_instInhabitedPersistentArray_default___closed__1() -> *mut LeanObject {
    let mut v___x_3121_: usize = 0;
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    v___x_3121_ = 5usize;
    v___x_3122_ = lean_unsigned_to_nat(0);
    v___x_3123_ = lean_unsigned_to_nat(32);
    v___x_3124_ = lean_mk_empty_array_with_capacity(v___x_3123_);
    v___x_3125_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__0_once),
        _init_l_Lean_instInhabitedPersistentArray_default___closed__0,
    );
    v___x_3126_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3126_, 0, v___x_3125_);
    lean_ctor_set(v___x_3126_, 1, v___x_3124_);
    lean_ctor_set(v___x_3126_, 2, v___x_3122_);
    lean_ctor_set(v___x_3126_, 3, v___x_3122_);
    lean_ctor_set_usize(v___x_3126_, 4, v___x_3121_);
    return v___x_3126_;
}
pub unsafe fn l_Lean_instInhabitedPersistentArray_default(
    mut v_00_u03b1_3127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    v___x_3128_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__1_once),
        _init_l_Lean_instInhabitedPersistentArray_default___closed__1,
    );
    return v___x_3128_;
}
pub unsafe fn _init_l_Lean_instInhabitedPersistentArray___closed__0() -> *mut LeanObject {
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    v___x_3129_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
    return v___x_3129_;
}
pub unsafe fn l_Lean_instInhabitedPersistentArray(
    mut v_a_3130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    v___x_3131_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray___closed__0_once),
        _init_l_Lean_instInhabitedPersistentArray___closed__0,
    );
    return v___x_3131_;
}
pub unsafe fn l_Lean_PersistentArray_empty(
    mut v_00_u03b1_3132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    v___x_3133_ = lean_unsigned_to_nat(32);
    v___x_3134_ = lean_mk_empty_array_with_capacity(v___x_3133_);
    lean_dec_ref(v___x_3134_);
    v___x_3135_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArray_default___closed__1_once),
        _init_l_Lean_instInhabitedPersistentArray_default___closed__1,
    );
    return v___x_3135_;
}
pub unsafe fn l_Lean_PersistentArray_isEmpty___redArg(mut v_a_3136_: *mut LeanObject) -> u8 {
    let mut v_size_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    v_size_3137_ = lean_ctor_get(v_a_3136_, 2);
    v___x_3138_ = lean_unsigned_to_nat(0);
    v___x_3139_ = lean_nat_dec_eq(v_size_3137_, v___x_3138_);
    return v___x_3139_;
}
pub unsafe fn l_Lean_PersistentArray_isEmpty___redArg___boxed(
    mut v_a_3140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3141_: u8 = 0;
    let mut v_r_3142_: *mut LeanObject = core::ptr::null_mut();
    v_res_3141_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_3140_);
    lean_dec_ref(v_a_3140_);
    v_r_3142_ = lean_box((v_res_3141_) as usize);
    return v_r_3142_;
}
pub unsafe fn l_Lean_PersistentArray_isEmpty(
    mut v_00_u03b1_3143_: *mut LeanObject,
    mut v_a_3144_: *mut LeanObject,
) -> u8 {
    let mut v___x_3145_: u8 = 0;
    v___x_3145_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_3144_);
    return v___x_3145_;
}
pub unsafe fn l_Lean_PersistentArray_isEmpty___boxed(
    mut v_00_u03b1_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3148_: u8 = 0;
    let mut v_r_3149_: *mut LeanObject = core::ptr::null_mut();
    v_res_3148_ = l_Lean_PersistentArray_isEmpty(v_00_u03b1_3146_, v_a_3147_);
    lean_dec_ref(v_a_3147_);
    v_r_3149_ = lean_box((v_res_3148_) as usize);
    return v_r_3149_;
}
pub unsafe fn l_Lean_PersistentArray_mkEmptyArray(
    mut v_00_u03b1_3150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    v___x_3151_ = lean_unsigned_to_nat(32);
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
    mut v_i_3156_: *mut LeanObject,
    mut v_shift_3157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3158_: usize = 0;
    let mut v_shift_boxed_3159_: usize = 0;
    let mut v_res_3160_: usize = 0;
    let mut v_r_3161_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3158_ = lean_unbox_usize(v_i_3156_);
    lean_dec(v_i_3156_);
    v_shift_boxed_3159_ = lean_unbox_usize(v_shift_3157_);
    lean_dec(v_shift_3157_);
    v_res_3160_ = l_Lean_PersistentArray_mul2Shift(v_i_boxed_3158_, v_shift_boxed_3159_);
    v_r_3161_ = lean_box_usize(v_res_3160_);
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
    mut v_i_3165_: *mut LeanObject,
    mut v_shift_3166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3167_: usize = 0;
    let mut v_shift_boxed_3168_: usize = 0;
    let mut v_res_3169_: usize = 0;
    let mut v_r_3170_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3167_ = lean_unbox_usize(v_i_3165_);
    lean_dec(v_i_3165_);
    v_shift_boxed_3168_ = lean_unbox_usize(v_shift_3166_);
    lean_dec(v_shift_3166_);
    v_res_3169_ = l_Lean_PersistentArray_div2Shift(v_i_boxed_3167_, v_shift_boxed_3168_);
    v_r_3170_ = lean_box_usize(v_res_3169_);
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
    mut v_i_3177_: *mut LeanObject,
    mut v_shift_3178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3179_: usize = 0;
    let mut v_shift_boxed_3180_: usize = 0;
    let mut v_res_3181_: usize = 0;
    let mut v_r_3182_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3179_ = lean_unbox_usize(v_i_3177_);
    lean_dec(v_i_3177_);
    v_shift_boxed_3180_ = lean_unbox_usize(v_shift_3178_);
    lean_dec(v_shift_3178_);
    v_res_3181_ = l_Lean_PersistentArray_mod2Shift(v_i_boxed_3179_, v_shift_boxed_3180_);
    v_r_3182_ = lean_box_usize(v_res_3181_);
    return v_r_3182_;
}
pub unsafe fn l_Lean_PersistentArray_getAux___redArg(
    mut v_inst_3183_: *mut LeanObject,
    mut v_x_3184_: *mut LeanObject,
    mut v_x_3185_: usize,
    mut v_x_3186_: usize,
) -> *mut LeanObject {
    let mut v_cs_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: usize = 0;
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: usize = 0;
    let mut v___x_3193_: usize = 0;
    let mut v___x_3194_: usize = 0;
    let mut v___x_3195_: usize = 0;
    let mut v___x_3196_: usize = 0;
    let mut v___x_3197_: usize = 0;
    let mut v_vs_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3184_) == 0 {
                    v_cs_3187_ = lean_ctor_get(v_x_3184_, 0);
                    v___x_3188_ = lean_obj_once(
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
                    lean_dec(v___x_3190_);
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
                    v_vs_3199_ = lean_ctor_get(v_x_3184_, 0);
                    v___x_3200_ = lean_usize_to_nat(v_x_3185_);
                    v___x_3201_ = lean_array_get_borrowed(v_inst_3183_, v_vs_3199_, v___x_3200_);
                    lean_dec(v___x_3200_);
                    lean_inc(v___x_3201_);
                    return v___x_3201_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_getAux___redArg___boxed(
    mut v_inst_3202_: *mut LeanObject,
    mut v_x_3203_: *mut LeanObject,
    mut v_x_3204_: *mut LeanObject,
    mut v_x_3205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_92__boxed_3206_: usize = 0;
    let mut v_x_93__boxed_3207_: usize = 0;
    let mut v_res_3208_: *mut LeanObject = core::ptr::null_mut();
    v_x_92__boxed_3206_ = lean_unbox_usize(v_x_3204_);
    lean_dec(v_x_3204_);
    v_x_93__boxed_3207_ = lean_unbox_usize(v_x_3205_);
    lean_dec(v_x_3205_);
    v_res_3208_ = l_Lean_PersistentArray_getAux___redArg(
        v_inst_3202_,
        v_x_3203_,
        v_x_92__boxed_3206_,
        v_x_93__boxed_3207_,
    );
    lean_dec_ref(v_x_3203_);
    lean_dec(v_inst_3202_);
    return v_res_3208_;
}
pub unsafe fn l_Lean_PersistentArray_getAux(
    mut v_00_u03b1_3209_: *mut LeanObject,
    mut v_inst_3210_: *mut LeanObject,
    mut v_x_3211_: *mut LeanObject,
    mut v_x_3212_: usize,
    mut v_x_3213_: usize,
) -> *mut LeanObject {
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    v___x_3214_ =
        l_Lean_PersistentArray_getAux___redArg(v_inst_3210_, v_x_3211_, v_x_3212_, v_x_3213_);
    return v___x_3214_;
}
pub unsafe fn l_Lean_PersistentArray_getAux___boxed(
    mut v_00_u03b1_3215_: *mut LeanObject,
    mut v_inst_3216_: *mut LeanObject,
    mut v_x_3217_: *mut LeanObject,
    mut v_x_3218_: *mut LeanObject,
    mut v_x_3219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_134__boxed_3220_: usize = 0;
    let mut v_x_135__boxed_3221_: usize = 0;
    let mut v_res_3222_: *mut LeanObject = core::ptr::null_mut();
    v_x_134__boxed_3220_ = lean_unbox_usize(v_x_3218_);
    lean_dec(v_x_3218_);
    v_x_135__boxed_3221_ = lean_unbox_usize(v_x_3219_);
    lean_dec(v_x_3219_);
    v_res_3222_ = l_Lean_PersistentArray_getAux(
        v_00_u03b1_3215_,
        v_inst_3216_,
        v_x_3217_,
        v_x_134__boxed_3220_,
        v_x_135__boxed_3221_,
    );
    lean_dec_ref(v_x_3217_);
    lean_dec(v_inst_3216_);
    return v_res_3222_;
}
pub unsafe fn l_Lean_PersistentArray_get_x21___redArg(
    mut v_inst_3223_: *mut LeanObject,
    mut v_t_3224_: *mut LeanObject,
    mut v_i_3225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_3228_: usize = 0;
    let mut v_tailOff_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: u8 = 0;
    v_root_3226_ = lean_ctor_get(v_t_3224_, 0);
    v_tail_3227_ = lean_ctor_get(v_t_3224_, 1);
    v_shift_3228_ = lean_ctor_get_usize(v_t_3224_, 4);
    v_tailOff_3229_ = lean_ctor_get(v_t_3224_, 3);
    v___x_3230_ = lean_nat_dec_le(v_tailOff_3229_, v_i_3225_);
    if v___x_3230_ == 0 {
        let mut v___x_3231_: usize = 0;
        let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
        v___x_3231_ = lean_usize_of_nat(v_i_3225_);
        v___x_3232_ = l_Lean_PersistentArray_getAux___redArg(
            v_inst_3223_,
            v_root_3226_,
            v___x_3231_,
            v_shift_3228_,
        );
        return v___x_3232_;
    } else {
        let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
        v___x_3233_ = lean_nat_sub(v_i_3225_, v_tailOff_3229_);
        v___x_3234_ = lean_array_get_borrowed(v_inst_3223_, v_tail_3227_, v___x_3233_);
        lean_dec(v___x_3233_);
        lean_inc(v___x_3234_);
        return v___x_3234_;
    }
}
pub unsafe fn l_Lean_PersistentArray_get_x21___redArg___boxed(
    mut v_inst_3235_: *mut LeanObject,
    mut v_t_3236_: *mut LeanObject,
    mut v_i_3237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3238_: *mut LeanObject = core::ptr::null_mut();
    v_res_3238_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_3235_, v_t_3236_, v_i_3237_);
    lean_dec(v_i_3237_);
    lean_dec_ref(v_t_3236_);
    lean_dec(v_inst_3235_);
    return v_res_3238_;
}
pub unsafe fn l_Lean_PersistentArray_get_x21(
    mut v_00_u03b1_3239_: *mut LeanObject,
    mut v_inst_3240_: *mut LeanObject,
    mut v_t_3241_: *mut LeanObject,
    mut v_i_3242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    v___x_3243_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_3240_, v_t_3241_, v_i_3242_);
    return v___x_3243_;
}
pub unsafe fn l_Lean_PersistentArray_get_x21___boxed(
    mut v_00_u03b1_3244_: *mut LeanObject,
    mut v_inst_3245_: *mut LeanObject,
    mut v_t_3246_: *mut LeanObject,
    mut v_i_3247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3248_: *mut LeanObject = core::ptr::null_mut();
    v_res_3248_ =
        l_Lean_PersistentArray_get_x21(v_00_u03b1_3244_, v_inst_3245_, v_t_3246_, v_i_3247_);
    lean_dec(v_i_3247_);
    lean_dec_ref(v_t_3246_);
    lean_dec(v_inst_3245_);
    return v_res_3248_;
}
pub unsafe fn l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(
    mut v_inst_3249_: *mut LeanObject,
    mut v_xs_3250_: *mut LeanObject,
    mut v_i_3251_: *mut LeanObject,
    mut v_x_3252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    v___x_3253_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_3249_, v_xs_3250_, v_i_3251_);
    return v___x_3253_;
}
pub unsafe fn l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed(
    mut v_inst_3254_: *mut LeanObject,
    mut v_xs_3255_: *mut LeanObject,
    mut v_i_3256_: *mut LeanObject,
    mut v_x_3257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3258_: *mut LeanObject = core::ptr::null_mut();
    v_res_3258_ = l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(
        v_inst_3254_,
        v_xs_3255_,
        v_i_3256_,
        v_x_3257_,
    );
    lean_dec(v_i_3256_);
    lean_dec_ref(v_xs_3255_);
    lean_dec(v_inst_3254_);
    return v_res_3258_;
}
pub unsafe fn l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg(
    mut v_inst_3259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3260_: *mut LeanObject = core::ptr::null_mut();
    v___f_3260_ = lean_alloc_closure(
        l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3260_, 0, v_inst_3259_);
    return v___f_3260_;
}
pub unsafe fn l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited(
    mut v_00_u03b1_3261_: *mut LeanObject,
    mut v_inst_3262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3263_: *mut LeanObject = core::ptr::null_mut();
    v___f_3263_ = lean_alloc_closure(
        l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_3263_, 0, v_inst_3262_);
    return v___f_3263_;
}
pub unsafe fn l_Lean_PersistentArray_setAux___redArg(
    mut v_x_3264_: *mut LeanObject,
    mut v_x_3265_: usize,
    mut v_x_3266_: usize,
    mut v_x_3267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_3269_: usize = 0;
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: u8 = 0;
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3275_: u8 = 0;
    let mut v___x_3276_: usize = 0;
    let mut v___x_3277_: usize = 0;
    let mut v___x_3278_: usize = 0;
    let mut v_i_3279_: usize = 0;
    let mut v___x_3280_: usize = 0;
    let mut v_shift_3281_: usize = 0;
    let mut v_v_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3290_: u8 = 0;
    let mut v_unused_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3295_: u8 = 0;
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3264_) == 0 {
                    v_cs_3268_ = lean_ctor_get(v_x_3264_, 0);
                    v_j_3269_ = lean_usize_shift_right(v_x_3265_, v_x_3266_);
                    v___x_3270_ = lean_usize_to_nat(v_j_3269_);
                    v___x_3271_ = lean_array_get_size(v_cs_3268_);
                    v___x_3272_ = lean_nat_dec_lt(v___x_3270_, v___x_3271_);
                    if v___x_3272_ == 0 {
                        lean_dec(v___x_3270_);
                        lean_dec(v_x_3267_);
                        return v_x_3264_;
                    } else {
                        lean_inc_ref(v_cs_3268_);
                        v_isSharedCheck_3290_ = (!lean_is_exclusive(v_x_3264_)) as u8;
                        if v_isSharedCheck_3290_ == 0 {
                            v_unused_3291_ = lean_ctor_get(v_x_3264_, 0);
                            lean_dec(v_unused_3291_);
                            v___x_3274_ = v_x_3264_;
                            v_isShared_3275_ = v_isSharedCheck_3290_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3264_);
                            v___x_3274_ = lean_box(0);
                            v_isShared_3275_ = v_isSharedCheck_3290_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_vs_3292_ = lean_ctor_get(v_x_3264_, 0);
                    v_isSharedCheck_3301_ = (!lean_is_exclusive(v_x_3264_)) as u8;
                    if v_isSharedCheck_3301_ == 0 {
                        v___x_3294_ = v_x_3264_;
                        v_isShared_3295_ = v_isSharedCheck_3301_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_vs_3292_);
                        lean_dec(v_x_3264_);
                        v___x_3294_ = lean_box(0);
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
                v___x_3283_ = lean_box(0);
                v_xs_x27_3284_ = lean_array_fset(v_cs_3268_, v___x_3270_, v___x_3283_);
                v___x_3285_ = l_Lean_PersistentArray_setAux___redArg(
                    v_v_3282_,
                    v_i_3279_,
                    v_shift_3281_,
                    v_x_3267_,
                );
                v___x_3286_ = lean_array_fset(v_xs_x27_3284_, v___x_3270_, v___x_3285_);
                lean_dec(v___x_3270_);
                if v_isShared_3275_ == 0 {
                    lean_ctor_set(v___x_3274_, 0, v___x_3286_);
                    v___x_3288_ = v___x_3274_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
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
                lean_dec(v___x_3296_);
                if v_isShared_3295_ == 0 {
                    lean_ctor_set(v___x_3294_, 0, v___x_3297_);
                    v___x_3299_ = v___x_3294_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
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
    mut v_x_3302_: *mut LeanObject,
    mut v_x_3303_: *mut LeanObject,
    mut v_x_3304_: *mut LeanObject,
    mut v_x_3305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_77__boxed_3306_: usize = 0;
    let mut v_x_78__boxed_3307_: usize = 0;
    let mut v_res_3308_: *mut LeanObject = core::ptr::null_mut();
    v_x_77__boxed_3306_ = lean_unbox_usize(v_x_3303_);
    lean_dec(v_x_3303_);
    v_x_78__boxed_3307_ = lean_unbox_usize(v_x_3304_);
    lean_dec(v_x_3304_);
    v_res_3308_ = l_Lean_PersistentArray_setAux___redArg(
        v_x_3302_,
        v_x_77__boxed_3306_,
        v_x_78__boxed_3307_,
        v_x_3305_,
    );
    return v_res_3308_;
}
pub unsafe fn l_Lean_PersistentArray_setAux(
    mut v_00_u03b1_3309_: *mut LeanObject,
    mut v_x_3310_: *mut LeanObject,
    mut v_x_3311_: usize,
    mut v_x_3312_: usize,
    mut v_x_3313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    v___x_3314_ =
        l_Lean_PersistentArray_setAux___redArg(v_x_3310_, v_x_3311_, v_x_3312_, v_x_3313_);
    return v___x_3314_;
}
pub unsafe fn l_Lean_PersistentArray_setAux___boxed(
    mut v_00_u03b1_3315_: *mut LeanObject,
    mut v_x_3316_: *mut LeanObject,
    mut v_x_3317_: *mut LeanObject,
    mut v_x_3318_: *mut LeanObject,
    mut v_x_3319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_147__boxed_3320_: usize = 0;
    let mut v_x_148__boxed_3321_: usize = 0;
    let mut v_res_3322_: *mut LeanObject = core::ptr::null_mut();
    v_x_147__boxed_3320_ = lean_unbox_usize(v_x_3317_);
    lean_dec(v_x_3317_);
    v_x_148__boxed_3321_ = lean_unbox_usize(v_x_3318_);
    lean_dec(v_x_3318_);
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
    mut v_t_3323_: *mut LeanObject,
    mut v_i_3324_: *mut LeanObject,
    mut v_a_3325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_3329_: usize = 0;
    let mut v_tailOff_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3333_: u8 = 0;
    let mut v___x_3334_: u8 = 0;
    let mut v___x_3335_: usize = 0;
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3326_ = lean_ctor_get(v_t_3323_, 0);
                v_tail_3327_ = lean_ctor_get(v_t_3323_, 1);
                v_size_3328_ = lean_ctor_get(v_t_3323_, 2);
                v_shift_3329_ = lean_ctor_get_usize(v_t_3323_, 4);
                v_tailOff_3330_ = lean_ctor_get(v_t_3323_, 3);
                v_isSharedCheck_3345_ = (!lean_is_exclusive(v_t_3323_)) as u8;
                if v_isSharedCheck_3345_ == 0 {
                    v___x_3332_ = v_t_3323_;
                    v_isShared_3333_ = v_isSharedCheck_3345_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tailOff_3330_);
                    lean_inc(v_size_3328_);
                    lean_inc(v_tail_3327_);
                    lean_inc(v_root_3326_);
                    lean_dec(v_t_3323_);
                    v___x_3332_ = lean_box(0);
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
                        lean_ctor_set(v___x_3332_, 0, v___x_3336_);
                        v___x_3338_ = v___x_3332_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3339_ =
                            lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3336_);
                        lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_tail_3327_);
                        lean_ctor_set(v_reuseFailAlloc_3339_, 2, v_size_3328_);
                        lean_ctor_set(v_reuseFailAlloc_3339_, 3, v_tailOff_3330_);
                        lean_ctor_set_usize(v_reuseFailAlloc_3339_, 4, v_shift_3329_);
                        v___x_3338_ = v_reuseFailAlloc_3339_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3340_ = lean_nat_sub(v_i_3324_, v_tailOff_3330_);
                    v___x_3341_ = lean_array_set(v_tail_3327_, v___x_3340_, v_a_3325_);
                    lean_dec(v___x_3340_);
                    if v_isShared_3333_ == 0 {
                        lean_ctor_set(v___x_3332_, 1, v___x_3341_);
                        v___x_3343_ = v___x_3332_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3344_ =
                            lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_root_3326_);
                        lean_ctor_set(v_reuseFailAlloc_3344_, 1, v___x_3341_);
                        lean_ctor_set(v_reuseFailAlloc_3344_, 2, v_size_3328_);
                        lean_ctor_set(v_reuseFailAlloc_3344_, 3, v_tailOff_3330_);
                        lean_ctor_set_usize(v_reuseFailAlloc_3344_, 4, v_shift_3329_);
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
    mut v_t_3346_: *mut LeanObject,
    mut v_i_3347_: *mut LeanObject,
    mut v_a_3348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3349_: *mut LeanObject = core::ptr::null_mut();
    v_res_3349_ = l_Lean_PersistentArray_set___redArg(v_t_3346_, v_i_3347_, v_a_3348_);
    lean_dec(v_i_3347_);
    return v_res_3349_;
}
pub unsafe fn l_Lean_PersistentArray_set(
    mut v_00_u03b1_3350_: *mut LeanObject,
    mut v_t_3351_: *mut LeanObject,
    mut v_i_3352_: *mut LeanObject,
    mut v_a_3353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    v___x_3354_ = l_Lean_PersistentArray_set___redArg(v_t_3351_, v_i_3352_, v_a_3353_);
    return v___x_3354_;
}
pub unsafe fn l_Lean_PersistentArray_set___boxed(
    mut v_00_u03b1_3355_: *mut LeanObject,
    mut v_t_3356_: *mut LeanObject,
    mut v_i_3357_: *mut LeanObject,
    mut v_a_3358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3359_: *mut LeanObject = core::ptr::null_mut();
    v_res_3359_ = l_Lean_PersistentArray_set(v_00_u03b1_3355_, v_t_3356_, v_i_3357_, v_a_3358_);
    lean_dec(v_i_3357_);
    return v_res_3359_;
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___redArg(
    mut v_f_3360_: *mut LeanObject,
    mut v_x_3361_: *mut LeanObject,
    mut v_x_3362_: usize,
    mut v_x_3363_: usize,
) -> *mut LeanObject {
    let mut v_cs_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_3365_: usize = 0;
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: u8 = 0;
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3371_: u8 = 0;
    let mut v___x_3372_: usize = 0;
    let mut v___x_3373_: usize = 0;
    let mut v___x_3374_: usize = 0;
    let mut v_i_3375_: usize = 0;
    let mut v___x_3376_: usize = 0;
    let mut v_shift_3377_: usize = 0;
    let mut v_v_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3386_: u8 = 0;
    let mut v_unused_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: u8 = 0;
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3394_: u8 = 0;
    let mut v_v_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3403_: u8 = 0;
    let mut v_unused_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3361_) == 0 {
                    v_cs_3364_ = lean_ctor_get(v_x_3361_, 0);
                    v_j_3365_ = lean_usize_shift_right(v_x_3362_, v_x_3363_);
                    v___x_3366_ = lean_usize_to_nat(v_j_3365_);
                    v___x_3367_ = lean_array_get_size(v_cs_3364_);
                    v___x_3368_ = lean_nat_dec_lt(v___x_3366_, v___x_3367_);
                    if v___x_3368_ == 0 {
                        lean_dec(v___x_3366_);
                        lean_dec(v_f_3360_);
                        return v_x_3361_;
                    } else {
                        lean_inc_ref(v_cs_3364_);
                        v_isSharedCheck_3386_ = (!lean_is_exclusive(v_x_3361_)) as u8;
                        if v_isSharedCheck_3386_ == 0 {
                            v_unused_3387_ = lean_ctor_get(v_x_3361_, 0);
                            lean_dec(v_unused_3387_);
                            v___x_3370_ = v_x_3361_;
                            v_isShared_3371_ = v_isSharedCheck_3386_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3361_);
                            v___x_3370_ = lean_box(0);
                            v_isShared_3371_ = v_isSharedCheck_3386_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_vs_3388_ = lean_ctor_get(v_x_3361_, 0);
                    v___x_3389_ = lean_usize_to_nat(v_x_3362_);
                    v___x_3390_ = lean_array_get_size(v_vs_3388_);
                    v___x_3391_ = lean_nat_dec_lt(v___x_3389_, v___x_3390_);
                    if v___x_3391_ == 0 {
                        lean_dec(v___x_3389_);
                        lean_dec(v_f_3360_);
                        return v_x_3361_;
                    } else {
                        lean_inc_ref(v_vs_3388_);
                        v_isSharedCheck_3403_ = (!lean_is_exclusive(v_x_3361_)) as u8;
                        if v_isSharedCheck_3403_ == 0 {
                            v_unused_3404_ = lean_ctor_get(v_x_3361_, 0);
                            lean_dec(v_unused_3404_);
                            v___x_3393_ = v_x_3361_;
                            v_isShared_3394_ = v_isSharedCheck_3403_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v_x_3361_);
                            v___x_3393_ = lean_box(0);
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
                v___x_3379_ = lean_box(0);
                v_xs_x27_3380_ = lean_array_fset(v_cs_3364_, v___x_3366_, v___x_3379_);
                v___x_3381_ = l_Lean_PersistentArray_modifyAux___redArg(
                    v_f_3360_,
                    v_v_3378_,
                    v_i_3375_,
                    v_shift_3377_,
                );
                v___x_3382_ = lean_array_fset(v_xs_x27_3380_, v___x_3366_, v___x_3381_);
                lean_dec(v___x_3366_);
                if v_isShared_3371_ == 0 {
                    lean_ctor_set(v___x_3370_, 0, v___x_3382_);
                    v___x_3384_ = v___x_3370_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3382_);
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
                v___x_3396_ = lean_box(0);
                v_xs_x27_3397_ = lean_array_fset(v_vs_3388_, v___x_3389_, v___x_3396_);
                v___x_3398_ = lean_apply_1(v_f_3360_, v_v_3395_);
                v___x_3399_ = lean_array_fset(v_xs_x27_3397_, v___x_3389_, v___x_3398_);
                lean_dec(v___x_3389_);
                if v_isShared_3394_ == 0 {
                    lean_ctor_set(v___x_3393_, 0, v___x_3399_);
                    v___x_3401_ = v___x_3393_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3399_);
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
    mut v_f_3405_: *mut LeanObject,
    mut v_x_3406_: *mut LeanObject,
    mut v_x_3407_: *mut LeanObject,
    mut v_x_3408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_92__boxed_3409_: usize = 0;
    let mut v_x_93__boxed_3410_: usize = 0;
    let mut v_res_3411_: *mut LeanObject = core::ptr::null_mut();
    v_x_92__boxed_3409_ = lean_unbox_usize(v_x_3407_);
    lean_dec(v_x_3407_);
    v_x_93__boxed_3410_ = lean_unbox_usize(v_x_3408_);
    lean_dec(v_x_3408_);
    v_res_3411_ = l_Lean_PersistentArray_modifyAux___redArg(
        v_f_3405_,
        v_x_3406_,
        v_x_92__boxed_3409_,
        v_x_93__boxed_3410_,
    );
    return v_res_3411_;
}
pub unsafe fn l_Lean_PersistentArray_modifyAux(
    mut v_00_u03b1_3412_: *mut LeanObject,
    mut v_inst_3413_: *mut LeanObject,
    mut v_f_3414_: *mut LeanObject,
    mut v_x_3415_: *mut LeanObject,
    mut v_x_3416_: usize,
    mut v_x_3417_: usize,
) -> *mut LeanObject {
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    v___x_3418_ =
        l_Lean_PersistentArray_modifyAux___redArg(v_f_3414_, v_x_3415_, v_x_3416_, v_x_3417_);
    return v___x_3418_;
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___boxed(
    mut v_00_u03b1_3419_: *mut LeanObject,
    mut v_inst_3420_: *mut LeanObject,
    mut v_f_3421_: *mut LeanObject,
    mut v_x_3422_: *mut LeanObject,
    mut v_x_3423_: *mut LeanObject,
    mut v_x_3424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_170__boxed_3425_: usize = 0;
    let mut v_x_171__boxed_3426_: usize = 0;
    let mut v_res_3427_: *mut LeanObject = core::ptr::null_mut();
    v_x_170__boxed_3425_ = lean_unbox_usize(v_x_3423_);
    lean_dec(v_x_3423_);
    v_x_171__boxed_3426_ = lean_unbox_usize(v_x_3424_);
    lean_dec(v_x_3424_);
    v_res_3427_ = l_Lean_PersistentArray_modifyAux(
        v_00_u03b1_3419_,
        v_inst_3420_,
        v_f_3421_,
        v_x_3422_,
        v_x_170__boxed_3425_,
        v_x_171__boxed_3426_,
    );
    lean_dec(v_inst_3420_);
    return v_res_3427_;
}
pub unsafe fn l_Lean_PersistentArray_modify___redArg(
    mut v_t_3428_: *mut LeanObject,
    mut v_i_3429_: *mut LeanObject,
    mut v_f_3430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_3434_: usize = 0;
    let mut v_tailOff_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3439_: u8 = 0;
    let mut v___x_3440_: usize = 0;
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: u8 = 0;
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3431_ = lean_ctor_get(v_t_3428_, 0);
                v_tail_3432_ = lean_ctor_get(v_t_3428_, 1);
                v_size_3433_ = lean_ctor_get(v_t_3428_, 2);
                v_shift_3434_ = lean_ctor_get_usize(v_t_3428_, 4);
                v_tailOff_3435_ = lean_ctor_get(v_t_3428_, 3);
                v_isSharedCheck_3459_ = (!lean_is_exclusive(v_t_3428_)) as u8;
                if v_isSharedCheck_3459_ == 0 {
                    v___x_3437_ = v_t_3428_;
                    v_isShared_3438_ = v_isSharedCheck_3459_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tailOff_3435_);
                    lean_inc(v_size_3433_);
                    lean_inc(v_tail_3432_);
                    lean_inc(v_root_3431_);
                    lean_dec(v_t_3428_);
                    v___x_3437_ = lean_box(0);
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
                        lean_ctor_set(v___x_3437_, 0, v___x_3441_);
                        v___x_3443_ = v___x_3437_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3444_ =
                            lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
                        lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_tail_3432_);
                        lean_ctor_set(v_reuseFailAlloc_3444_, 2, v_size_3433_);
                        lean_ctor_set(v_reuseFailAlloc_3444_, 3, v_tailOff_3435_);
                        lean_ctor_set_usize(v_reuseFailAlloc_3444_, 4, v_shift_3434_);
                        v___x_3443_ = v_reuseFailAlloc_3444_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3445_ = lean_nat_sub(v_i_3429_, v_tailOff_3435_);
                    v___x_3446_ = lean_array_get_size(v_tail_3432_);
                    v___x_3447_ = lean_nat_dec_lt(v___x_3445_, v___x_3446_);
                    if v___x_3447_ == 0 {
                        lean_dec(v___x_3445_);
                        lean_dec(v_f_3430_);
                        if v_isShared_3438_ == 0 {
                            v___x_3449_ = v___x_3437_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3450_ =
                                lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_root_3431_);
                            lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_tail_3432_);
                            lean_ctor_set(v_reuseFailAlloc_3450_, 2, v_size_3433_);
                            lean_ctor_set(v_reuseFailAlloc_3450_, 3, v_tailOff_3435_);
                            lean_ctor_set_usize(v_reuseFailAlloc_3450_, 4, v_shift_3434_);
                            v___x_3449_ = v_reuseFailAlloc_3450_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_v_3451_ = lean_array_fget(v_tail_3432_, v___x_3445_);
                        v___x_3452_ = lean_box(0);
                        v_xs_x27_3453_ = lean_array_fset(v_tail_3432_, v___x_3445_, v___x_3452_);
                        v___x_3454_ = lean_apply_1(v_f_3430_, v_v_3451_);
                        v___x_3455_ = lean_array_fset(v_xs_x27_3453_, v___x_3445_, v___x_3454_);
                        lean_dec(v___x_3445_);
                        if v_isShared_3438_ == 0 {
                            lean_ctor_set(v___x_3437_, 1, v___x_3455_);
                            v___x_3457_ = v___x_3437_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3458_ =
                                lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_root_3431_);
                            lean_ctor_set(v_reuseFailAlloc_3458_, 1, v___x_3455_);
                            lean_ctor_set(v_reuseFailAlloc_3458_, 2, v_size_3433_);
                            lean_ctor_set(v_reuseFailAlloc_3458_, 3, v_tailOff_3435_);
                            lean_ctor_set_usize(v_reuseFailAlloc_3458_, 4, v_shift_3434_);
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
    mut v_t_3460_: *mut LeanObject,
    mut v_i_3461_: *mut LeanObject,
    mut v_f_3462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3463_: *mut LeanObject = core::ptr::null_mut();
    v_res_3463_ = l_Lean_PersistentArray_modify___redArg(v_t_3460_, v_i_3461_, v_f_3462_);
    lean_dec(v_i_3461_);
    return v_res_3463_;
}
pub unsafe fn l_Lean_PersistentArray_modify(
    mut v_00_u03b1_3464_: *mut LeanObject,
    mut v_inst_3465_: *mut LeanObject,
    mut v_t_3466_: *mut LeanObject,
    mut v_i_3467_: *mut LeanObject,
    mut v_f_3468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    v___x_3469_ = l_Lean_PersistentArray_modify___redArg(v_t_3466_, v_i_3467_, v_f_3468_);
    return v___x_3469_;
}
pub unsafe fn l_Lean_PersistentArray_modify___boxed(
    mut v_00_u03b1_3470_: *mut LeanObject,
    mut v_inst_3471_: *mut LeanObject,
    mut v_t_3472_: *mut LeanObject,
    mut v_i_3473_: *mut LeanObject,
    mut v_f_3474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3475_: *mut LeanObject = core::ptr::null_mut();
    v_res_3475_ = l_Lean_PersistentArray_modify(
        v_00_u03b1_3470_,
        v_inst_3471_,
        v_t_3472_,
        v_i_3473_,
        v_f_3474_,
    );
    lean_dec(v_i_3473_);
    lean_dec(v_inst_3471_);
    return v_res_3475_;
}
pub unsafe fn _init_l_Lean_PersistentArray_mkNewPath___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    v___x_3476_ = l_Lean_PersistentArray_mkEmptyArray(lean_box(0));
    return v___x_3476_;
}
pub unsafe fn l_Lean_PersistentArray_mkNewPath___redArg(
    mut v_shift_3477_: usize,
    mut v_a_3478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3479_: usize = 0;
    let mut v___x_3480_: u8 = 0;
    v___x_3479_ = 0usize;
    v___x_3480_ = lean_usize_dec_eq(v_shift_3477_, v___x_3479_);
    if v___x_3480_ == 0 {
        let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3482_: usize = 0;
        let mut v___x_3483_: usize = 0;
        let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
        v___x_3481_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_PersistentArray_mkNewPath___redArg___closed__0),
            core::ptr::addr_of_mut!(l_Lean_PersistentArray_mkNewPath___redArg___closed__0_once),
            _init_l_Lean_PersistentArray_mkNewPath___redArg___closed__0,
        );
        v___x_3482_ = 5usize;
        v___x_3483_ = lean_usize_sub(v_shift_3477_, v___x_3482_);
        v___x_3484_ = l_Lean_PersistentArray_mkNewPath___redArg(v___x_3483_, v_a_3478_);
        v___x_3485_ = lean_array_push(v___x_3481_, v___x_3484_);
        v___x_3486_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3486_, 0, v___x_3485_);
        return v___x_3486_;
    } else {
        let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
        v___x_3487_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3487_, 0, v_a_3478_);
        return v___x_3487_;
    }
}
pub unsafe fn l_Lean_PersistentArray_mkNewPath___redArg___boxed(
    mut v_shift_3488_: *mut LeanObject,
    mut v_a_3489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shift_boxed_3490_: usize = 0;
    let mut v_res_3491_: *mut LeanObject = core::ptr::null_mut();
    v_shift_boxed_3490_ = lean_unbox_usize(v_shift_3488_);
    lean_dec(v_shift_3488_);
    v_res_3491_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_boxed_3490_, v_a_3489_);
    return v_res_3491_;
}
pub unsafe fn l_Lean_PersistentArray_mkNewPath(
    mut v_00_u03b1_3492_: *mut LeanObject,
    mut v_shift_3493_: usize,
    mut v_a_3494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    v___x_3495_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_3493_, v_a_3494_);
    return v___x_3495_;
}
pub unsafe fn l_Lean_PersistentArray_mkNewPath___boxed(
    mut v_00_u03b1_3496_: *mut LeanObject,
    mut v_shift_3497_: *mut LeanObject,
    mut v_a_3498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shift_boxed_3499_: usize = 0;
    let mut v_res_3500_: *mut LeanObject = core::ptr::null_mut();
    v_shift_boxed_3499_ = lean_unbox_usize(v_shift_3497_);
    lean_dec(v_shift_3497_);
    v_res_3500_ =
        l_Lean_PersistentArray_mkNewPath(v_00_u03b1_3496_, v_shift_boxed_3499_, v_a_3498_);
    return v_res_3500_;
}
pub unsafe fn l_Lean_PersistentArray_insertNewLeaf___redArg(
    mut v_x_3501_: *mut LeanObject,
    mut v_x_3502_: usize,
    mut v_x_3503_: usize,
    mut v_x_3504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: usize = 0;
    let mut v___x_3507_: u8 = 0;
    let mut v_j_3508_: usize = 0;
    let mut v___x_3509_: usize = 0;
    let mut v___x_3510_: usize = 0;
    let mut v___x_3511_: usize = 0;
    let mut v_shift_3512_: usize = 0;
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: u8 = 0;
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3518_: u8 = 0;
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3524_: u8 = 0;
    let mut v_unused_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v___x_3529_: usize = 0;
    let mut v_i_3530_: usize = 0;
    let mut v_v_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3539_: u8 = 0;
    let mut v_unused_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3543_: u8 = 0;
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3549_: u8 = 0;
    let mut v_unused_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3501_) == 0 {
                    v_cs_3505_ = lean_ctor_get(v_x_3501_, 0);
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
                            lean_inc_ref(v_cs_3505_);
                            lean_dec(v___x_3513_);
                            v_isSharedCheck_3524_ = (!lean_is_exclusive(v_x_3501_)) as u8;
                            if v_isSharedCheck_3524_ == 0 {
                                v_unused_3525_ = lean_ctor_get(v_x_3501_, 0);
                                lean_dec(v_unused_3525_);
                                v___x_3517_ = v_x_3501_;
                                v_isShared_3518_ = v_isSharedCheck_3524_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_x_3501_);
                                v___x_3517_ = lean_box(0);
                                v_isShared_3518_ = v_isSharedCheck_3524_;
                                state = 1;
                                continue;
                            }
                        } else {
                            if v___x_3515_ == 0 {
                                lean_dec(v___x_3513_);
                                lean_dec_ref(v_x_3504_);
                                return v_x_3501_;
                            } else {
                                lean_inc_ref(v_cs_3505_);
                                v_isSharedCheck_3539_ = (!lean_is_exclusive(v_x_3501_)) as u8;
                                if v_isSharedCheck_3539_ == 0 {
                                    v_unused_3540_ = lean_ctor_get(v_x_3501_, 0);
                                    lean_dec(v_unused_3540_);
                                    v___x_3527_ = v_x_3501_;
                                    v_isShared_3528_ = v_isSharedCheck_3539_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_x_3501_);
                                    v___x_3527_ = lean_box(0);
                                    v_isShared_3528_ = v_isSharedCheck_3539_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_inc_ref(v_cs_3505_);
                        v_isSharedCheck_3549_ = (!lean_is_exclusive(v_x_3501_)) as u8;
                        if v_isSharedCheck_3549_ == 0 {
                            v_unused_3550_ = lean_ctor_get(v_x_3501_, 0);
                            lean_dec(v_unused_3550_);
                            v___x_3542_ = v_x_3501_;
                            v_isShared_3543_ = v_isSharedCheck_3549_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v_x_3501_);
                            v___x_3542_ = lean_box(0);
                            v_isShared_3543_ = v_isSharedCheck_3549_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_x_3504_);
                    return v_x_3501_;
                }
            }
            1 => {
                v___x_3519_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_3512_, v_x_3504_);
                v___x_3520_ = lean_array_push(v_cs_3505_, v___x_3519_);
                if v_isShared_3518_ == 0 {
                    lean_ctor_set(v___x_3517_, 0, v___x_3520_);
                    v___x_3522_ = v___x_3517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3520_);
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
                v___x_3532_ = lean_box(0);
                v_xs_x27_3533_ = lean_array_fset(v_cs_3505_, v___x_3513_, v___x_3532_);
                v___x_3534_ = l_Lean_PersistentArray_insertNewLeaf___redArg(
                    v_v_3531_,
                    v_i_3530_,
                    v_shift_3512_,
                    v_x_3504_,
                );
                v___x_3535_ = lean_array_fset(v_xs_x27_3533_, v___x_3513_, v___x_3534_);
                lean_dec(v___x_3513_);
                if v_isShared_3528_ == 0 {
                    lean_ctor_set(v___x_3527_, 0, v___x_3535_);
                    v___x_3537_ = v___x_3527_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
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
                    lean_ctor_set_tag(v___x_3542_, 1);
                    lean_ctor_set(v___x_3542_, 0, v_x_3504_);
                    v___x_3545_ = v___x_3542_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_x_3504_);
                    v___x_3545_ = v_reuseFailAlloc_3548_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3546_ = lean_array_push(v_cs_3505_, v___x_3545_);
                v___x_3547_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3547_, 0, v___x_3546_);
                return v___x_3547_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_insertNewLeaf___redArg___boxed(
    mut v_x_3551_: *mut LeanObject,
    mut v_x_3552_: *mut LeanObject,
    mut v_x_3553_: *mut LeanObject,
    mut v_x_3554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_107__boxed_3555_: usize = 0;
    let mut v_x_108__boxed_3556_: usize = 0;
    let mut v_res_3557_: *mut LeanObject = core::ptr::null_mut();
    v_x_107__boxed_3555_ = lean_unbox_usize(v_x_3552_);
    lean_dec(v_x_3552_);
    v_x_108__boxed_3556_ = lean_unbox_usize(v_x_3553_);
    lean_dec(v_x_3553_);
    v_res_3557_ = l_Lean_PersistentArray_insertNewLeaf___redArg(
        v_x_3551_,
        v_x_107__boxed_3555_,
        v_x_108__boxed_3556_,
        v_x_3554_,
    );
    return v_res_3557_;
}
pub unsafe fn l_Lean_PersistentArray_insertNewLeaf(
    mut v_00_u03b1_3558_: *mut LeanObject,
    mut v_x_3559_: *mut LeanObject,
    mut v_x_3560_: usize,
    mut v_x_3561_: usize,
    mut v_x_3562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    v___x_3563_ =
        l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_3559_, v_x_3560_, v_x_3561_, v_x_3562_);
    return v___x_3563_;
}
pub unsafe fn l_Lean_PersistentArray_insertNewLeaf___boxed(
    mut v_00_u03b1_3564_: *mut LeanObject,
    mut v_x_3565_: *mut LeanObject,
    mut v_x_3566_: *mut LeanObject,
    mut v_x_3567_: *mut LeanObject,
    mut v_x_3568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_201__boxed_3569_: usize = 0;
    let mut v_x_202__boxed_3570_: usize = 0;
    let mut v_res_3571_: *mut LeanObject = core::ptr::null_mut();
    v_x_201__boxed_3569_ = lean_unbox_usize(v_x_3566_);
    lean_dec(v_x_3566_);
    v_x_202__boxed_3570_ = lean_unbox_usize(v_x_3567_);
    lean_dec(v_x_3567_);
    v_res_3571_ = l_Lean_PersistentArray_insertNewLeaf(
        v_00_u03b1_3564_,
        v_x_3565_,
        v_x_201__boxed_3569_,
        v_x_202__boxed_3570_,
        v_x_3568_,
    );
    return v_res_3571_;
}
pub unsafe fn _init_l_Lean_PersistentArray_mkNewTail___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    v___x_3574_ = l_Lean_PersistentArray_mkEmptyArray(lean_box(0));
    return v___x_3574_;
}
pub unsafe fn l_Lean_PersistentArray_mkNewTail___redArg(
    mut v_t_3575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_3579_: usize = 0;
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3582_: u8 = 0;
    let mut v___x_3583_: usize = 0;
    let mut v___x_3584_: usize = 0;
    let mut v___x_3585_: usize = 0;
    let mut v___x_3586_: usize = 0;
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: u8 = 0;
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: usize = 0;
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3606_: u8 = 0;
    let mut v_unused_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3576_ = lean_ctor_get(v_t_3575_, 0);
                v_tail_3577_ = lean_ctor_get(v_t_3575_, 1);
                v_size_3578_ = lean_ctor_get(v_t_3575_, 2);
                v_shift_3579_ = lean_ctor_get_usize(v_t_3575_, 4);
                v_isSharedCheck_3606_ = (!lean_is_exclusive(v_t_3575_)) as u8;
                if v_isSharedCheck_3606_ == 0 {
                    v_unused_3607_ = lean_ctor_get(v_t_3575_, 3);
                    lean_dec(v_unused_3607_);
                    v___x_3581_ = v_t_3575_;
                    v_isShared_3582_ = v_isSharedCheck_3606_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_size_3578_);
                    lean_inc(v_tail_3577_);
                    lean_inc(v_root_3576_);
                    lean_dec(v_t_3575_);
                    v___x_3581_ = lean_box(0);
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
                lean_dec(v___x_3587_);
                if v___x_3588_ == 0 {
                    v___x_3589_ = lean_obj_once(
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
                    v___x_3593_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3593_, 0, v___x_3592_);
                    v___x_3594_ = l_Lean_PersistentArray_mkNewTail___redArg___closed__0;
                    lean_inc(v_size_3578_);
                    if v_isShared_3582_ == 0 {
                        lean_ctor_set(v___x_3581_, 3, v_size_3578_);
                        lean_ctor_set(v___x_3581_, 1, v___x_3594_);
                        lean_ctor_set(v___x_3581_, 0, v___x_3593_);
                        v___x_3596_ = v___x_3581_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3597_ =
                            lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3593_);
                        lean_ctor_set(v_reuseFailAlloc_3597_, 1, v___x_3594_);
                        lean_ctor_set(v_reuseFailAlloc_3597_, 2, v_size_3578_);
                        lean_ctor_set(v_reuseFailAlloc_3597_, 3, v_size_3578_);
                        v___x_3596_ = v_reuseFailAlloc_3597_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3598_ = lean_unsigned_to_nat(1);
                    v___x_3599_ = lean_nat_sub(v_size_3578_, v___x_3598_);
                    v___x_3600_ = lean_usize_of_nat(v___x_3599_);
                    lean_dec(v___x_3599_);
                    v___x_3601_ = l_Lean_PersistentArray_insertNewLeaf___redArg(
                        v_root_3576_,
                        v___x_3600_,
                        v_shift_3579_,
                        v_tail_3577_,
                    );
                    v___x_3602_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentArray_mkNewTail___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentArray_mkNewTail___redArg___closed__1_once
                        ),
                        _init_l_Lean_PersistentArray_mkNewTail___redArg___closed__1,
                    );
                    lean_inc(v_size_3578_);
                    if v_isShared_3582_ == 0 {
                        lean_ctor_set(v___x_3581_, 3, v_size_3578_);
                        lean_ctor_set(v___x_3581_, 1, v___x_3602_);
                        lean_ctor_set(v___x_3581_, 0, v___x_3601_);
                        v___x_3604_ = v___x_3581_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3605_ =
                            lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3601_);
                        lean_ctor_set(v_reuseFailAlloc_3605_, 1, v___x_3602_);
                        lean_ctor_set(v_reuseFailAlloc_3605_, 2, v_size_3578_);
                        lean_ctor_set(v_reuseFailAlloc_3605_, 3, v_size_3578_);
                        lean_ctor_set_usize(v_reuseFailAlloc_3605_, 4, v_shift_3579_);
                        v___x_3604_ = v_reuseFailAlloc_3605_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_usize(v___x_3596_, 4, v___x_3585_);
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
    mut v_00_u03b1_3608_: *mut LeanObject,
    mut v_t_3609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    v___x_3610_ = l_Lean_PersistentArray_mkNewTail___redArg(v_t_3609_);
    return v___x_3610_;
}
pub unsafe fn _init_l_Lean_PersistentArray_tooBig___closed__0() -> *mut LeanObject {
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    v___x_3611_ = l_System_Platform_numBits;
    v___x_3612_ = lean_unsigned_to_nat(2);
    v___x_3613_ = lean_nat_pow(v___x_3612_, v___x_3611_);
    return v___x_3613_;
}
pub unsafe fn _init_l_Lean_PersistentArray_tooBig___closed__1() -> *mut LeanObject {
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    v___x_3614_ = lean_unsigned_to_nat(3);
    v___x_3615_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PersistentArray_tooBig___closed__0),
        core::ptr::addr_of_mut!(l_Lean_PersistentArray_tooBig___closed__0_once),
        _init_l_Lean_PersistentArray_tooBig___closed__0,
    );
    v___x_3616_ = lean_nat_shiftr(v___x_3615_, v___x_3614_);
    return v___x_3616_;
}
pub unsafe fn _init_l_Lean_PersistentArray_tooBig() -> *mut LeanObject {
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    v___x_3617_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PersistentArray_tooBig___closed__1),
        core::ptr::addr_of_mut!(l_Lean_PersistentArray_tooBig___closed__1_once),
        _init_l_Lean_PersistentArray_tooBig___closed__1,
    );
    return v___x_3617_;
}
pub unsafe fn l_Lean_PersistentArray_push___redArg(
    mut v_t_3618_: *mut LeanObject,
    mut v_a_3619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_3623_: usize = 0;
    let mut v_tailOff_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3627_: u8 = 0;
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3634_: u8 = 0;
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: u8 = 0;
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: u8 = 0;
    let mut v_reuseFailAlloc_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3620_ = lean_ctor_get(v_t_3618_, 0);
                v_tail_3621_ = lean_ctor_get(v_t_3618_, 1);
                v_size_3622_ = lean_ctor_get(v_t_3618_, 2);
                v_shift_3623_ = lean_ctor_get_usize(v_t_3618_, 4);
                v_tailOff_3624_ = lean_ctor_get(v_t_3618_, 3);
                v_isSharedCheck_3642_ = (!lean_is_exclusive(v_t_3618_)) as u8;
                if v_isSharedCheck_3642_ == 0 {
                    v___x_3626_ = v_t_3618_;
                    v_isShared_3627_ = v_isSharedCheck_3642_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tailOff_3624_);
                    lean_inc(v_size_3622_);
                    lean_inc(v_tail_3621_);
                    lean_inc(v_root_3620_);
                    lean_dec(v_t_3618_);
                    v___x_3626_ = lean_box(0);
                    v_isShared_3627_ = v_isSharedCheck_3642_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3628_ = lean_array_push(v_tail_3621_, v_a_3619_);
                v___x_3629_ = lean_unsigned_to_nat(1);
                v___x_3630_ = lean_nat_add(v_size_3622_, v___x_3629_);
                lean_inc_ref(v___x_3628_);
                if v_isShared_3627_ == 0 {
                    lean_ctor_set(v___x_3626_, 2, v___x_3630_);
                    lean_ctor_set(v___x_3626_, 1, v___x_3628_);
                    v_r_3632_ = v___x_3626_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3641_ =
                        lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_root_3620_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 1, v___x_3628_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 2, v___x_3630_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 3, v_tailOff_3624_);
                    lean_ctor_set_usize(v_reuseFailAlloc_3641_, 4, v_shift_3623_);
                    v_r_3632_ = v_reuseFailAlloc_3641_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3636_ = lean_array_get_size(v___x_3628_);
                lean_dec_ref(v___x_3628_);
                v___x_3637_ = lean_unsigned_to_nat(32);
                v___x_3638_ = lean_nat_dec_lt(v___x_3636_, v___x_3637_);
                if v___x_3638_ == 0 {
                    v___x_3639_ = l_Lean_PersistentArray_tooBig;
                    v___x_3640_ = lean_nat_dec_le(v___x_3639_, v_size_3622_);
                    lean_dec(v_size_3622_);
                    v___y_3634_ = v___x_3640_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_size_3622_);
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
    mut v_00_u03b1_3643_: *mut LeanObject,
    mut v_t_3644_: *mut LeanObject,
    mut v_a_3645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    v___x_3646_ = l_Lean_PersistentArray_push___redArg(v_t_3644_, v_a_3645_);
    return v___x_3646_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(
    mut v_00_u03b1_3647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    v___x_3648_ = lean_unsigned_to_nat(32);
    v___x_3649_ = lean_mk_empty_array_with_capacity(v___x_3648_);
    return v___x_3649_;
}
pub unsafe fn _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    v___x_3650_ =
        l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(lean_box(0));
    return v___x_3650_;
}
pub unsafe fn _init_l_Lean_PersistentArray_popLeaf___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    v___x_3651_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PersistentArray_popLeaf___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_PersistentArray_popLeaf___redArg___closed__0_once),
        _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0,
    );
    v___x_3652_ = lean_box(0);
    v___x_3653_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3653_, 0, v___x_3652_);
    lean_ctor_set(v___x_3653_, 1, v___x_3651_);
    return v___x_3653_;
}
pub unsafe fn l_Lean_PersistentArray_popLeaf___redArg(
    mut v_x_3654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3658_: u8 = 0;
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: u8 = 0;
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_last_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3669_: u8 = 0;
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3674_: u8 = 0;
    let mut v_unused_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3680_: u8 = 0;
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cs_x27_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: u8 = 0;
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cs_x27_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: u8 = 0;
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3702_: u8 = 0;
    let mut v_unused_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3705_: u8 = 0;
    let mut v_vs_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3654_) == 0 {
                    v_cs_3655_ = lean_ctor_get(v_x_3654_, 0);
                    v_isSharedCheck_3705_ = (!lean_is_exclusive(v_x_3654_)) as u8;
                    if v_isSharedCheck_3705_ == 0 {
                        v___x_3657_ = v_x_3654_;
                        v_isShared_3658_ = v_isSharedCheck_3705_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_3655_);
                        lean_dec(v_x_3654_);
                        v___x_3657_ = lean_box(0);
                        v_isShared_3658_ = v_isSharedCheck_3705_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_3706_ = lean_ctor_get(v_x_3654_, 0);
                    lean_inc_ref(v_vs_3706_);
                    lean_dec_ref_known(v_x_3654_, 1);
                    v___x_3707_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3707_, 0, v_vs_3706_);
                    v___x_3708_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentArray_popLeaf___redArg___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PersistentArray_popLeaf___redArg___closed__0_once
                        ),
                        _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0,
                    );
                    v___x_3709_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3709_, 0, v___x_3707_);
                    lean_ctor_set(v___x_3709_, 1, v___x_3708_);
                    return v___x_3709_;
                }
            }
            1 => {
                v___x_3659_ = lean_array_get_size(v_cs_3655_);
                v___x_3660_ = lean_unsigned_to_nat(0);
                v___x_3661_ = lean_nat_dec_eq(v___x_3659_, v___x_3660_);
                if v___x_3661_ == 0 {
                    v___x_3662_ = lean_unsigned_to_nat(1);
                    v_idx_3663_ = lean_nat_sub(v___x_3659_, v___x_3662_);
                    v_last_3664_ = lean_array_fget_borrowed(v_cs_3655_, v_idx_3663_);
                    lean_inc(v_last_3664_);
                    v___x_3665_ = l_Lean_PersistentArray_popLeaf___redArg(v_last_3664_);
                    v_fst_3666_ = lean_ctor_get(v___x_3665_, 0);
                    lean_inc(v_fst_3666_);
                    if lean_obj_tag(v_fst_3666_) == 0 {
                        lean_dec(v_idx_3663_);
                        lean_del_object(v___x_3657_);
                        lean_dec_ref(v_cs_3655_);
                        v_isSharedCheck_3674_ = (!lean_is_exclusive(v___x_3665_)) as u8;
                        if v_isSharedCheck_3674_ == 0 {
                            v_unused_3675_ = lean_ctor_get(v___x_3665_, 1);
                            lean_dec(v_unused_3675_);
                            v_unused_3676_ = lean_ctor_get(v___x_3665_, 0);
                            lean_dec(v_unused_3676_);
                            v___x_3668_ = v___x_3665_;
                            v_isShared_3669_ = v_isSharedCheck_3674_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_3665_);
                            v___x_3668_ = lean_box(0);
                            v_isShared_3669_ = v_isSharedCheck_3674_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_3677_ = lean_ctor_get(v___x_3665_, 1);
                        v_isSharedCheck_3702_ = (!lean_is_exclusive(v___x_3665_)) as u8;
                        if v_isSharedCheck_3702_ == 0 {
                            v_unused_3703_ = lean_ctor_get(v___x_3665_, 0);
                            lean_dec(v_unused_3703_);
                            v___x_3679_ = v___x_3665_;
                            v_isShared_3680_ = v_isSharedCheck_3702_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_snd_3677_);
                            lean_dec(v___x_3665_);
                            v___x_3679_ = lean_box(0);
                            v_isShared_3680_ = v_isSharedCheck_3702_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3657_);
                    lean_dec_ref(v_cs_3655_);
                    v___x_3704_ = lean_obj_once(
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
                v___x_3670_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PersistentArray_popLeaf___redArg___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_PersistentArray_popLeaf___redArg___closed__0_once
                    ),
                    _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0,
                );
                if v_isShared_3669_ == 0 {
                    lean_ctor_set(v___x_3668_, 1, v___x_3670_);
                    v___x_3672_ = v___x_3668_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_fst_3666_);
                    lean_ctor_set(v_reuseFailAlloc_3673_, 1, v___x_3670_);
                    v___x_3672_ = v_reuseFailAlloc_3673_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3672_;
            }
            4 => {
                v___x_3681_ = lean_obj_once(
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
                        lean_ctor_set(v___x_3657_, 0, v_snd_3677_);
                        v___x_3686_ = v___x_3657_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_snd_3677_);
                        v___x_3686_ = v_reuseFailAlloc_3691_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_3677_);
                    lean_dec(v_idx_3663_);
                    lean_del_object(v___x_3657_);
                    v_cs_x27_3692_ = lean_array_pop(v_cs_x27_3682_);
                    v___x_3693_ = lean_array_get_size(v_cs_x27_3692_);
                    v___x_3694_ = lean_nat_dec_eq(v___x_3693_, v___x_3660_);
                    if v___x_3694_ == 0 {
                        if v_isShared_3680_ == 0 {
                            lean_ctor_set(v___x_3679_, 1, v_cs_x27_3692_);
                            v___x_3696_ = v___x_3679_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_fst_3666_);
                            lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_cs_x27_3692_);
                            v___x_3696_ = v_reuseFailAlloc_3697_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_cs_x27_3692_);
                        v___x_3698_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_PersistentArray_popLeaf___redArg___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_PersistentArray_popLeaf___redArg___closed__0_once
                            ),
                            _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0,
                        );
                        if v_isShared_3680_ == 0 {
                            lean_ctor_set(v___x_3679_, 1, v___x_3698_);
                            v___x_3700_ = v___x_3679_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_fst_3666_);
                            lean_ctor_set(v_reuseFailAlloc_3701_, 1, v___x_3698_);
                            v___x_3700_ = v_reuseFailAlloc_3701_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_3687_ = lean_array_fset(v_cs_x27_3682_, v_idx_3663_, v___x_3686_);
                lean_dec(v_idx_3663_);
                if v_isShared_3680_ == 0 {
                    lean_ctor_set(v___x_3679_, 1, v___x_3687_);
                    v___x_3689_ = v___x_3679_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_fst_3666_);
                    lean_ctor_set(v_reuseFailAlloc_3690_, 1, v___x_3687_);
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
    mut v_00_u03b1_3710_: *mut LeanObject,
    mut v_x_3711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    v___x_3712_ = l_Lean_PersistentArray_popLeaf___redArg(v_x_3711_);
    return v___x_3712_;
}
pub unsafe fn l_Lean_PersistentArray_pop___redArg(
    mut v_t_3713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_3717_: usize = 0;
    let mut v_tailOff_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: u8 = 0;
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3726_: u8 = 0;
    let mut v_snd_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3731_: u8 = 0;
    let mut v_last_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newSize_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newTailOff_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3738_: u8 = 0;
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: usize = 0;
    let mut v___x_3747_: usize = 0;
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: u8 = 0;
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: u8 = 0;
    let mut v_isSharedCheck_3755_: u8 = 0;
    let mut v_isSharedCheck_3756_: u8 = 0;
    let mut v_unused_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3763_: u8 = 0;
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v_unused_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3714_ = lean_ctor_get(v_t_3713_, 0);
                v_tail_3715_ = lean_ctor_get(v_t_3713_, 1);
                v_size_3716_ = lean_ctor_get(v_t_3713_, 2);
                v_shift_3717_ = lean_ctor_get_usize(v_t_3713_, 4);
                v_tailOff_3718_ = lean_ctor_get(v_t_3713_, 3);
                v___x_3719_ = lean_unsigned_to_nat(0);
                v___x_3720_ = lean_array_get_size(v_tail_3715_);
                v___x_3721_ = lean_nat_dec_lt(v___x_3719_, v___x_3720_);
                if v___x_3721_ == 0 {
                    lean_inc_ref(v_root_3714_);
                    v___x_3722_ = l_Lean_PersistentArray_popLeaf___redArg(v_root_3714_);
                    v_fst_3723_ = lean_ctor_get(v___x_3722_, 0);
                    lean_inc(v_fst_3723_);
                    if lean_obj_tag(v_fst_3723_) == 0 {
                        lean_dec_ref(v___x_3722_);
                        return v_t_3713_;
                    } else {
                        lean_inc(v_size_3716_);
                        v_isSharedCheck_3756_ = (!lean_is_exclusive(v_t_3713_)) as u8;
                        if v_isSharedCheck_3756_ == 0 {
                            v_unused_3757_ = lean_ctor_get(v_t_3713_, 3);
                            lean_dec(v_unused_3757_);
                            v_unused_3758_ = lean_ctor_get(v_t_3713_, 2);
                            lean_dec(v_unused_3758_);
                            v_unused_3759_ = lean_ctor_get(v_t_3713_, 1);
                            lean_dec(v_unused_3759_);
                            v_unused_3760_ = lean_ctor_get(v_t_3713_, 0);
                            lean_dec(v_unused_3760_);
                            v___x_3725_ = v_t_3713_;
                            v_isShared_3726_ = v_isSharedCheck_3756_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_t_3713_);
                            v___x_3725_ = lean_box(0);
                            v_isShared_3726_ = v_isSharedCheck_3756_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_tailOff_3718_);
                    lean_inc(v_size_3716_);
                    lean_inc_ref(v_tail_3715_);
                    lean_inc_ref(v_root_3714_);
                    v_isSharedCheck_3770_ = (!lean_is_exclusive(v_t_3713_)) as u8;
                    if v_isSharedCheck_3770_ == 0 {
                        v_unused_3771_ = lean_ctor_get(v_t_3713_, 3);
                        lean_dec(v_unused_3771_);
                        v_unused_3772_ = lean_ctor_get(v_t_3713_, 2);
                        lean_dec(v_unused_3772_);
                        v_unused_3773_ = lean_ctor_get(v_t_3713_, 1);
                        lean_dec(v_unused_3773_);
                        v_unused_3774_ = lean_ctor_get(v_t_3713_, 0);
                        lean_dec(v_unused_3774_);
                        v___x_3762_ = v_t_3713_;
                        v_isShared_3763_ = v_isSharedCheck_3770_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v_t_3713_);
                        v___x_3762_ = lean_box(0);
                        v_isShared_3763_ = v_isSharedCheck_3770_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3727_ = lean_ctor_get(v___x_3722_, 1);
                lean_inc(v_snd_3727_);
                lean_dec_ref(v___x_3722_);
                v_val_3728_ = lean_ctor_get(v_fst_3723_, 0);
                v_isSharedCheck_3755_ = (!lean_is_exclusive(v_fst_3723_)) as u8;
                if v_isSharedCheck_3755_ == 0 {
                    v___x_3730_ = v_fst_3723_;
                    v_isShared_3731_ = v_isSharedCheck_3755_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_val_3728_);
                    lean_dec(v_fst_3723_);
                    v___x_3730_ = lean_box(0);
                    v_isShared_3731_ = v_isSharedCheck_3755_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_last_3732_ = lean_array_pop(v_val_3728_);
                v___x_3733_ = lean_unsigned_to_nat(1);
                v_newSize_3734_ = lean_nat_sub(v_size_3716_, v___x_3733_);
                lean_dec(v_size_3716_);
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
                        lean_ctor_set_tag(v___x_3730_, 0);
                        lean_ctor_set(v___x_3730_, 0, v_snd_3727_);
                        v___x_3740_ = v___x_3730_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_snd_3727_);
                        v___x_3740_ = v_reuseFailAlloc_3744_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3730_);
                    v___x_3745_ = lean_array_fget(v_snd_3727_, v___x_3719_);
                    lean_dec(v_snd_3727_);
                    v___x_3746_ = 5usize;
                    v___x_3747_ = lean_usize_sub(v_shift_3717_, v___x_3746_);
                    if v_isShared_3726_ == 0 {
                        lean_ctor_set(v___x_3725_, 3, v_newTailOff_3736_);
                        lean_ctor_set(v___x_3725_, 2, v_newSize_3734_);
                        lean_ctor_set(v___x_3725_, 1, v_last_3732_);
                        lean_ctor_set(v___x_3725_, 0, v___x_3745_);
                        v___x_3749_ = v___x_3725_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3750_ =
                            lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3745_);
                        lean_ctor_set(v_reuseFailAlloc_3750_, 1, v_last_3732_);
                        lean_ctor_set(v_reuseFailAlloc_3750_, 2, v_newSize_3734_);
                        lean_ctor_set(v_reuseFailAlloc_3750_, 3, v_newTailOff_3736_);
                        v___x_3749_ = v_reuseFailAlloc_3750_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3726_ == 0 {
                    lean_ctor_set(v___x_3725_, 3, v_newTailOff_3736_);
                    lean_ctor_set(v___x_3725_, 2, v_newSize_3734_);
                    lean_ctor_set(v___x_3725_, 1, v_last_3732_);
                    lean_ctor_set(v___x_3725_, 0, v___x_3740_);
                    v___x_3742_ = v___x_3725_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3743_ =
                        lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3740_);
                    lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_last_3732_);
                    lean_ctor_set(v_reuseFailAlloc_3743_, 2, v_newSize_3734_);
                    lean_ctor_set(v_reuseFailAlloc_3743_, 3, v_newTailOff_3736_);
                    lean_ctor_set_usize(v_reuseFailAlloc_3743_, 4, v_shift_3717_);
                    v___x_3742_ = v_reuseFailAlloc_3743_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3742_;
            }
            6 => {
                lean_ctor_set_usize(v___x_3749_, 4, v___x_3747_);
                return v___x_3749_;
            }
            7 => {
                v___x_3764_ = lean_array_pop(v_tail_3715_);
                v___x_3765_ = lean_unsigned_to_nat(1);
                v___x_3766_ = lean_nat_sub(v_size_3716_, v___x_3765_);
                lean_dec(v_size_3716_);
                if v_isShared_3763_ == 0 {
                    lean_ctor_set(v___x_3762_, 2, v___x_3766_);
                    lean_ctor_set(v___x_3762_, 1, v___x_3764_);
                    v___x_3768_ = v___x_3762_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3769_ =
                        lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_root_3714_);
                    lean_ctor_set(v_reuseFailAlloc_3769_, 1, v___x_3764_);
                    lean_ctor_set(v_reuseFailAlloc_3769_, 2, v___x_3766_);
                    lean_ctor_set(v_reuseFailAlloc_3769_, 3, v_tailOff_3718_);
                    lean_ctor_set_usize(v_reuseFailAlloc_3769_, 4, v_shift_3717_);
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
    mut v_00_u03b1_3775_: *mut LeanObject,
    mut v_t_3776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    v___x_3777_ = l_Lean_PersistentArray_pop___redArg(v_t_3776_);
    return v___x_3777_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(
    mut v_inst_3778_: *mut LeanObject,
    mut v_f_3779_: *mut LeanObject,
    mut v_x_3780_: *mut LeanObject,
    mut v_x_3781_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3780_) == 0 {
        let mut v_cs_3782_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3785_: u8 = 0;
        v_cs_3782_ = lean_ctor_get(v_x_3780_, 0);
        lean_inc_ref(v_cs_3782_);
        lean_dec_ref_known(v_x_3780_, 1);
        v___x_3783_ = lean_unsigned_to_nat(0);
        v___x_3784_ = lean_array_get_size(v_cs_3782_);
        v___x_3785_ = lean_nat_dec_lt(v___x_3783_, v___x_3784_);
        if v___x_3785_ == 0 {
            let mut v_toApplicative_3786_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_3787_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_cs_3782_);
            lean_dec(v_f_3779_);
            v_toApplicative_3786_ = lean_ctor_get(v_inst_3778_, 0);
            lean_inc_ref(v_toApplicative_3786_);
            lean_dec_ref(v_inst_3778_);
            v_toPure_3787_ = lean_ctor_get(v_toApplicative_3786_, 1);
            lean_inc(v_toPure_3787_);
            lean_dec_ref(v_toApplicative_3786_);
            v___x_3788_ = lean_apply_2(v_toPure_3787_, lean_box(0), v_x_3781_);
            return v___x_3788_;
        } else {
            let mut v___f_3789_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3790_: u8 = 0;
            lean_inc_ref(v_inst_3778_);
            v___f_3789_ = lean_alloc_closure(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0 as *mut core::ffi::c_void, 4, 2);
            lean_closure_set(v___f_3789_, 0, v_inst_3778_);
            lean_closure_set(v___f_3789_, 1, v_f_3779_);
            v___x_3790_ = lean_nat_dec_le(v___x_3784_, v___x_3784_);
            if v___x_3790_ == 0 {
                if v___x_3785_ == 0 {
                    let mut v_toApplicative_3791_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_toPure_3792_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v___f_3789_);
                    lean_dec_ref(v_cs_3782_);
                    v_toApplicative_3791_ = lean_ctor_get(v_inst_3778_, 0);
                    lean_inc_ref(v_toApplicative_3791_);
                    lean_dec_ref(v_inst_3778_);
                    v_toPure_3792_ = lean_ctor_get(v_toApplicative_3791_, 1);
                    lean_inc(v_toPure_3792_);
                    lean_dec_ref(v_toApplicative_3791_);
                    v___x_3793_ = lean_apply_2(v_toPure_3792_, lean_box(0), v_x_3781_);
                    return v___x_3793_;
                } else {
                    let mut v___x_3794_: usize = 0;
                    let mut v___x_3795_: usize = 0;
                    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
                    v___x_3794_ = 0usize;
                    v___x_3795_ = lean_usize_of_nat(v___x_3784_);
                    v___x_3796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
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
                let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
                v___x_3797_ = 0usize;
                v___x_3798_ = lean_usize_of_nat(v___x_3784_);
                v___x_3799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
        let mut v_vs_3800_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3803_: u8 = 0;
        v_vs_3800_ = lean_ctor_get(v_x_3780_, 0);
        lean_inc_ref(v_vs_3800_);
        lean_dec_ref_known(v_x_3780_, 1);
        v___x_3801_ = lean_unsigned_to_nat(0);
        v___x_3802_ = lean_array_get_size(v_vs_3800_);
        v___x_3803_ = lean_nat_dec_lt(v___x_3801_, v___x_3802_);
        if v___x_3803_ == 0 {
            let mut v_toApplicative_3804_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_3805_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_vs_3800_);
            lean_dec(v_f_3779_);
            v_toApplicative_3804_ = lean_ctor_get(v_inst_3778_, 0);
            lean_inc_ref(v_toApplicative_3804_);
            lean_dec_ref(v_inst_3778_);
            v_toPure_3805_ = lean_ctor_get(v_toApplicative_3804_, 1);
            lean_inc(v_toPure_3805_);
            lean_dec_ref(v_toApplicative_3804_);
            v___x_3806_ = lean_apply_2(v_toPure_3805_, lean_box(0), v_x_3781_);
            return v___x_3806_;
        } else {
            let mut v___x_3807_: u8 = 0;
            v___x_3807_ = lean_nat_dec_le(v___x_3802_, v___x_3802_);
            if v___x_3807_ == 0 {
                if v___x_3803_ == 0 {
                    let mut v_toApplicative_3808_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_toPure_3809_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v_vs_3800_);
                    lean_dec(v_f_3779_);
                    v_toApplicative_3808_ = lean_ctor_get(v_inst_3778_, 0);
                    lean_inc_ref(v_toApplicative_3808_);
                    lean_dec_ref(v_inst_3778_);
                    v_toPure_3809_ = lean_ctor_get(v_toApplicative_3808_, 1);
                    lean_inc(v_toPure_3809_);
                    lean_dec_ref(v_toApplicative_3808_);
                    v___x_3810_ = lean_apply_2(v_toPure_3809_, lean_box(0), v_x_3781_);
                    return v___x_3810_;
                } else {
                    let mut v___x_3811_: usize = 0;
                    let mut v___x_3812_: usize = 0;
                    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
                    v___x_3811_ = 0usize;
                    v___x_3812_ = lean_usize_of_nat(v___x_3802_);
                    v___x_3813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
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
                let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
                v___x_3814_ = 0usize;
                v___x_3815_ = lean_usize_of_nat(v___x_3802_);
                v___x_3816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_3817_: *mut LeanObject,
    mut v_f_3818_: *mut LeanObject,
    mut v_b_3819_: *mut LeanObject,
    mut v_c_3820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    v___x_3821_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(
        v_inst_3817_,
        v_f_3818_,
        v_c_3820_,
        v_b_3819_,
    );
    return v___x_3821_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux(
    mut v_00_u03b1_3822_: *mut LeanObject,
    mut v_m_3823_: *mut LeanObject,
    mut v_inst_3824_: *mut LeanObject,
    mut v_00_u03b2_3825_: *mut LeanObject,
    mut v_f_3826_: *mut LeanObject,
    mut v_x_3827_: *mut LeanObject,
    mut v_x_3828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    v___x_3829_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(
        v_inst_3824_,
        v_f_3826_,
        v_x_3827_,
        v_x_3828_,
    );
    return v___x_3829_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(
    mut v_j_3830_: *mut LeanObject,
    mut v_cs_3831_: *mut LeanObject,
    mut v_toApplicative_3832_: *mut LeanObject,
    mut v_inst_3833_: *mut LeanObject,
    mut v___f_3834_: *mut LeanObject,
    mut v_b_3835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: u8 = 0;
    v___x_3836_ = lean_unsigned_to_nat(1);
    v___x_3837_ = lean_nat_add(v_j_3830_, v___x_3836_);
    v___x_3838_ = lean_array_get_size(v_cs_3831_);
    v___x_3839_ = lean_nat_dec_lt(v___x_3837_, v___x_3838_);
    if v___x_3839_ == 0 {
        let mut v_toPure_3840_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_3837_);
        lean_dec(v___f_3834_);
        lean_dec_ref(v_inst_3833_);
        lean_dec_ref(v_cs_3831_);
        v_toPure_3840_ = lean_ctor_get(v_toApplicative_3832_, 1);
        lean_inc(v_toPure_3840_);
        lean_dec_ref(v_toApplicative_3832_);
        v___x_3841_ = lean_apply_2(v_toPure_3840_, lean_box(0), v_b_3835_);
        return v___x_3841_;
    } else {
        let mut v___x_3842_: u8 = 0;
        v___x_3842_ = lean_nat_dec_le(v___x_3838_, v___x_3838_);
        if v___x_3842_ == 0 {
            if v___x_3839_ == 0 {
                let mut v_toPure_3843_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_3837_);
                lean_dec(v___f_3834_);
                lean_dec_ref(v_inst_3833_);
                lean_dec_ref(v_cs_3831_);
                v_toPure_3843_ = lean_ctor_get(v_toApplicative_3832_, 1);
                lean_inc(v_toPure_3843_);
                lean_dec_ref(v_toApplicative_3832_);
                v___x_3844_ = lean_apply_2(v_toPure_3843_, lean_box(0), v_b_3835_);
                return v___x_3844_;
            } else {
                let mut v___x_3845_: usize = 0;
                let mut v___x_3846_: usize = 0;
                let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toApplicative_3832_);
                v___x_3845_ = lean_usize_of_nat(v___x_3837_);
                lean_dec(v___x_3837_);
                v___x_3846_ = lean_usize_of_nat(v___x_3838_);
                v___x_3847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_toApplicative_3832_);
            v___x_3848_ = lean_usize_of_nat(v___x_3837_);
            lean_dec(v___x_3837_);
            v___x_3849_ = lean_usize_of_nat(v___x_3838_);
            v___x_3850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_j_3851_: *mut LeanObject,
    mut v_cs_3852_: *mut LeanObject,
    mut v_toApplicative_3853_: *mut LeanObject,
    mut v_inst_3854_: *mut LeanObject,
    mut v___f_3855_: *mut LeanObject,
    mut v_b_3856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3857_: *mut LeanObject = core::ptr::null_mut();
    v_res_3857_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(v_j_3851_, v_cs_3852_, v_toApplicative_3853_, v_inst_3854_, v___f_3855_, v_b_3856_);
    lean_dec(v_j_3851_);
    return v_res_3857_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(
    mut v_inst_3858_: *mut LeanObject,
    mut v_f_3859_: *mut LeanObject,
    mut v_x_3860_: *mut LeanObject,
    mut v_x_3861_: usize,
    mut v_x_3862_: usize,
    mut v_x_3863_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3860_) == 0 {
        let mut v_toApplicative_3864_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_3865_: *mut LeanObject = core::ptr::null_mut();
        let mut v_cs_3866_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3867_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3869_: usize = 0;
        let mut v_j_3870_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3873_: usize = 0;
        let mut v___x_3874_: usize = 0;
        let mut v___x_3875_: usize = 0;
        let mut v___x_3876_: usize = 0;
        let mut v___x_3877_: usize = 0;
        let mut v___x_3878_: usize = 0;
        let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_3864_ = lean_ctor_get(v_inst_3858_, 0);
        v_toBind_3865_ = lean_ctor_get(v_inst_3858_, 1);
        lean_inc(v_toBind_3865_);
        v_cs_3866_ = lean_ctor_get(v_x_3860_, 0);
        lean_inc_ref_n(v_cs_3866_, 2);
        lean_dec_ref_known(v_x_3860_, 1);
        lean_inc(v_f_3859_);
        lean_inc_ref_n(v_inst_3858_, 2);
        v___f_3867_ = lean_alloc_closure(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0 as *mut core::ffi::c_void, 4, 2);
        lean_closure_set(v___f_3867_, 0, v_inst_3858_);
        lean_closure_set(v___f_3867_, 1, v_f_3859_);
        v___x_3868_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0),
            core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0_once),
            _init_l_Lean_instInhabitedPersistentArrayNode___closed__0,
        );
        v___x_3869_ = lean_usize_shift_right(v_x_3861_, v_x_3862_);
        v_j_3870_ = lean_usize_to_nat(v___x_3869_);
        lean_inc_ref(v_toApplicative_3864_);
        lean_inc(v_j_3870_);
        v___f_3871_ = lean_alloc_closure(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 5);
        lean_closure_set(v___f_3871_, 0, v_j_3870_);
        lean_closure_set(v___f_3871_, 1, v_cs_3866_);
        lean_closure_set(v___f_3871_, 2, v_toApplicative_3864_);
        lean_closure_set(v___f_3871_, 3, v_inst_3858_);
        lean_closure_set(v___f_3871_, 4, v___f_3867_);
        v___x_3872_ = lean_array_get(v___x_3868_, v_cs_3866_, v_j_3870_);
        lean_dec(v_j_3870_);
        lean_dec_ref(v_cs_3866_);
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
        v___x_3880_ = lean_apply_4(
            v_toBind_3865_,
            lean_box(0),
            lean_box(0),
            v___x_3879_,
            v___f_3871_,
        );
        return v___x_3880_;
    } else {
        let mut v_toApplicative_3881_: *mut LeanObject = core::ptr::null_mut();
        let mut v_vs_3882_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3885_: u8 = 0;
        v_toApplicative_3881_ = lean_ctor_get(v_inst_3858_, 0);
        v_vs_3882_ = lean_ctor_get(v_x_3860_, 0);
        lean_inc_ref(v_vs_3882_);
        lean_dec_ref_known(v_x_3860_, 1);
        v___x_3883_ = lean_usize_to_nat(v_x_3861_);
        v___x_3884_ = lean_array_get_size(v_vs_3882_);
        v___x_3885_ = lean_nat_dec_lt(v___x_3883_, v___x_3884_);
        if v___x_3885_ == 0 {
            let mut v_toPure_3886_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_toApplicative_3881_);
            lean_dec(v___x_3883_);
            lean_dec_ref(v_vs_3882_);
            lean_dec(v_f_3859_);
            lean_dec_ref(v_inst_3858_);
            v_toPure_3886_ = lean_ctor_get(v_toApplicative_3881_, 1);
            lean_inc(v_toPure_3886_);
            lean_dec_ref(v_toApplicative_3881_);
            v___x_3887_ = lean_apply_2(v_toPure_3886_, lean_box(0), v_x_3863_);
            return v___x_3887_;
        } else {
            let mut v___x_3888_: u8 = 0;
            v___x_3888_ = lean_nat_dec_le(v___x_3884_, v___x_3884_);
            if v___x_3888_ == 0 {
                if v___x_3885_ == 0 {
                    let mut v_toPure_3889_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
                    lean_inc_ref(v_toApplicative_3881_);
                    lean_dec(v___x_3883_);
                    lean_dec_ref(v_vs_3882_);
                    lean_dec(v_f_3859_);
                    lean_dec_ref(v_inst_3858_);
                    v_toPure_3889_ = lean_ctor_get(v_toApplicative_3881_, 1);
                    lean_inc(v_toPure_3889_);
                    lean_dec_ref(v_toApplicative_3881_);
                    v___x_3890_ = lean_apply_2(v_toPure_3889_, lean_box(0), v_x_3863_);
                    return v___x_3890_;
                } else {
                    let mut v___x_3891_: usize = 0;
                    let mut v___x_3892_: usize = 0;
                    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
                    v___x_3891_ = lean_usize_of_nat(v___x_3883_);
                    lean_dec(v___x_3883_);
                    v___x_3892_ = lean_usize_of_nat(v___x_3884_);
                    v___x_3893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
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
                let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
                v___x_3894_ = lean_usize_of_nat(v___x_3883_);
                lean_dec(v___x_3883_);
                v___x_3895_ = lean_usize_of_nat(v___x_3884_);
                v___x_3896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_3897_: *mut LeanObject,
    mut v_f_3898_: *mut LeanObject,
    mut v_x_3899_: *mut LeanObject,
    mut v_x_3900_: *mut LeanObject,
    mut v_x_3901_: *mut LeanObject,
    mut v_x_3902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_215__boxed_3903_: usize = 0;
    let mut v_x_216__boxed_3904_: usize = 0;
    let mut v_res_3905_: *mut LeanObject = core::ptr::null_mut();
    v_x_215__boxed_3903_ = lean_unbox_usize(v_x_3900_);
    lean_dec(v_x_3900_);
    v_x_216__boxed_3904_ = lean_unbox_usize(v_x_3901_);
    lean_dec(v_x_3901_);
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
    mut v_00_u03b1_3906_: *mut LeanObject,
    mut v_m_3907_: *mut LeanObject,
    mut v_inst_3908_: *mut LeanObject,
    mut v_00_u03b2_3909_: *mut LeanObject,
    mut v_f_3910_: *mut LeanObject,
    mut v_x_3911_: *mut LeanObject,
    mut v_x_3912_: usize,
    mut v_x_3913_: usize,
    mut v_x_3914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3916_: *mut LeanObject,
    mut v_m_3917_: *mut LeanObject,
    mut v_inst_3918_: *mut LeanObject,
    mut v_00_u03b2_3919_: *mut LeanObject,
    mut v_f_3920_: *mut LeanObject,
    mut v_x_3921_: *mut LeanObject,
    mut v_x_3922_: *mut LeanObject,
    mut v_x_3923_: *mut LeanObject,
    mut v_x_3924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_284__boxed_3925_: usize = 0;
    let mut v_x_285__boxed_3926_: usize = 0;
    let mut v_res_3927_: *mut LeanObject = core::ptr::null_mut();
    v_x_284__boxed_3925_ = lean_unbox_usize(v_x_3922_);
    lean_dec(v_x_3922_);
    v_x_285__boxed_3926_ = lean_unbox_usize(v_x_3923_);
    lean_dec(v_x_3923_);
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
    mut v_tail_3928_: *mut LeanObject,
    mut v___x_3929_: *mut LeanObject,
    mut v_toApplicative_3930_: *mut LeanObject,
    mut v_inst_3931_: *mut LeanObject,
    mut v_f_3932_: *mut LeanObject,
    mut v_b_3933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: u8 = 0;
    v___x_3934_ = lean_array_get_size(v_tail_3928_);
    v___x_3935_ = lean_nat_dec_lt(v___x_3929_, v___x_3934_);
    if v___x_3935_ == 0 {
        let mut v_toPure_3936_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_3932_);
        lean_dec_ref(v_inst_3931_);
        lean_dec_ref(v_tail_3928_);
        v_toPure_3936_ = lean_ctor_get(v_toApplicative_3930_, 1);
        lean_inc(v_toPure_3936_);
        lean_dec_ref(v_toApplicative_3930_);
        v___x_3937_ = lean_apply_2(v_toPure_3936_, lean_box(0), v_b_3933_);
        return v___x_3937_;
    } else {
        let mut v___x_3938_: u8 = 0;
        v___x_3938_ = lean_nat_dec_le(v___x_3934_, v___x_3934_);
        if v___x_3938_ == 0 {
            if v___x_3935_ == 0 {
                let mut v_toPure_3939_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_f_3932_);
                lean_dec_ref(v_inst_3931_);
                lean_dec_ref(v_tail_3928_);
                v_toPure_3939_ = lean_ctor_get(v_toApplicative_3930_, 1);
                lean_inc(v_toPure_3939_);
                lean_dec_ref(v_toApplicative_3930_);
                v___x_3940_ = lean_apply_2(v_toPure_3939_, lean_box(0), v_b_3933_);
                return v___x_3940_;
            } else {
                let mut v___x_3941_: usize = 0;
                let mut v___x_3942_: usize = 0;
                let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toApplicative_3930_);
                v___x_3941_ = 0usize;
                v___x_3942_ = lean_usize_of_nat(v___x_3934_);
                v___x_3943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_toApplicative_3930_);
            v___x_3944_ = 0usize;
            v___x_3945_ = lean_usize_of_nat(v___x_3934_);
            v___x_3946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_tail_3947_: *mut LeanObject,
    mut v___x_3948_: *mut LeanObject,
    mut v_toApplicative_3949_: *mut LeanObject,
    mut v_inst_3950_: *mut LeanObject,
    mut v_f_3951_: *mut LeanObject,
    mut v_b_3952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3953_: *mut LeanObject = core::ptr::null_mut();
    v_res_3953_ = l_Lean_PersistentArray_foldlM___redArg___lam__0(
        v_tail_3947_,
        v___x_3948_,
        v_toApplicative_3949_,
        v_inst_3950_,
        v_f_3951_,
        v_b_3952_,
    );
    lean_dec(v___x_3948_);
    return v_res_3953_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___redArg(
    mut v_inst_3954_: *mut LeanObject,
    mut v_t_3955_: *mut LeanObject,
    mut v_f_3956_: *mut LeanObject,
    mut v_init_3957_: *mut LeanObject,
    mut v_start_3958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: u8 = 0;
    v___x_3959_ = lean_unsigned_to_nat(0);
    v___x_3960_ = lean_nat_dec_eq(v_start_3958_, v___x_3959_);
    if v___x_3960_ == 0 {
        let mut v_root_3961_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_3962_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_3963_: usize = 0;
        let mut v_tailOff_3964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3965_: u8 = 0;
        v_root_3961_ = lean_ctor_get(v_t_3955_, 0);
        lean_inc_ref(v_root_3961_);
        v_tail_3962_ = lean_ctor_get(v_t_3955_, 1);
        lean_inc_ref(v_tail_3962_);
        v_shift_3963_ = lean_ctor_get_usize(v_t_3955_, 4);
        v_tailOff_3964_ = lean_ctor_get(v_t_3955_, 3);
        lean_inc(v_tailOff_3964_);
        lean_dec_ref(v_t_3955_);
        v___x_3965_ = lean_nat_dec_le(v_tailOff_3964_, v_start_3958_);
        if v___x_3965_ == 0 {
            let mut v_toApplicative_3966_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_3967_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_3968_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3969_: usize = 0;
            let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_tailOff_3964_);
            v_toApplicative_3966_ = lean_ctor_get(v_inst_3954_, 0);
            v_toBind_3967_ = lean_ctor_get(v_inst_3954_, 1);
            lean_inc(v_toBind_3967_);
            lean_inc(v_f_3956_);
            lean_inc_ref(v_inst_3954_);
            lean_inc_ref(v_toApplicative_3966_);
            v___f_3968_ = lean_alloc_closure(
                l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___f_3968_, 0, v_tail_3962_);
            lean_closure_set(v___f_3968_, 1, v___x_3959_);
            lean_closure_set(v___f_3968_, 2, v_toApplicative_3966_);
            lean_closure_set(v___f_3968_, 3, v_inst_3954_);
            lean_closure_set(v___f_3968_, 4, v_f_3956_);
            v___x_3969_ = lean_usize_of_nat(v_start_3958_);
            v___x_3970_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_3954_, v_f_3956_, v_root_3961_, v___x_3969_, v_shift_3963_, v_init_3957_);
            v___x_3971_ = lean_apply_4(
                v_toBind_3967_,
                lean_box(0),
                lean_box(0),
                v___x_3970_,
                v___f_3968_,
            );
            return v___x_3971_;
        } else {
            let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3974_: u8 = 0;
            lean_dec_ref(v_root_3961_);
            v___x_3972_ = lean_nat_sub(v_start_3958_, v_tailOff_3964_);
            lean_dec(v_tailOff_3964_);
            v___x_3973_ = lean_array_get_size(v_tail_3962_);
            v___x_3974_ = lean_nat_dec_lt(v___x_3972_, v___x_3973_);
            if v___x_3974_ == 0 {
                let mut v_toApplicative_3975_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_3976_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_3972_);
                lean_dec_ref(v_tail_3962_);
                lean_dec(v_f_3956_);
                v_toApplicative_3975_ = lean_ctor_get(v_inst_3954_, 0);
                lean_inc_ref(v_toApplicative_3975_);
                lean_dec_ref(v_inst_3954_);
                v_toPure_3976_ = lean_ctor_get(v_toApplicative_3975_, 1);
                lean_inc(v_toPure_3976_);
                lean_dec_ref(v_toApplicative_3975_);
                v___x_3977_ = lean_apply_2(v_toPure_3976_, lean_box(0), v_init_3957_);
                return v___x_3977_;
            } else {
                let mut v___x_3978_: u8 = 0;
                v___x_3978_ = lean_nat_dec_le(v___x_3973_, v___x_3973_);
                if v___x_3978_ == 0 {
                    if v___x_3974_ == 0 {
                        let mut v_toApplicative_3979_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_toPure_3980_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v___x_3972_);
                        lean_dec_ref(v_tail_3962_);
                        lean_dec(v_f_3956_);
                        v_toApplicative_3979_ = lean_ctor_get(v_inst_3954_, 0);
                        lean_inc_ref(v_toApplicative_3979_);
                        lean_dec_ref(v_inst_3954_);
                        v_toPure_3980_ = lean_ctor_get(v_toApplicative_3979_, 1);
                        lean_inc(v_toPure_3980_);
                        lean_dec_ref(v_toApplicative_3979_);
                        v___x_3981_ = lean_apply_2(v_toPure_3980_, lean_box(0), v_init_3957_);
                        return v___x_3981_;
                    } else {
                        let mut v___x_3982_: usize = 0;
                        let mut v___x_3983_: usize = 0;
                        let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
                        v___x_3982_ = lean_usize_of_nat(v___x_3972_);
                        lean_dec(v___x_3972_);
                        v___x_3983_ = lean_usize_of_nat(v___x_3973_);
                        v___x_3984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
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
                    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
                    v___x_3985_ = lean_usize_of_nat(v___x_3972_);
                    lean_dec(v___x_3972_);
                    v___x_3986_ = lean_usize_of_nat(v___x_3973_);
                    v___x_3987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
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
        let mut v_toApplicative_3988_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_3989_: *mut LeanObject = core::ptr::null_mut();
        let mut v_root_3990_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_3991_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3992_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_3988_ = lean_ctor_get(v_inst_3954_, 0);
        v_toBind_3989_ = lean_ctor_get(v_inst_3954_, 1);
        lean_inc(v_toBind_3989_);
        v_root_3990_ = lean_ctor_get(v_t_3955_, 0);
        lean_inc_ref(v_root_3990_);
        v_tail_3991_ = lean_ctor_get(v_t_3955_, 1);
        lean_inc_ref(v_tail_3991_);
        lean_dec_ref(v_t_3955_);
        lean_inc(v_f_3956_);
        lean_inc_ref(v_inst_3954_);
        lean_inc_ref(v_toApplicative_3988_);
        v___f_3992_ = lean_alloc_closure(
            l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_3992_, 0, v_tail_3991_);
        lean_closure_set(v___f_3992_, 1, v___x_3959_);
        lean_closure_set(v___f_3992_, 2, v_toApplicative_3988_);
        lean_closure_set(v___f_3992_, 3, v_inst_3954_);
        lean_closure_set(v___f_3992_, 4, v_f_3956_);
        v___x_3993_ =
            l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(
                v_inst_3954_,
                v_f_3956_,
                v_root_3990_,
                v_init_3957_,
            );
        v___x_3994_ = lean_apply_4(
            v_toBind_3989_,
            lean_box(0),
            lean_box(0),
            v___x_3993_,
            v___f_3992_,
        );
        return v___x_3994_;
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___redArg___boxed(
    mut v_inst_3995_: *mut LeanObject,
    mut v_t_3996_: *mut LeanObject,
    mut v_f_3997_: *mut LeanObject,
    mut v_init_3998_: *mut LeanObject,
    mut v_start_3999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4000_: *mut LeanObject = core::ptr::null_mut();
    v_res_4000_ = l_Lean_PersistentArray_foldlM___redArg(
        v_inst_3995_,
        v_t_3996_,
        v_f_3997_,
        v_init_3998_,
        v_start_3999_,
    );
    lean_dec(v_start_3999_);
    return v_res_4000_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM(
    mut v_00_u03b1_4001_: *mut LeanObject,
    mut v_m_4002_: *mut LeanObject,
    mut v_inst_4003_: *mut LeanObject,
    mut v_00_u03b2_4004_: *mut LeanObject,
    mut v_t_4005_: *mut LeanObject,
    mut v_f_4006_: *mut LeanObject,
    mut v_init_4007_: *mut LeanObject,
    mut v_start_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4010_: *mut LeanObject,
    mut v_m_4011_: *mut LeanObject,
    mut v_inst_4012_: *mut LeanObject,
    mut v_00_u03b2_4013_: *mut LeanObject,
    mut v_t_4014_: *mut LeanObject,
    mut v_f_4015_: *mut LeanObject,
    mut v_init_4016_: *mut LeanObject,
    mut v_start_4017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4018_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_start_4017_);
    return v_res_4018_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(
    mut v_inst_4019_: *mut LeanObject,
    mut v_f_4020_: *mut LeanObject,
    mut v_x_4021_: *mut LeanObject,
    mut v_x_4022_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4021_) == 0 {
        let mut v_cs_4023_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4026_: u8 = 0;
        v_cs_4023_ = lean_ctor_get(v_x_4021_, 0);
        lean_inc_ref(v_cs_4023_);
        lean_dec_ref_known(v_x_4021_, 1);
        v___x_4024_ = lean_array_get_size(v_cs_4023_);
        v___x_4025_ = lean_unsigned_to_nat(0);
        v___x_4026_ = lean_nat_dec_lt(v___x_4025_, v___x_4024_);
        if v___x_4026_ == 0 {
            let mut v_toApplicative_4027_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_4028_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_cs_4023_);
            lean_dec(v_f_4020_);
            v_toApplicative_4027_ = lean_ctor_get(v_inst_4019_, 0);
            lean_inc_ref(v_toApplicative_4027_);
            lean_dec_ref(v_inst_4019_);
            v_toPure_4028_ = lean_ctor_get(v_toApplicative_4027_, 1);
            lean_inc(v_toPure_4028_);
            lean_dec_ref(v_toApplicative_4027_);
            v___x_4029_ = lean_apply_2(v_toPure_4028_, lean_box(0), v_x_4022_);
            return v___x_4029_;
        } else {
            let mut v___f_4030_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4031_: usize = 0;
            let mut v___x_4032_: usize = 0;
            let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_inst_4019_);
            v___f_4030_ = lean_alloc_closure(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0 as *mut core::ffi::c_void, 4, 2);
            lean_closure_set(v___f_4030_, 0, v_inst_4019_);
            lean_closure_set(v___f_4030_, 1, v_f_4020_);
            v___x_4031_ = lean_usize_of_nat(v___x_4024_);
            v___x_4032_ = 0usize;
            v___x_4033_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
        let mut v_vs_4034_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4037_: u8 = 0;
        v_vs_4034_ = lean_ctor_get(v_x_4021_, 0);
        lean_inc_ref(v_vs_4034_);
        lean_dec_ref_known(v_x_4021_, 1);
        v___x_4035_ = lean_array_get_size(v_vs_4034_);
        v___x_4036_ = lean_unsigned_to_nat(0);
        v___x_4037_ = lean_nat_dec_lt(v___x_4036_, v___x_4035_);
        if v___x_4037_ == 0 {
            let mut v_toApplicative_4038_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_4039_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_vs_4034_);
            lean_dec(v_f_4020_);
            v_toApplicative_4038_ = lean_ctor_get(v_inst_4019_, 0);
            lean_inc_ref(v_toApplicative_4038_);
            lean_dec_ref(v_inst_4019_);
            v_toPure_4039_ = lean_ctor_get(v_toApplicative_4038_, 1);
            lean_inc(v_toPure_4039_);
            lean_dec_ref(v_toApplicative_4038_);
            v___x_4040_ = lean_apply_2(v_toPure_4039_, lean_box(0), v_x_4022_);
            return v___x_4040_;
        } else {
            let mut v___x_4041_: usize = 0;
            let mut v___x_4042_: usize = 0;
            let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
            v___x_4041_ = lean_usize_of_nat(v___x_4035_);
            v___x_4042_ = 0usize;
            v___x_4043_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_inst_4044_: *mut LeanObject,
    mut v_f_4045_: *mut LeanObject,
    mut v_c_4046_: *mut LeanObject,
    mut v_b_4047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    v___x_4048_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(
        v_inst_4044_,
        v_f_4045_,
        v_c_4046_,
        v_b_4047_,
    );
    return v___x_4048_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux(
    mut v_00_u03b1_4049_: *mut LeanObject,
    mut v_m_4050_: *mut LeanObject,
    mut v_00_u03b2_4051_: *mut LeanObject,
    mut v_inst_4052_: *mut LeanObject,
    mut v_f_4053_: *mut LeanObject,
    mut v_x_4054_: *mut LeanObject,
    mut v_x_4055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    v___x_4056_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(
        v_inst_4052_,
        v_f_4053_,
        v_x_4054_,
        v_x_4055_,
    );
    return v___x_4056_;
}
pub unsafe fn l_Lean_PersistentArray_foldrM___redArg___lam__0(
    mut v_inst_4057_: *mut LeanObject,
    mut v_f_4058_: *mut LeanObject,
    mut v_root_4059_: *mut LeanObject,
    mut v_____do__lift_4060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    v___x_4061_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(
        v_inst_4057_,
        v_f_4058_,
        v_root_4059_,
        v_____do__lift_4060_,
    );
    return v___x_4061_;
}
pub unsafe fn l_Lean_PersistentArray_foldrM___redArg(
    mut v_inst_4062_: *mut LeanObject,
    mut v_t_4063_: *mut LeanObject,
    mut v_f_4064_: *mut LeanObject,
    mut v_init_4065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: u8 = 0;
    v_toApplicative_4066_ = lean_ctor_get(v_inst_4062_, 0);
    v_toBind_4067_ = lean_ctor_get(v_inst_4062_, 1);
    lean_inc(v_toBind_4067_);
    v_root_4068_ = lean_ctor_get(v_t_4063_, 0);
    lean_inc_ref(v_root_4068_);
    v_tail_4069_ = lean_ctor_get(v_t_4063_, 1);
    lean_inc_ref(v_tail_4069_);
    lean_dec_ref(v_t_4063_);
    lean_inc(v_f_4064_);
    lean_inc_ref(v_inst_4062_);
    v___f_4070_ = lean_alloc_closure(
        l_Lean_PersistentArray_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4070_, 0, v_inst_4062_);
    lean_closure_set(v___f_4070_, 1, v_f_4064_);
    lean_closure_set(v___f_4070_, 2, v_root_4068_);
    v___x_4071_ = lean_array_get_size(v_tail_4069_);
    v___x_4072_ = lean_unsigned_to_nat(0);
    v___x_4073_ = lean_nat_dec_lt(v___x_4072_, v___x_4071_);
    if v___x_4073_ == 0 {
        let mut v_toPure_4074_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_toApplicative_4066_);
        lean_dec_ref(v_tail_4069_);
        lean_dec(v_f_4064_);
        lean_dec_ref(v_inst_4062_);
        v_toPure_4074_ = lean_ctor_get(v_toApplicative_4066_, 1);
        lean_inc(v_toPure_4074_);
        lean_dec_ref(v_toApplicative_4066_);
        v___x_4075_ = lean_apply_2(v_toPure_4074_, lean_box(0), v_init_4065_);
        v___x_4076_ = lean_apply_4(
            v_toBind_4067_,
            lean_box(0),
            lean_box(0),
            v___x_4075_,
            v___f_4070_,
        );
        return v___x_4076_;
    } else {
        let mut v___x_4077_: usize = 0;
        let mut v___x_4078_: usize = 0;
        let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
        v___x_4077_ = lean_usize_of_nat(v___x_4071_);
        v___x_4078_ = 0usize;
        v___x_4079_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            lean_box(0),
            lean_box(0),
            lean_box(0),
            v_inst_4062_,
            v_f_4064_,
            v_tail_4069_,
            v___x_4077_,
            v___x_4078_,
            v_init_4065_,
        );
        v___x_4080_ = lean_apply_4(
            v_toBind_4067_,
            lean_box(0),
            lean_box(0),
            v___x_4079_,
            v___f_4070_,
        );
        return v___x_4080_;
    }
}
pub unsafe fn l_Lean_PersistentArray_foldrM(
    mut v_00_u03b1_4081_: *mut LeanObject,
    mut v_m_4082_: *mut LeanObject,
    mut v_00_u03b2_4083_: *mut LeanObject,
    mut v_inst_4084_: *mut LeanObject,
    mut v_t_4085_: *mut LeanObject,
    mut v_f_4086_: *mut LeanObject,
    mut v_init_4087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    v___x_4088_ =
        l_Lean_PersistentArray_foldrM___redArg(v_inst_4084_, v_t_4085_, v_f_4086_, v_init_4087_);
    return v___x_4088_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___redArg___lam__0(
    mut v_toPure_4089_: *mut LeanObject,
    mut v_____s_4090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_4091_: *mut LeanObject = core::ptr::null_mut();
    v_fst_4091_ = lean_ctor_get(v_____s_4090_, 0);
    if lean_obj_tag(v_fst_4091_) == 0 {
        let mut v_snd_4092_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
        v_snd_4092_ = lean_ctor_get(v_____s_4090_, 1);
        lean_inc(v_snd_4092_);
        lean_dec_ref(v_____s_4090_);
        v___x_4093_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4093_, 0, v_snd_4092_);
        v___x_4094_ = lean_apply_2(v_toPure_4089_, lean_box(0), v___x_4093_);
        return v___x_4094_;
    } else {
        let mut v_val_4095_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_fst_4091_);
        lean_dec_ref(v_____s_4090_);
        v_val_4095_ = lean_ctor_get(v_fst_4091_, 0);
        lean_inc(v_val_4095_);
        lean_dec_ref_known(v_fst_4091_, 1);
        v___x_4096_ = lean_apply_2(v_toPure_4089_, lean_box(0), v_val_4095_);
        return v___x_4096_;
    }
}
pub unsafe fn l_Lean_PersistentArray_forInAux___redArg___lam__1(
    mut v_snd_4097_: *mut LeanObject,
    mut v_toPure_4098_: *mut LeanObject,
    mut v___x_4099_: *mut LeanObject,
    mut v_____do__lift_4100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4108_: u8 = 0;
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_4100_) == 0 {
                    lean_dec(v___x_4099_);
                    v___x_4101_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4101_, 0, v_____do__lift_4100_);
                    v___x_4102_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4102_, 0, v___x_4101_);
                    lean_ctor_set(v___x_4102_, 1, v_snd_4097_);
                    v___x_4103_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4103_, 0, v___x_4102_);
                    v___x_4104_ = lean_apply_2(v_toPure_4098_, lean_box(0), v___x_4103_);
                    return v___x_4104_;
                } else {
                    lean_dec(v_snd_4097_);
                    v_a_4105_ = lean_ctor_get(v_____do__lift_4100_, 0);
                    v_isSharedCheck_4114_ = (!lean_is_exclusive(v_____do__lift_4100_)) as u8;
                    if v_isSharedCheck_4114_ == 0 {
                        v___x_4107_ = v_____do__lift_4100_;
                        v_isShared_4108_ = v_isSharedCheck_4114_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4105_);
                        lean_dec(v_____do__lift_4100_);
                        v___x_4107_ = lean_box(0);
                        v_isShared_4108_ = v_isSharedCheck_4114_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4109_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4109_, 0, v___x_4099_);
                lean_ctor_set(v___x_4109_, 1, v_a_4105_);
                if v_isShared_4108_ == 0 {
                    lean_ctor_set(v___x_4107_, 0, v___x_4109_);
                    v___x_4111_ = v___x_4107_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4109_);
                    v___x_4111_ = v_reuseFailAlloc_4113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4112_ = lean_apply_2(v_toPure_4098_, lean_box(0), v___x_4111_);
                return v___x_4112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forInAux___redArg___lam__5(
    mut v_toPure_4115_: *mut LeanObject,
    mut v___x_4116_: *mut LeanObject,
    mut v_f_4117_: *mut LeanObject,
    mut v_toBind_4118_: *mut LeanObject,
    mut v_a_4119_: *mut LeanObject,
    mut v_x_4120_: *mut LeanObject,
    mut v___y_4121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    v_snd_4122_ = lean_ctor_get(v___y_4121_, 1);
    lean_inc_n(v_snd_4122_, 2);
    lean_dec_ref(v___y_4121_);
    v___f_4123_ = lean_alloc_closure(
        l_Lean_PersistentArray_forInAux___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4123_, 0, v_snd_4122_);
    lean_closure_set(v___f_4123_, 1, v_toPure_4115_);
    lean_closure_set(v___f_4123_, 2, v___x_4116_);
    v___x_4124_ = lean_apply_2(v_f_4117_, v_a_4119_, v_snd_4122_);
    v___x_4125_ = lean_apply_4(
        v_toBind_4118_,
        lean_box(0),
        lean_box(0),
        v___x_4124_,
        v___f_4123_,
    );
    return v___x_4125_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed(
    mut v_toPure_4126_: *mut LeanObject,
    mut v___x_4127_: *mut LeanObject,
    mut v_inst_4128_: *mut LeanObject,
    mut v_f_4129_: *mut LeanObject,
    mut v_toBind_4130_: *mut LeanObject,
    mut v_a_4131_: *mut LeanObject,
    mut v_x_4132_: *mut LeanObject,
    mut v___y_4133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4134_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_4131_);
    return v_res_4134_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___redArg(
    mut v_inst_4135_: *mut LeanObject,
    mut v_f_4136_: *mut LeanObject,
    mut v_n_4137_: *mut LeanObject,
    mut v_b_4138_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_n_4137_) == 0 {
        let mut v_toApplicative_4139_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_4140_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_4141_: *mut LeanObject = core::ptr::null_mut();
        let mut v_cs_4142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4147_: usize = 0;
        let mut v___x_4148_: usize = 0;
        let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_4139_ = lean_ctor_get(v_inst_4135_, 0);
        v_toBind_4140_ = lean_ctor_get(v_inst_4135_, 1);
        lean_inc_n(v_toBind_4140_, 2);
        v_toPure_4141_ = lean_ctor_get(v_toApplicative_4139_, 1);
        v_cs_4142_ = lean_ctor_get(v_n_4137_, 0);
        lean_inc_n(v_toPure_4141_, 2);
        v___f_4143_ = lean_alloc_closure(
            l_Lean_PersistentArray_forInAux___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_4143_, 0, v_toPure_4141_);
        v___x_4144_ = lean_box(0);
        lean_inc_ref(v_inst_4135_);
        v___f_4145_ = lean_alloc_closure(
            l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed as *mut core::ffi::c_void,
            8,
            5,
        );
        lean_closure_set(v___f_4145_, 0, v_toPure_4141_);
        lean_closure_set(v___f_4145_, 1, v___x_4144_);
        lean_closure_set(v___f_4145_, 2, v_inst_4135_);
        lean_closure_set(v___f_4145_, 3, v_f_4136_);
        lean_closure_set(v___f_4145_, 4, v_toBind_4140_);
        v___x_4146_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4146_, 0, v___x_4144_);
        lean_ctor_set(v___x_4146_, 1, v_b_4138_);
        v_sz_4147_ = lean_array_size(v_cs_4142_);
        v___x_4148_ = 0usize;
        lean_inc_ref(v_cs_4142_);
        v___x_4149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            lean_box(0),
            lean_box(0),
            lean_box(0),
            v_inst_4135_,
            v_cs_4142_,
            v___f_4145_,
            v_sz_4147_,
            v___x_4148_,
            v___x_4146_,
        );
        v___x_4150_ = lean_apply_4(
            v_toBind_4140_,
            lean_box(0),
            lean_box(0),
            v___x_4149_,
            v___f_4143_,
        );
        return v___x_4150_;
    } else {
        let mut v_toApplicative_4151_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_4152_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_4153_: *mut LeanObject = core::ptr::null_mut();
        let mut v_vs_4154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4159_: usize = 0;
        let mut v___x_4160_: usize = 0;
        let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_4151_ = lean_ctor_get(v_inst_4135_, 0);
        v_toBind_4152_ = lean_ctor_get(v_inst_4135_, 1);
        lean_inc_n(v_toBind_4152_, 2);
        v_toPure_4153_ = lean_ctor_get(v_toApplicative_4151_, 1);
        v_vs_4154_ = lean_ctor_get(v_n_4137_, 0);
        lean_inc_n(v_toPure_4153_, 2);
        v___f_4155_ = lean_alloc_closure(
            l_Lean_PersistentArray_forInAux___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_4155_, 0, v_toPure_4153_);
        v___x_4156_ = lean_box(0);
        v___f_4157_ = lean_alloc_closure(
            l_Lean_PersistentArray_forInAux___redArg___lam__5 as *mut core::ffi::c_void,
            7,
            4,
        );
        lean_closure_set(v___f_4157_, 0, v_toPure_4153_);
        lean_closure_set(v___f_4157_, 1, v___x_4156_);
        lean_closure_set(v___f_4157_, 2, v_f_4136_);
        lean_closure_set(v___f_4157_, 3, v_toBind_4152_);
        v___x_4158_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4158_, 0, v___x_4156_);
        lean_ctor_set(v___x_4158_, 1, v_b_4138_);
        v_sz_4159_ = lean_array_size(v_vs_4154_);
        v___x_4160_ = 0usize;
        lean_inc_ref(v_vs_4154_);
        v___x_4161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            lean_box(0),
            lean_box(0),
            lean_box(0),
            v_inst_4135_,
            v_vs_4154_,
            v___f_4157_,
            v_sz_4159_,
            v___x_4160_,
            v___x_4158_,
        );
        v___x_4162_ = lean_apply_4(
            v_toBind_4152_,
            lean_box(0),
            lean_box(0),
            v___x_4161_,
            v___f_4155_,
        );
        return v___x_4162_;
    }
}
pub unsafe fn l_Lean_PersistentArray_forInAux___redArg___lam__2(
    mut v_toPure_4163_: *mut LeanObject,
    mut v___x_4164_: *mut LeanObject,
    mut v_inst_4165_: *mut LeanObject,
    mut v_f_4166_: *mut LeanObject,
    mut v_toBind_4167_: *mut LeanObject,
    mut v_a_4168_: *mut LeanObject,
    mut v_x_4169_: *mut LeanObject,
    mut v___y_4170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    v_snd_4171_ = lean_ctor_get(v___y_4170_, 1);
    lean_inc_n(v_snd_4171_, 2);
    lean_dec_ref(v___y_4170_);
    v___f_4172_ = lean_alloc_closure(
        l_Lean_PersistentArray_forInAux___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4172_, 0, v_snd_4171_);
    lean_closure_set(v___f_4172_, 1, v_toPure_4163_);
    lean_closure_set(v___f_4172_, 2, v___x_4164_);
    v___x_4173_ =
        l_Lean_PersistentArray_forInAux___redArg(v_inst_4165_, v_f_4166_, v_a_4168_, v_snd_4171_);
    v___x_4174_ = lean_apply_4(
        v_toBind_4167_,
        lean_box(0),
        lean_box(0),
        v___x_4173_,
        v___f_4172_,
    );
    return v___x_4174_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___redArg___boxed(
    mut v_inst_4175_: *mut LeanObject,
    mut v_f_4176_: *mut LeanObject,
    mut v_n_4177_: *mut LeanObject,
    mut v_b_4178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4179_: *mut LeanObject = core::ptr::null_mut();
    v_res_4179_ =
        l_Lean_PersistentArray_forInAux___redArg(v_inst_4175_, v_f_4176_, v_n_4177_, v_b_4178_);
    lean_dec_ref(v_n_4177_);
    return v_res_4179_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux(
    mut v_00_u03b1_4180_: *mut LeanObject,
    mut v_00_u03b2_4181_: *mut LeanObject,
    mut v_m_4182_: *mut LeanObject,
    mut v_inst_4183_: *mut LeanObject,
    mut v_inh_4184_: *mut LeanObject,
    mut v_f_4185_: *mut LeanObject,
    mut v_n_4186_: *mut LeanObject,
    mut v_b_4187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    v___x_4188_ =
        l_Lean_PersistentArray_forInAux___redArg(v_inst_4183_, v_f_4185_, v_n_4186_, v_b_4187_);
    return v___x_4188_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___boxed(
    mut v_00_u03b1_4189_: *mut LeanObject,
    mut v_00_u03b2_4190_: *mut LeanObject,
    mut v_m_4191_: *mut LeanObject,
    mut v_inst_4192_: *mut LeanObject,
    mut v_inh_4193_: *mut LeanObject,
    mut v_f_4194_: *mut LeanObject,
    mut v_n_4195_: *mut LeanObject,
    mut v_b_4196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4197_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_n_4195_);
    lean_dec(v_inh_4193_);
    return v_res_4197_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___redArg___lam__0(
    mut v_toPure_4198_: *mut LeanObject,
    mut v_____s_4199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_4200_: *mut LeanObject = core::ptr::null_mut();
    v_fst_4200_ = lean_ctor_get(v_____s_4199_, 0);
    if lean_obj_tag(v_fst_4200_) == 0 {
        let mut v_snd_4201_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
        v_snd_4201_ = lean_ctor_get(v_____s_4199_, 1);
        lean_inc(v_snd_4201_);
        lean_dec_ref(v_____s_4199_);
        v___x_4202_ = lean_apply_2(v_toPure_4198_, lean_box(0), v_snd_4201_);
        return v___x_4202_;
    } else {
        let mut v_val_4203_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_fst_4200_);
        lean_dec_ref(v_____s_4199_);
        v_val_4203_ = lean_ctor_get(v_fst_4200_, 0);
        lean_inc(v_val_4203_);
        lean_dec_ref_known(v_fst_4200_, 1);
        v___x_4204_ = lean_apply_2(v_toPure_4198_, lean_box(0), v_val_4203_);
        return v___x_4204_;
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___redArg___lam__1(
    mut v_snd_4205_: *mut LeanObject,
    mut v_toPure_4206_: *mut LeanObject,
    mut v___x_4207_: *mut LeanObject,
    mut v_____do__lift_4208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4212_: u8 = 0;
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4219_: u8 = 0;
    let mut v_a_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4223_: u8 = 0;
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_4208_) == 0 {
                    lean_dec(v___x_4207_);
                    v_a_4209_ = lean_ctor_get(v_____do__lift_4208_, 0);
                    v_isSharedCheck_4219_ = (!lean_is_exclusive(v_____do__lift_4208_)) as u8;
                    if v_isSharedCheck_4219_ == 0 {
                        v___x_4211_ = v_____do__lift_4208_;
                        v_isShared_4212_ = v_isSharedCheck_4219_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4209_);
                        lean_dec(v_____do__lift_4208_);
                        v___x_4211_ = lean_box(0);
                        v_isShared_4212_ = v_isSharedCheck_4219_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_4205_);
                    v_a_4220_ = lean_ctor_get(v_____do__lift_4208_, 0);
                    v_isSharedCheck_4229_ = (!lean_is_exclusive(v_____do__lift_4208_)) as u8;
                    if v_isSharedCheck_4229_ == 0 {
                        v___x_4222_ = v_____do__lift_4208_;
                        v_isShared_4223_ = v_isSharedCheck_4229_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4220_);
                        lean_dec(v_____do__lift_4208_);
                        v___x_4222_ = lean_box(0);
                        v_isShared_4223_ = v_isSharedCheck_4229_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4213_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4213_, 0, v_a_4209_);
                v___x_4214_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4214_, 0, v___x_4213_);
                lean_ctor_set(v___x_4214_, 1, v_snd_4205_);
                if v_isShared_4212_ == 0 {
                    lean_ctor_set(v___x_4211_, 0, v___x_4214_);
                    v___x_4216_ = v___x_4211_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4214_);
                    v___x_4216_ = v_reuseFailAlloc_4218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4217_ = lean_apply_2(v_toPure_4206_, lean_box(0), v___x_4216_);
                return v___x_4217_;
            }
            3 => {
                v___x_4224_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4224_, 0, v___x_4207_);
                lean_ctor_set(v___x_4224_, 1, v_a_4220_);
                if v_isShared_4223_ == 0 {
                    lean_ctor_set(v___x_4222_, 0, v___x_4224_);
                    v___x_4226_ = v___x_4222_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4224_);
                    v___x_4226_ = v_reuseFailAlloc_4228_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4227_ = lean_apply_2(v_toPure_4206_, lean_box(0), v___x_4226_);
                return v___x_4227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___redArg___lam__2(
    mut v_toPure_4230_: *mut LeanObject,
    mut v___x_4231_: *mut LeanObject,
    mut v_f_4232_: *mut LeanObject,
    mut v_toBind_4233_: *mut LeanObject,
    mut v_a_4234_: *mut LeanObject,
    mut v_x_4235_: *mut LeanObject,
    mut v___y_4236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    v_snd_4237_ = lean_ctor_get(v___y_4236_, 1);
    lean_inc_n(v_snd_4237_, 2);
    lean_dec_ref(v___y_4236_);
    v___f_4238_ = lean_alloc_closure(
        l_Lean_PersistentArray_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_4238_, 0, v_snd_4237_);
    lean_closure_set(v___f_4238_, 1, v_toPure_4230_);
    lean_closure_set(v___f_4238_, 2, v___x_4231_);
    v___x_4239_ = lean_apply_2(v_f_4232_, v_a_4234_, v_snd_4237_);
    v___x_4240_ = lean_apply_4(
        v_toBind_4233_,
        lean_box(0),
        lean_box(0),
        v___x_4239_,
        v___f_4238_,
    );
    return v___x_4240_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___redArg___lam__3(
    mut v_toPure_4241_: *mut LeanObject,
    mut v_f_4242_: *mut LeanObject,
    mut v_toBind_4243_: *mut LeanObject,
    mut v_tail_4244_: *mut LeanObject,
    mut v_inst_4245_: *mut LeanObject,
    mut v___f_4246_: *mut LeanObject,
    mut v_____do__lift_4247_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_4247_) == 0 {
        let mut v_a_4248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_4246_);
        lean_dec_ref(v_inst_4245_);
        lean_dec_ref(v_tail_4244_);
        lean_dec(v_toBind_4243_);
        lean_dec(v_f_4242_);
        v_a_4248_ = lean_ctor_get(v_____do__lift_4247_, 0);
        lean_inc(v_a_4248_);
        lean_dec_ref_known(v_____do__lift_4247_, 1);
        v___x_4249_ = lean_apply_2(v_toPure_4241_, lean_box(0), v_a_4248_);
        return v___x_4249_;
    } else {
        let mut v_a_4250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4252_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4254_: usize = 0;
        let mut v___x_4255_: usize = 0;
        let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
        v_a_4250_ = lean_ctor_get(v_____do__lift_4247_, 0);
        lean_inc(v_a_4250_);
        lean_dec_ref_known(v_____do__lift_4247_, 1);
        v___x_4251_ = lean_box(0);
        lean_inc(v_toBind_4243_);
        v___f_4252_ = lean_alloc_closure(
            l_Lean_PersistentArray_forIn___redArg___lam__2 as *mut core::ffi::c_void,
            7,
            4,
        );
        lean_closure_set(v___f_4252_, 0, v_toPure_4241_);
        lean_closure_set(v___f_4252_, 1, v___x_4251_);
        lean_closure_set(v___f_4252_, 2, v_f_4242_);
        lean_closure_set(v___f_4252_, 3, v_toBind_4243_);
        v___x_4253_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4253_, 0, v___x_4251_);
        lean_ctor_set(v___x_4253_, 1, v_a_4250_);
        v_sz_4254_ = lean_array_size(v_tail_4244_);
        v___x_4255_ = 0usize;
        v___x_4256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            lean_box(0),
            lean_box(0),
            lean_box(0),
            v_inst_4245_,
            v_tail_4244_,
            v___f_4252_,
            v_sz_4254_,
            v___x_4255_,
            v___x_4253_,
        );
        v___x_4257_ = lean_apply_4(
            v_toBind_4243_,
            lean_box(0),
            lean_box(0),
            v___x_4256_,
            v___f_4246_,
        );
        return v___x_4257_;
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___redArg(
    mut v_inst_4258_: *mut LeanObject,
    mut v_t_4259_: *mut LeanObject,
    mut v_init_4260_: *mut LeanObject,
    mut v_f_4261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4262_ = lean_ctor_get(v_inst_4258_, 0);
    v_toBind_4263_ = lean_ctor_get(v_inst_4258_, 1);
    lean_inc_n(v_toBind_4263_, 2);
    v_root_4264_ = lean_ctor_get(v_t_4259_, 0);
    v_tail_4265_ = lean_ctor_get(v_t_4259_, 1);
    v_toPure_4266_ = lean_ctor_get(v_toApplicative_4262_, 1);
    lean_inc_n(v_toPure_4266_, 2);
    lean_inc(v_f_4261_);
    lean_inc_ref(v_inst_4258_);
    v___x_4267_ = l_Lean_PersistentArray_forInAux___redArg(
        v_inst_4258_,
        v_f_4261_,
        v_root_4264_,
        v_init_4260_,
    );
    v___f_4268_ = lean_alloc_closure(
        l_Lean_PersistentArray_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4268_, 0, v_toPure_4266_);
    lean_inc_ref(v_tail_4265_);
    v___f_4269_ = lean_alloc_closure(
        l_Lean_PersistentArray_forIn___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_4269_, 0, v_toPure_4266_);
    lean_closure_set(v___f_4269_, 1, v_f_4261_);
    lean_closure_set(v___f_4269_, 2, v_toBind_4263_);
    lean_closure_set(v___f_4269_, 3, v_tail_4265_);
    lean_closure_set(v___f_4269_, 4, v_inst_4258_);
    lean_closure_set(v___f_4269_, 5, v___f_4268_);
    v___x_4270_ = lean_apply_4(
        v_toBind_4263_,
        lean_box(0),
        lean_box(0),
        v___x_4267_,
        v___f_4269_,
    );
    return v___x_4270_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___redArg___boxed(
    mut v_inst_4271_: *mut LeanObject,
    mut v_t_4272_: *mut LeanObject,
    mut v_init_4273_: *mut LeanObject,
    mut v_f_4274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4275_: *mut LeanObject = core::ptr::null_mut();
    v_res_4275_ =
        l_Lean_PersistentArray_forIn___redArg(v_inst_4271_, v_t_4272_, v_init_4273_, v_f_4274_);
    lean_dec_ref(v_t_4272_);
    return v_res_4275_;
}
pub unsafe fn l_Lean_PersistentArray_forIn(
    mut v_00_u03b1_4276_: *mut LeanObject,
    mut v_m_4277_: *mut LeanObject,
    mut v_inst_4278_: *mut LeanObject,
    mut v_00_u03b2_4279_: *mut LeanObject,
    mut v_t_4280_: *mut LeanObject,
    mut v_init_4281_: *mut LeanObject,
    mut v_f_4282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    v___x_4283_ =
        l_Lean_PersistentArray_forIn___redArg(v_inst_4278_, v_t_4280_, v_init_4281_, v_f_4282_);
    return v___x_4283_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___boxed(
    mut v_00_u03b1_4284_: *mut LeanObject,
    mut v_m_4285_: *mut LeanObject,
    mut v_inst_4286_: *mut LeanObject,
    mut v_00_u03b2_4287_: *mut LeanObject,
    mut v_t_4288_: *mut LeanObject,
    mut v_init_4289_: *mut LeanObject,
    mut v_f_4290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4291_: *mut LeanObject = core::ptr::null_mut();
    v_res_4291_ = l_Lean_PersistentArray_forIn(
        v_00_u03b1_4284_,
        v_m_4285_,
        v_inst_4286_,
        v_00_u03b2_4287_,
        v_t_4288_,
        v_init_4289_,
        v_f_4290_,
    );
    lean_dec_ref(v_t_4288_);
    return v_res_4291_;
}
pub unsafe fn l_Lean_PersistentArray_instForInOfMonad___redArg(
    mut v_inst_4292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    v___x_4293_ = lean_alloc_closure(
        l_Lean_PersistentArray_forIn___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___x_4293_, 0, lean_box(0));
    lean_closure_set(v___x_4293_, 1, lean_box(0));
    lean_closure_set(v___x_4293_, 2, v_inst_4292_);
    return v___x_4293_;
}
pub unsafe fn l_Lean_PersistentArray_instForInOfMonad(
    mut v_00_u03b1_4294_: *mut LeanObject,
    mut v_m_4295_: *mut LeanObject,
    mut v_inst_4296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    v___x_4297_ = lean_alloc_closure(
        l_Lean_PersistentArray_forIn___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___x_4297_, 0, lean_box(0));
    lean_closure_set(v___x_4297_, 1, lean_box(0));
    lean_closure_set(v___x_4297_, 2, v_inst_4296_);
    return v___x_4297_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___redArg___lam__0(
    mut v_toPure_4298_: *mut LeanObject,
    mut v_____s_4299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_4300_: *mut LeanObject = core::ptr::null_mut();
    v_fst_4300_ = lean_ctor_get(v_____s_4299_, 0);
    lean_inc(v_fst_4300_);
    lean_dec_ref(v_____s_4299_);
    if lean_obj_tag(v_fst_4300_) == 0 {
        let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
        v___x_4301_ = lean_box(0);
        v___x_4302_ = lean_apply_2(v_toPure_4298_, lean_box(0), v___x_4301_);
        return v___x_4302_;
    } else {
        let mut v_val_4303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
        v_val_4303_ = lean_ctor_get(v_fst_4300_, 0);
        lean_inc(v_val_4303_);
        lean_dec_ref_known(v_fst_4300_, 1);
        v___x_4304_ = lean_apply_2(v_toPure_4298_, lean_box(0), v_val_4303_);
        return v___x_4304_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___redArg___lam__1(
    mut v___x_4305_: *mut LeanObject,
    mut v_toPure_4306_: *mut LeanObject,
    mut v___x_4307_: *mut LeanObject,
    mut v_____do__lift_4308_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_4308_) == 1 {
        let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_4307_);
        v___x_4309_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4309_, 0, v_____do__lift_4308_);
        v___x_4310_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4310_, 0, v___x_4309_);
        lean_ctor_set(v___x_4310_, 1, v___x_4305_);
        v___x_4311_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4311_, 0, v___x_4310_);
        v___x_4312_ = lean_apply_2(v_toPure_4306_, lean_box(0), v___x_4311_);
        return v___x_4312_;
    } else {
        let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_____do__lift_4308_);
        v___x_4313_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4313_, 0, v___x_4307_);
        v___x_4314_ = lean_apply_2(v_toPure_4306_, lean_box(0), v___x_4313_);
        return v___x_4314_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(
    mut v_f_4315_: *mut LeanObject,
    mut v_toBind_4316_: *mut LeanObject,
    mut v___f_4317_: *mut LeanObject,
    mut v_a_4318_: *mut LeanObject,
    mut v_x_4319_: *mut LeanObject,
    mut v___y_4320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    v___x_4321_ = lean_apply_1(v_f_4315_, v_a_4318_);
    v___x_4322_ = lean_apply_4(
        v_toBind_4316_,
        lean_box(0),
        lean_box(0),
        v___x_4321_,
        v___f_4317_,
    );
    return v___x_4322_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed(
    mut v_f_4323_: *mut LeanObject,
    mut v_toBind_4324_: *mut LeanObject,
    mut v___f_4325_: *mut LeanObject,
    mut v_a_4326_: *mut LeanObject,
    mut v_x_4327_: *mut LeanObject,
    mut v___y_4328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4329_: *mut LeanObject = core::ptr::null_mut();
    v_res_4329_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(
        v_f_4323_,
        v_toBind_4324_,
        v___f_4325_,
        v_a_4326_,
        v_x_4327_,
        v___y_4328_,
    );
    lean_dec_ref(v___y_4328_);
    return v_res_4329_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed(
    mut v_inst_4333_: *mut LeanObject,
    mut v_f_4334_: *mut LeanObject,
    mut v_toBind_4335_: *mut LeanObject,
    mut v___f_4336_: *mut LeanObject,
    mut v_a_4337_: *mut LeanObject,
    mut v_x_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4340_: *mut LeanObject = core::ptr::null_mut();
    v_res_4340_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(
        v_inst_4333_,
        v_f_4334_,
        v_toBind_4335_,
        v___f_4336_,
        v_a_4337_,
        v_x_4338_,
        v___y_4339_,
    );
    lean_dec_ref(v___y_4339_);
    return v_res_4340_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___redArg(
    mut v_inst_4341_: *mut LeanObject,
    mut v_f_4342_: *mut LeanObject,
    mut v_x_4343_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4343_) == 0 {
        let mut v_toApplicative_4344_: *mut LeanObject = core::ptr::null_mut();
        let mut v_cs_4345_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_4346_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_4347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4350_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4351_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4352_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4353_: usize = 0;
        let mut v___x_4354_: usize = 0;
        let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_4344_ = lean_ctor_get(v_inst_4341_, 0);
        v_cs_4345_ = lean_ctor_get(v_x_4343_, 0);
        lean_inc_ref(v_cs_4345_);
        lean_dec_ref_known(v_x_4343_, 1);
        v_toBind_4346_ = lean_ctor_get(v_inst_4341_, 1);
        lean_inc_n(v_toBind_4346_, 2);
        v_toPure_4347_ = lean_ctor_get(v_toApplicative_4344_, 1);
        v___x_4348_ = lean_box(0);
        v___x_4349_ = l_Lean_PersistentArray_findSomeMAux___redArg___closed__0;
        lean_inc_n(v_toPure_4347_, 2);
        v___f_4350_ = lean_alloc_closure(
            l_Lean_PersistentArray_findSomeMAux___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_4350_, 0, v_toPure_4347_);
        v___f_4351_ = lean_alloc_closure(
            l_Lean_PersistentArray_findSomeMAux___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_4351_, 0, v___x_4348_);
        lean_closure_set(v___f_4351_, 1, v_toPure_4347_);
        lean_closure_set(v___f_4351_, 2, v___x_4349_);
        lean_inc_ref(v_inst_4341_);
        v___f_4352_ = lean_alloc_closure(
            l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed as *mut core::ffi::c_void,
            7,
            4,
        );
        lean_closure_set(v___f_4352_, 0, v_inst_4341_);
        lean_closure_set(v___f_4352_, 1, v_f_4342_);
        lean_closure_set(v___f_4352_, 2, v_toBind_4346_);
        lean_closure_set(v___f_4352_, 3, v___f_4351_);
        v_sz_4353_ = lean_array_size(v_cs_4345_);
        v___x_4354_ = 0usize;
        v___x_4355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            lean_box(0),
            lean_box(0),
            lean_box(0),
            v_inst_4341_,
            v_cs_4345_,
            v___f_4352_,
            v_sz_4353_,
            v___x_4354_,
            v___x_4349_,
        );
        v___x_4356_ = lean_apply_4(
            v_toBind_4346_,
            lean_box(0),
            lean_box(0),
            v___x_4355_,
            v___f_4350_,
        );
        return v___x_4356_;
    } else {
        let mut v_toApplicative_4357_: *mut LeanObject = core::ptr::null_mut();
        let mut v_vs_4358_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_4359_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_4360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4363_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4364_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4365_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4366_: usize = 0;
        let mut v___x_4367_: usize = 0;
        let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_4357_ = lean_ctor_get(v_inst_4341_, 0);
        v_vs_4358_ = lean_ctor_get(v_x_4343_, 0);
        lean_inc_ref(v_vs_4358_);
        lean_dec_ref_known(v_x_4343_, 1);
        v_toBind_4359_ = lean_ctor_get(v_inst_4341_, 1);
        lean_inc_n(v_toBind_4359_, 2);
        v_toPure_4360_ = lean_ctor_get(v_toApplicative_4357_, 1);
        v___x_4361_ = lean_box(0);
        v___x_4362_ = l_Lean_PersistentArray_findSomeMAux___redArg___closed__0;
        lean_inc_n(v_toPure_4360_, 2);
        v___f_4363_ = lean_alloc_closure(
            l_Lean_PersistentArray_findSomeMAux___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_4363_, 0, v_toPure_4360_);
        v___f_4364_ = lean_alloc_closure(
            l_Lean_PersistentArray_findSomeMAux___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_4364_, 0, v___x_4361_);
        lean_closure_set(v___f_4364_, 1, v_toPure_4360_);
        lean_closure_set(v___f_4364_, 2, v___x_4362_);
        v___f_4365_ = lean_alloc_closure(
            l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed as *mut core::ffi::c_void,
            6,
            3,
        );
        lean_closure_set(v___f_4365_, 0, v_f_4342_);
        lean_closure_set(v___f_4365_, 1, v_toBind_4359_);
        lean_closure_set(v___f_4365_, 2, v___f_4364_);
        v_sz_4366_ = lean_array_size(v_vs_4358_);
        v___x_4367_ = 0usize;
        v___x_4368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            lean_box(0),
            lean_box(0),
            lean_box(0),
            v_inst_4341_,
            v_vs_4358_,
            v___f_4365_,
            v_sz_4366_,
            v___x_4367_,
            v___x_4362_,
        );
        v___x_4369_ = lean_apply_4(
            v_toBind_4359_,
            lean_box(0),
            lean_box(0),
            v___x_4368_,
            v___f_4363_,
        );
        return v___x_4369_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(
    mut v_inst_4370_: *mut LeanObject,
    mut v_f_4371_: *mut LeanObject,
    mut v_toBind_4372_: *mut LeanObject,
    mut v___f_4373_: *mut LeanObject,
    mut v_a_4374_: *mut LeanObject,
    mut v_x_4375_: *mut LeanObject,
    mut v___y_4376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    v___x_4377_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_4370_, v_f_4371_, v_a_4374_);
    v___x_4378_ = lean_apply_4(
        v_toBind_4372_,
        lean_box(0),
        lean_box(0),
        v___x_4377_,
        v___f_4373_,
    );
    return v___x_4378_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeMAux(
    mut v_00_u03b1_4379_: *mut LeanObject,
    mut v_m_4380_: *mut LeanObject,
    mut v_inst_4381_: *mut LeanObject,
    mut v_00_u03b2_4382_: *mut LeanObject,
    mut v_f_4383_: *mut LeanObject,
    mut v_x_4384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    v___x_4385_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_4381_, v_f_4383_, v_x_4384_);
    return v___x_4385_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0(
    mut v_toPure_4386_: *mut LeanObject,
    mut v_____do__lift_4387_: *mut LeanObject,
    mut v_____s_4388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_4389_: *mut LeanObject = core::ptr::null_mut();
    v_fst_4389_ = lean_ctor_get(v_____s_4388_, 0);
    lean_inc(v_fst_4389_);
    lean_dec_ref(v_____s_4388_);
    if lean_obj_tag(v_fst_4389_) == 0 {
        let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
        v___x_4390_ = lean_apply_2(v_toPure_4386_, lean_box(0), v_____do__lift_4387_);
        return v___x_4390_;
    } else {
        let mut v_val_4391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_____do__lift_4387_);
        v_val_4391_ = lean_ctor_get(v_fst_4389_, 0);
        lean_inc(v_val_4391_);
        lean_dec_ref_known(v_fst_4389_, 1);
        v___x_4392_ = lean_apply_2(v_toPure_4386_, lean_box(0), v_val_4391_);
        return v___x_4392_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1(
    mut v___x_4393_: *mut LeanObject,
    mut v_toPure_4394_: *mut LeanObject,
    mut v___x_4395_: *mut LeanObject,
    mut v_____do__lift_4396_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_4396_) == 1 {
        let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_4395_);
        v___x_4397_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4397_, 0, v_____do__lift_4396_);
        v___x_4398_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4398_, 0, v___x_4397_);
        lean_ctor_set(v___x_4398_, 1, v___x_4393_);
        v___x_4399_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4399_, 0, v___x_4398_);
        v___x_4400_ = lean_apply_2(v_toPure_4394_, lean_box(0), v___x_4399_);
        return v___x_4400_;
    } else {
        let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_____do__lift_4396_);
        v___x_4401_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4401_, 0, v___x_4395_);
        v___x_4402_ = lean_apply_2(v_toPure_4394_, lean_box(0), v___x_4401_);
        return v___x_4402_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(
    mut v_f_4403_: *mut LeanObject,
    mut v_toBind_4404_: *mut LeanObject,
    mut v___f_4405_: *mut LeanObject,
    mut v_a_4406_: *mut LeanObject,
    mut v_x_4407_: *mut LeanObject,
    mut v___y_4408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    v___x_4409_ = lean_apply_1(v_f_4403_, v_a_4406_);
    v___x_4410_ = lean_apply_4(
        v_toBind_4404_,
        lean_box(0),
        lean_box(0),
        v___x_4409_,
        v___f_4405_,
    );
    return v___x_4410_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed(
    mut v_f_4411_: *mut LeanObject,
    mut v_toBind_4412_: *mut LeanObject,
    mut v___f_4413_: *mut LeanObject,
    mut v_a_4414_: *mut LeanObject,
    mut v_x_4415_: *mut LeanObject,
    mut v___y_4416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4417_: *mut LeanObject = core::ptr::null_mut();
    v_res_4417_ = l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(
        v_f_4411_,
        v_toBind_4412_,
        v___f_4413_,
        v_a_4414_,
        v_x_4415_,
        v___y_4416_,
    );
    lean_dec_ref(v___y_4416_);
    return v_res_4417_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3(
    mut v_toPure_4418_: *mut LeanObject,
    mut v_f_4419_: *mut LeanObject,
    mut v_toBind_4420_: *mut LeanObject,
    mut v_tail_4421_: *mut LeanObject,
    mut v_inst_4422_: *mut LeanObject,
    mut v_____do__lift_4423_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_4423_) == 0 {
        let mut v___f_4424_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4428_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4429_: usize = 0;
        let mut v___x_4430_: usize = 0;
        let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_4418_);
        v___f_4424_ = lean_alloc_closure(
            l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_4424_, 0, v_toPure_4418_);
        lean_closure_set(v___f_4424_, 1, v_____do__lift_4423_);
        v___x_4425_ = lean_box(0);
        v___x_4426_ = l_Lean_PersistentArray_findSomeMAux___redArg___closed__0;
        v___f_4427_ = lean_alloc_closure(
            l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_4427_, 0, v___x_4425_);
        lean_closure_set(v___f_4427_, 1, v_toPure_4418_);
        lean_closure_set(v___f_4427_, 2, v___x_4426_);
        lean_inc(v_toBind_4420_);
        v___f_4428_ = lean_alloc_closure(
            l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed
                as *mut core::ffi::c_void,
            6,
            3,
        );
        lean_closure_set(v___f_4428_, 0, v_f_4419_);
        lean_closure_set(v___f_4428_, 1, v_toBind_4420_);
        lean_closure_set(v___f_4428_, 2, v___f_4427_);
        v_sz_4429_ = lean_array_size(v_tail_4421_);
        v___x_4430_ = 0usize;
        v___x_4431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            lean_box(0),
            lean_box(0),
            lean_box(0),
            v_inst_4422_,
            v_tail_4421_,
            v___f_4428_,
            v_sz_4429_,
            v___x_4430_,
            v___x_4426_,
        );
        v___x_4432_ = lean_apply_4(
            v_toBind_4420_,
            lean_box(0),
            lean_box(0),
            v___x_4431_,
            v___f_4424_,
        );
        return v___x_4432_;
    } else {
        let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_4422_);
        lean_dec_ref(v_tail_4421_);
        lean_dec(v_toBind_4420_);
        lean_dec(v_f_4419_);
        v___x_4433_ = lean_apply_2(v_toPure_4418_, lean_box(0), v_____do__lift_4423_);
        return v___x_4433_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f___redArg(
    mut v_inst_4434_: *mut LeanObject,
    mut v_t_4435_: *mut LeanObject,
    mut v_f_4436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4437_ = lean_ctor_get(v_inst_4434_, 0);
    v_toBind_4438_ = lean_ctor_get(v_inst_4434_, 1);
    lean_inc_n(v_toBind_4438_, 2);
    v_root_4439_ = lean_ctor_get(v_t_4435_, 0);
    lean_inc_ref(v_root_4439_);
    v_tail_4440_ = lean_ctor_get(v_t_4435_, 1);
    lean_inc_ref(v_tail_4440_);
    lean_dec_ref(v_t_4435_);
    v_toPure_4441_ = lean_ctor_get(v_toApplicative_4437_, 1);
    lean_inc(v_toPure_4441_);
    lean_inc(v_f_4436_);
    lean_inc_ref(v_inst_4434_);
    v___x_4442_ =
        l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_4434_, v_f_4436_, v_root_4439_);
    v___f_4443_ = lean_alloc_closure(
        l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_4443_, 0, v_toPure_4441_);
    lean_closure_set(v___f_4443_, 1, v_f_4436_);
    lean_closure_set(v___f_4443_, 2, v_toBind_4438_);
    lean_closure_set(v___f_4443_, 3, v_tail_4440_);
    lean_closure_set(v___f_4443_, 4, v_inst_4434_);
    v___x_4444_ = lean_apply_4(
        v_toBind_4438_,
        lean_box(0),
        lean_box(0),
        v___x_4442_,
        v___f_4443_,
    );
    return v___x_4444_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeM_x3f(
    mut v_00_u03b1_4445_: *mut LeanObject,
    mut v_m_4446_: *mut LeanObject,
    mut v_inst_4447_: *mut LeanObject,
    mut v_00_u03b2_4448_: *mut LeanObject,
    mut v_t_4449_: *mut LeanObject,
    mut v_f_4450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    v___x_4451_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_4447_, v_t_4449_, v_f_4450_);
    return v___x_4451_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevMAux___redArg(
    mut v_inst_4452_: *mut LeanObject,
    mut v_f_4453_: *mut LeanObject,
    mut v_x_4454_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4454_) == 0 {
        let mut v_cs_4455_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4456_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
        v_cs_4455_ = lean_ctor_get(v_x_4454_, 0);
        lean_inc_ref(v_cs_4455_);
        lean_dec_ref_known(v_x_4454_, 1);
        lean_inc_ref(v_inst_4452_);
        v___f_4456_ = lean_alloc_closure(
            l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_4456_, 0, v_inst_4452_);
        lean_closure_set(v___f_4456_, 1, v_f_4453_);
        v___x_4457_ = lean_array_get_size(v_cs_4455_);
        v___x_4458_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
            lean_box(0),
            lean_box(0),
            lean_box(0),
            v_inst_4452_,
            v___f_4456_,
            v_cs_4455_,
            v___x_4457_,
            lean_box(0),
        );
        return v___x_4458_;
    } else {
        let mut v_vs_4459_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
        v_vs_4459_ = lean_ctor_get(v_x_4454_, 0);
        lean_inc_ref(v_vs_4459_);
        lean_dec_ref_known(v_x_4454_, 1);
        v___x_4460_ = lean_array_get_size(v_vs_4459_);
        v___x_4461_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
            lean_box(0),
            lean_box(0),
            lean_box(0),
            v_inst_4452_,
            v_f_4453_,
            v_vs_4459_,
            v___x_4460_,
            lean_box(0),
        );
        return v___x_4461_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0(
    mut v_inst_4462_: *mut LeanObject,
    mut v_f_4463_: *mut LeanObject,
    mut v_c_4464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    v___x_4465_ =
        l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_4462_, v_f_4463_, v_c_4464_);
    return v___x_4465_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevMAux(
    mut v_00_u03b1_4466_: *mut LeanObject,
    mut v_m_4467_: *mut LeanObject,
    mut v_inst_4468_: *mut LeanObject,
    mut v_00_u03b2_4469_: *mut LeanObject,
    mut v_f_4470_: *mut LeanObject,
    mut v_x_4471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    v___x_4472_ =
        l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_4468_, v_f_4470_, v_x_4471_);
    return v___x_4472_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0(
    mut v_inst_4473_: *mut LeanObject,
    mut v_f_4474_: *mut LeanObject,
    mut v_root_4475_: *mut LeanObject,
    mut v_toPure_4476_: *mut LeanObject,
    mut v_____do__lift_4477_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_4477_) == 0 {
        let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_4476_);
        v___x_4478_ =
            l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_4473_, v_f_4474_, v_root_4475_);
        return v___x_4478_;
    } else {
        let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_root_4475_);
        lean_dec(v_f_4474_);
        lean_dec_ref(v_inst_4473_);
        v___x_4479_ = lean_apply_2(v_toPure_4476_, lean_box(0), v_____do__lift_4477_);
        return v___x_4479_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevM_x3f___redArg(
    mut v_inst_4480_: *mut LeanObject,
    mut v_t_4481_: *mut LeanObject,
    mut v_f_4482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4483_ = lean_ctor_get(v_inst_4480_, 0);
    v_toBind_4484_ = lean_ctor_get(v_inst_4480_, 1);
    lean_inc(v_toBind_4484_);
    v_root_4485_ = lean_ctor_get(v_t_4481_, 0);
    lean_inc_ref(v_root_4485_);
    v_tail_4486_ = lean_ctor_get(v_t_4481_, 1);
    lean_inc_ref(v_tail_4486_);
    lean_dec_ref(v_t_4481_);
    v_toPure_4487_ = lean_ctor_get(v_toApplicative_4483_, 1);
    lean_inc(v_toPure_4487_);
    v___x_4488_ = lean_array_get_size(v_tail_4486_);
    lean_inc(v_f_4482_);
    lean_inc_ref(v_inst_4480_);
    v___x_4489_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_4480_,
        v_f_4482_,
        v_tail_4486_,
        v___x_4488_,
        lean_box(0),
    );
    v___f_4490_ = lean_alloc_closure(
        l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4490_, 0, v_inst_4480_);
    lean_closure_set(v___f_4490_, 1, v_f_4482_);
    lean_closure_set(v___f_4490_, 2, v_root_4485_);
    lean_closure_set(v___f_4490_, 3, v_toPure_4487_);
    v___x_4491_ = lean_apply_4(
        v_toBind_4484_,
        lean_box(0),
        lean_box(0),
        v___x_4489_,
        v___f_4490_,
    );
    return v___x_4491_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevM_x3f(
    mut v_00_u03b1_4492_: *mut LeanObject,
    mut v_m_4493_: *mut LeanObject,
    mut v_inst_4494_: *mut LeanObject,
    mut v_00_u03b2_4495_: *mut LeanObject,
    mut v_t_4496_: *mut LeanObject,
    mut v_f_4497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    v___x_4498_ =
        l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_4494_, v_t_4496_, v_f_4497_);
    return v___x_4498_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___redArg___lam__1(
    mut v_f_4499_: *mut LeanObject,
    mut v_x_4500_: *mut LeanObject,
    mut v___y_4501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    v___x_4502_ = lean_apply_1(v_f_4499_, v___y_4501_);
    return v___x_4502_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___redArg(
    mut v_inst_4503_: *mut LeanObject,
    mut v_f_4504_: *mut LeanObject,
    mut v_x_4505_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4505_) == 0 {
        let mut v_cs_4506_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4510_: u8 = 0;
        v_cs_4506_ = lean_ctor_get(v_x_4505_, 0);
        lean_inc_ref(v_cs_4506_);
        lean_dec_ref_known(v_x_4505_, 1);
        v___x_4507_ = lean_unsigned_to_nat(0);
        v___x_4508_ = lean_array_get_size(v_cs_4506_);
        v___x_4509_ = lean_box(0);
        v___x_4510_ = lean_nat_dec_lt(v___x_4507_, v___x_4508_);
        if v___x_4510_ == 0 {
            let mut v_toApplicative_4511_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_4512_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_cs_4506_);
            lean_dec(v_f_4504_);
            v_toApplicative_4511_ = lean_ctor_get(v_inst_4503_, 0);
            lean_inc_ref(v_toApplicative_4511_);
            lean_dec_ref(v_inst_4503_);
            v_toPure_4512_ = lean_ctor_get(v_toApplicative_4511_, 1);
            lean_inc(v_toPure_4512_);
            lean_dec_ref(v_toApplicative_4511_);
            v___x_4513_ = lean_apply_2(v_toPure_4512_, lean_box(0), v___x_4509_);
            return v___x_4513_;
        } else {
            let mut v___f_4514_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4515_: u8 = 0;
            lean_inc_ref(v_inst_4503_);
            v___f_4514_ = lean_alloc_closure(
                l_Lean_PersistentArray_forMAux___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                2,
            );
            lean_closure_set(v___f_4514_, 0, v_inst_4503_);
            lean_closure_set(v___f_4514_, 1, v_f_4504_);
            v___x_4515_ = lean_nat_dec_le(v___x_4508_, v___x_4508_);
            if v___x_4515_ == 0 {
                if v___x_4510_ == 0 {
                    let mut v_toApplicative_4516_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_toPure_4517_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v___f_4514_);
                    lean_dec_ref(v_cs_4506_);
                    v_toApplicative_4516_ = lean_ctor_get(v_inst_4503_, 0);
                    lean_inc_ref(v_toApplicative_4516_);
                    lean_dec_ref(v_inst_4503_);
                    v_toPure_4517_ = lean_ctor_get(v_toApplicative_4516_, 1);
                    lean_inc(v_toPure_4517_);
                    lean_dec_ref(v_toApplicative_4516_);
                    v___x_4518_ = lean_apply_2(v_toPure_4517_, lean_box(0), v___x_4509_);
                    return v___x_4518_;
                } else {
                    let mut v___x_4519_: usize = 0;
                    let mut v___x_4520_: usize = 0;
                    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4519_ = 0usize;
                    v___x_4520_ = lean_usize_of_nat(v___x_4508_);
                    v___x_4521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
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
                let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
                v___x_4522_ = 0usize;
                v___x_4523_ = lean_usize_of_nat(v___x_4508_);
                v___x_4524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
        let mut v_vs_4525_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4529_: u8 = 0;
        v_vs_4525_ = lean_ctor_get(v_x_4505_, 0);
        lean_inc_ref(v_vs_4525_);
        lean_dec_ref_known(v_x_4505_, 1);
        v___x_4526_ = lean_unsigned_to_nat(0);
        v___x_4527_ = lean_array_get_size(v_vs_4525_);
        v___x_4528_ = lean_box(0);
        v___x_4529_ = lean_nat_dec_lt(v___x_4526_, v___x_4527_);
        if v___x_4529_ == 0 {
            let mut v_toApplicative_4530_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_4531_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_vs_4525_);
            lean_dec(v_f_4504_);
            v_toApplicative_4530_ = lean_ctor_get(v_inst_4503_, 0);
            lean_inc_ref(v_toApplicative_4530_);
            lean_dec_ref(v_inst_4503_);
            v_toPure_4531_ = lean_ctor_get(v_toApplicative_4530_, 1);
            lean_inc(v_toPure_4531_);
            lean_dec_ref(v_toApplicative_4530_);
            v___x_4532_ = lean_apply_2(v_toPure_4531_, lean_box(0), v___x_4528_);
            return v___x_4532_;
        } else {
            let mut v___f_4533_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4534_: u8 = 0;
            v___f_4533_ = lean_alloc_closure(
                l_Lean_PersistentArray_forMAux___redArg___lam__1 as *mut core::ffi::c_void,
                3,
                1,
            );
            lean_closure_set(v___f_4533_, 0, v_f_4504_);
            v___x_4534_ = lean_nat_dec_le(v___x_4527_, v___x_4527_);
            if v___x_4534_ == 0 {
                if v___x_4529_ == 0 {
                    let mut v_toApplicative_4535_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_toPure_4536_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v___f_4533_);
                    lean_dec_ref(v_vs_4525_);
                    v_toApplicative_4535_ = lean_ctor_get(v_inst_4503_, 0);
                    lean_inc_ref(v_toApplicative_4535_);
                    lean_dec_ref(v_inst_4503_);
                    v_toPure_4536_ = lean_ctor_get(v_toApplicative_4535_, 1);
                    lean_inc(v_toPure_4536_);
                    lean_dec_ref(v_toApplicative_4535_);
                    v___x_4537_ = lean_apply_2(v_toPure_4536_, lean_box(0), v___x_4528_);
                    return v___x_4537_;
                } else {
                    let mut v___x_4538_: usize = 0;
                    let mut v___x_4539_: usize = 0;
                    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4538_ = 0usize;
                    v___x_4539_ = lean_usize_of_nat(v___x_4527_);
                    v___x_4540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
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
                let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
                v___x_4541_ = 0usize;
                v___x_4542_ = lean_usize_of_nat(v___x_4527_);
                v___x_4543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_4544_: *mut LeanObject,
    mut v_f_4545_: *mut LeanObject,
    mut v_x_4546_: *mut LeanObject,
    mut v___y_4547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    v___x_4548_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_4544_, v_f_4545_, v___y_4547_);
    return v___x_4548_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux(
    mut v_00_u03b1_4549_: *mut LeanObject,
    mut v_m_4550_: *mut LeanObject,
    mut v_inst_4551_: *mut LeanObject,
    mut v_f_4552_: *mut LeanObject,
    mut v_x_4553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    v___x_4554_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_4551_, v_f_4552_, v_x_4553_);
    return v___x_4554_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___redArg___lam__0(
    mut v_f_4555_: *mut LeanObject,
    mut v_x_4556_: *mut LeanObject,
    mut v___y_4557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    v___x_4558_ = lean_apply_1(v_f_4555_, v___y_4557_);
    return v___x_4558_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___redArg___lam__1(
    mut v_tail_4559_: *mut LeanObject,
    mut v_toPure_4560_: *mut LeanObject,
    mut v_inst_4561_: *mut LeanObject,
    mut v___f_4562_: *mut LeanObject,
    mut v_x_4563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: u8 = 0;
    v___x_4564_ = lean_unsigned_to_nat(0);
    v___x_4565_ = lean_array_get_size(v_tail_4559_);
    v___x_4566_ = lean_box(0);
    v___x_4567_ = lean_nat_dec_lt(v___x_4564_, v___x_4565_);
    if v___x_4567_ == 0 {
        let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_4562_);
        lean_dec_ref(v_inst_4561_);
        lean_dec_ref(v_tail_4559_);
        v___x_4568_ = lean_apply_2(v_toPure_4560_, lean_box(0), v___x_4566_);
        return v___x_4568_;
    } else {
        let mut v___x_4569_: u8 = 0;
        v___x_4569_ = lean_nat_dec_le(v___x_4565_, v___x_4565_);
        if v___x_4569_ == 0 {
            if v___x_4567_ == 0 {
                let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___f_4562_);
                lean_dec_ref(v_inst_4561_);
                lean_dec_ref(v_tail_4559_);
                v___x_4570_ = lean_apply_2(v_toPure_4560_, lean_box(0), v___x_4566_);
                return v___x_4570_;
            } else {
                let mut v___x_4571_: usize = 0;
                let mut v___x_4572_: usize = 0;
                let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_toPure_4560_);
                v___x_4571_ = 0usize;
                v___x_4572_ = lean_usize_of_nat(v___x_4565_);
                v___x_4573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toPure_4560_);
            v___x_4574_ = 0usize;
            v___x_4575_ = lean_usize_of_nat(v___x_4565_);
            v___x_4576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_inst_4577_: *mut LeanObject,
    mut v_t_4578_: *mut LeanObject,
    mut v_f_4579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4580_ = lean_ctor_get(v_inst_4577_, 0);
    v_toPure_4581_ = lean_ctor_get(v_toApplicative_4580_, 1);
    v_toSeqRight_4582_ = lean_ctor_get(v_toApplicative_4580_, 4);
    lean_inc(v_toSeqRight_4582_);
    v_root_4583_ = lean_ctor_get(v_t_4578_, 0);
    lean_inc_ref(v_root_4583_);
    v_tail_4584_ = lean_ctor_get(v_t_4578_, 1);
    lean_inc_ref(v_tail_4584_);
    lean_dec_ref(v_t_4578_);
    lean_inc(v_f_4579_);
    v___f_4585_ = lean_alloc_closure(
        l_Lean_PersistentArray_forMFrom0___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4585_, 0, v_f_4579_);
    lean_inc_ref(v_inst_4577_);
    lean_inc(v_toPure_4581_);
    v___f_4586_ = lean_alloc_closure(
        l_Lean_PersistentArray_forMFrom0___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4586_, 0, v_tail_4584_);
    lean_closure_set(v___f_4586_, 1, v_toPure_4581_);
    lean_closure_set(v___f_4586_, 2, v_inst_4577_);
    lean_closure_set(v___f_4586_, 3, v___f_4585_);
    v___x_4587_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_4577_, v_f_4579_, v_root_4583_);
    v___x_4588_ = lean_apply_4(
        v_toSeqRight_4582_,
        lean_box(0),
        lean_box(0),
        v___x_4587_,
        v___f_4586_,
    );
    return v___x_4588_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0(
    mut v_00_u03b1_4589_: *mut LeanObject,
    mut v_m_4590_: *mut LeanObject,
    mut v_inst_4591_: *mut LeanObject,
    mut v_t_4592_: *mut LeanObject,
    mut v_f_4593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    v___x_4594_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_4591_, v_t_4592_, v_f_4593_);
    return v___x_4594_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(
    mut v_j_4595_: *mut LeanObject,
    mut v_cs_4596_: *mut LeanObject,
    mut v_toApplicative_4597_: *mut LeanObject,
    mut v_inst_4598_: *mut LeanObject,
    mut v___f_4599_: *mut LeanObject,
    mut v_____r_4600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: u8 = 0;
    v___x_4601_ = lean_unsigned_to_nat(1);
    v___x_4602_ = lean_nat_add(v_j_4595_, v___x_4601_);
    v___x_4603_ = lean_array_get_size(v_cs_4596_);
    v___x_4604_ = lean_box(0);
    v___x_4605_ = lean_nat_dec_lt(v___x_4602_, v___x_4603_);
    if v___x_4605_ == 0 {
        let mut v_toPure_4606_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_4602_);
        lean_dec(v___f_4599_);
        lean_dec_ref(v_inst_4598_);
        lean_dec_ref(v_cs_4596_);
        v_toPure_4606_ = lean_ctor_get(v_toApplicative_4597_, 1);
        lean_inc(v_toPure_4606_);
        lean_dec_ref(v_toApplicative_4597_);
        v___x_4607_ = lean_apply_2(v_toPure_4606_, lean_box(0), v___x_4604_);
        return v___x_4607_;
    } else {
        let mut v___x_4608_: u8 = 0;
        v___x_4608_ = lean_nat_dec_le(v___x_4603_, v___x_4603_);
        if v___x_4608_ == 0 {
            if v___x_4605_ == 0 {
                let mut v_toPure_4609_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_4602_);
                lean_dec(v___f_4599_);
                lean_dec_ref(v_inst_4598_);
                lean_dec_ref(v_cs_4596_);
                v_toPure_4609_ = lean_ctor_get(v_toApplicative_4597_, 1);
                lean_inc(v_toPure_4609_);
                lean_dec_ref(v_toApplicative_4597_);
                v___x_4610_ = lean_apply_2(v_toPure_4609_, lean_box(0), v___x_4604_);
                return v___x_4610_;
            } else {
                let mut v___x_4611_: usize = 0;
                let mut v___x_4612_: usize = 0;
                let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toApplicative_4597_);
                v___x_4611_ = lean_usize_of_nat(v___x_4602_);
                lean_dec(v___x_4602_);
                v___x_4612_ = lean_usize_of_nat(v___x_4603_);
                v___x_4613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_toApplicative_4597_);
            v___x_4614_ = lean_usize_of_nat(v___x_4602_);
            lean_dec(v___x_4602_);
            v___x_4615_ = lean_usize_of_nat(v___x_4603_);
            v___x_4616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_j_4617_: *mut LeanObject,
    mut v_cs_4618_: *mut LeanObject,
    mut v_toApplicative_4619_: *mut LeanObject,
    mut v_inst_4620_: *mut LeanObject,
    mut v___f_4621_: *mut LeanObject,
    mut v_____r_4622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4623_: *mut LeanObject = core::ptr::null_mut();
    v_res_4623_ =
        l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(
            v_j_4617_,
            v_cs_4618_,
            v_toApplicative_4619_,
            v_inst_4620_,
            v___f_4621_,
            v_____r_4622_,
        );
    lean_dec(v_j_4617_);
    return v_res_4623_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(
    mut v_inst_4624_: *mut LeanObject,
    mut v_f_4625_: *mut LeanObject,
    mut v_x_4626_: *mut LeanObject,
    mut v_x_4627_: usize,
    mut v_x_4628_: usize,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4626_) == 0 {
        let mut v_toApplicative_4629_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_4630_: *mut LeanObject = core::ptr::null_mut();
        let mut v_cs_4631_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4632_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4634_: usize = 0;
        let mut v_j_4635_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4636_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4638_: usize = 0;
        let mut v___x_4639_: usize = 0;
        let mut v___x_4640_: usize = 0;
        let mut v___x_4641_: usize = 0;
        let mut v___x_4642_: usize = 0;
        let mut v___x_4643_: usize = 0;
        let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_4629_ = lean_ctor_get(v_inst_4624_, 0);
        v_toBind_4630_ = lean_ctor_get(v_inst_4624_, 1);
        lean_inc(v_toBind_4630_);
        v_cs_4631_ = lean_ctor_get(v_x_4626_, 0);
        lean_inc_ref_n(v_cs_4631_, 2);
        lean_dec_ref_known(v_x_4626_, 1);
        lean_inc(v_f_4625_);
        lean_inc_ref_n(v_inst_4624_, 2);
        v___f_4632_ = lean_alloc_closure(
            l_Lean_PersistentArray_forMAux___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_4632_, 0, v_inst_4624_);
        lean_closure_set(v___f_4632_, 1, v_f_4625_);
        v___x_4633_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0),
            core::ptr::addr_of_mut!(l_Lean_instInhabitedPersistentArrayNode___closed__0_once),
            _init_l_Lean_instInhabitedPersistentArrayNode___closed__0,
        );
        v___x_4634_ = lean_usize_shift_right(v_x_4627_, v_x_4628_);
        v_j_4635_ = lean_usize_to_nat(v___x_4634_);
        lean_inc_ref(v_toApplicative_4629_);
        lean_inc(v_j_4635_);
        v___f_4636_ = lean_alloc_closure(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 5);
        lean_closure_set(v___f_4636_, 0, v_j_4635_);
        lean_closure_set(v___f_4636_, 1, v_cs_4631_);
        lean_closure_set(v___f_4636_, 2, v_toApplicative_4629_);
        lean_closure_set(v___f_4636_, 3, v_inst_4624_);
        lean_closure_set(v___f_4636_, 4, v___f_4632_);
        v___x_4637_ = lean_array_get(v___x_4633_, v_cs_4631_, v_j_4635_);
        lean_dec(v_j_4635_);
        lean_dec_ref(v_cs_4631_);
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
        v___x_4645_ = lean_apply_4(
            v_toBind_4630_,
            lean_box(0),
            lean_box(0),
            v___x_4644_,
            v___f_4636_,
        );
        return v___x_4645_;
    } else {
        let mut v_toApplicative_4646_: *mut LeanObject = core::ptr::null_mut();
        let mut v_vs_4647_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4651_: u8 = 0;
        v_toApplicative_4646_ = lean_ctor_get(v_inst_4624_, 0);
        v_vs_4647_ = lean_ctor_get(v_x_4626_, 0);
        lean_inc_ref(v_vs_4647_);
        lean_dec_ref_known(v_x_4626_, 1);
        v___x_4648_ = lean_usize_to_nat(v_x_4627_);
        v___x_4649_ = lean_array_get_size(v_vs_4647_);
        v___x_4650_ = lean_box(0);
        v___x_4651_ = lean_nat_dec_lt(v___x_4648_, v___x_4649_);
        if v___x_4651_ == 0 {
            let mut v_toPure_4652_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_toApplicative_4646_);
            lean_dec(v___x_4648_);
            lean_dec_ref(v_vs_4647_);
            lean_dec(v_f_4625_);
            lean_dec_ref(v_inst_4624_);
            v_toPure_4652_ = lean_ctor_get(v_toApplicative_4646_, 1);
            lean_inc(v_toPure_4652_);
            lean_dec_ref(v_toApplicative_4646_);
            v___x_4653_ = lean_apply_2(v_toPure_4652_, lean_box(0), v___x_4650_);
            return v___x_4653_;
        } else {
            let mut v___f_4654_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4655_: u8 = 0;
            v___f_4654_ = lean_alloc_closure(
                l_Lean_PersistentArray_forMAux___redArg___lam__1 as *mut core::ffi::c_void,
                3,
                1,
            );
            lean_closure_set(v___f_4654_, 0, v_f_4625_);
            v___x_4655_ = lean_nat_dec_le(v___x_4649_, v___x_4649_);
            if v___x_4655_ == 0 {
                if v___x_4651_ == 0 {
                    let mut v_toPure_4656_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
                    lean_inc_ref(v_toApplicative_4646_);
                    lean_dec_ref(v___f_4654_);
                    lean_dec(v___x_4648_);
                    lean_dec_ref(v_vs_4647_);
                    lean_dec_ref(v_inst_4624_);
                    v_toPure_4656_ = lean_ctor_get(v_toApplicative_4646_, 1);
                    lean_inc(v_toPure_4656_);
                    lean_dec_ref(v_toApplicative_4646_);
                    v___x_4657_ = lean_apply_2(v_toPure_4656_, lean_box(0), v___x_4650_);
                    return v___x_4657_;
                } else {
                    let mut v___x_4658_: usize = 0;
                    let mut v___x_4659_: usize = 0;
                    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4658_ = lean_usize_of_nat(v___x_4648_);
                    lean_dec(v___x_4648_);
                    v___x_4659_ = lean_usize_of_nat(v___x_4649_);
                    v___x_4660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
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
                let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
                v___x_4661_ = lean_usize_of_nat(v___x_4648_);
                lean_dec(v___x_4648_);
                v___x_4662_ = lean_usize_of_nat(v___x_4649_);
                v___x_4663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_4664_: *mut LeanObject,
    mut v_f_4665_: *mut LeanObject,
    mut v_x_4666_: *mut LeanObject,
    mut v_x_4667_: *mut LeanObject,
    mut v_x_4668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_290__boxed_4669_: usize = 0;
    let mut v_x_291__boxed_4670_: usize = 0;
    let mut v_res_4671_: *mut LeanObject = core::ptr::null_mut();
    v_x_290__boxed_4669_ = lean_unbox_usize(v_x_4667_);
    lean_dec(v_x_4667_);
    v_x_291__boxed_4670_ = lean_unbox_usize(v_x_4668_);
    lean_dec(v_x_4668_);
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
    mut v_00_u03b1_4672_: *mut LeanObject,
    mut v_m_4673_: *mut LeanObject,
    mut v_inst_4674_: *mut LeanObject,
    mut v_f_4675_: *mut LeanObject,
    mut v_x_4676_: *mut LeanObject,
    mut v_x_4677_: usize,
    mut v_x_4678_: usize,
) -> *mut LeanObject {
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4680_: *mut LeanObject,
    mut v_m_4681_: *mut LeanObject,
    mut v_inst_4682_: *mut LeanObject,
    mut v_f_4683_: *mut LeanObject,
    mut v_x_4684_: *mut LeanObject,
    mut v_x_4685_: *mut LeanObject,
    mut v_x_4686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_360__boxed_4687_: usize = 0;
    let mut v_x_361__boxed_4688_: usize = 0;
    let mut v_res_4689_: *mut LeanObject = core::ptr::null_mut();
    v_x_360__boxed_4687_ = lean_unbox_usize(v_x_4685_);
    lean_dec(v_x_4685_);
    v_x_361__boxed_4688_ = lean_unbox_usize(v_x_4686_);
    lean_dec(v_x_4686_);
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
    mut v_tail_4690_: *mut LeanObject,
    mut v___x_4691_: *mut LeanObject,
    mut v_toApplicative_4692_: *mut LeanObject,
    mut v_inst_4693_: *mut LeanObject,
    mut v___f_4694_: *mut LeanObject,
    mut v_____r_4695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: u8 = 0;
    v___x_4696_ = lean_array_get_size(v_tail_4690_);
    v___x_4697_ = lean_box(0);
    v___x_4698_ = lean_nat_dec_lt(v___x_4691_, v___x_4696_);
    if v___x_4698_ == 0 {
        let mut v_toPure_4699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_4694_);
        lean_dec_ref(v_inst_4693_);
        lean_dec_ref(v_tail_4690_);
        v_toPure_4699_ = lean_ctor_get(v_toApplicative_4692_, 1);
        lean_inc(v_toPure_4699_);
        lean_dec_ref(v_toApplicative_4692_);
        v___x_4700_ = lean_apply_2(v_toPure_4699_, lean_box(0), v___x_4697_);
        return v___x_4700_;
    } else {
        let mut v___x_4701_: u8 = 0;
        v___x_4701_ = lean_nat_dec_le(v___x_4696_, v___x_4696_);
        if v___x_4701_ == 0 {
            if v___x_4698_ == 0 {
                let mut v_toPure_4702_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___f_4694_);
                lean_dec_ref(v_inst_4693_);
                lean_dec_ref(v_tail_4690_);
                v_toPure_4702_ = lean_ctor_get(v_toApplicative_4692_, 1);
                lean_inc(v_toPure_4702_);
                lean_dec_ref(v_toApplicative_4692_);
                v___x_4703_ = lean_apply_2(v_toPure_4702_, lean_box(0), v___x_4697_);
                return v___x_4703_;
            } else {
                let mut v___x_4704_: usize = 0;
                let mut v___x_4705_: usize = 0;
                let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toApplicative_4692_);
                v___x_4704_ = 0usize;
                v___x_4705_ = lean_usize_of_nat(v___x_4696_);
                v___x_4706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_toApplicative_4692_);
            v___x_4707_ = 0usize;
            v___x_4708_ = lean_usize_of_nat(v___x_4696_);
            v___x_4709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_tail_4710_: *mut LeanObject,
    mut v___x_4711_: *mut LeanObject,
    mut v_toApplicative_4712_: *mut LeanObject,
    mut v_inst_4713_: *mut LeanObject,
    mut v___f_4714_: *mut LeanObject,
    mut v_____r_4715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4716_: *mut LeanObject = core::ptr::null_mut();
    v_res_4716_ = l_Lean_PersistentArray_forM___redArg___lam__1(
        v_tail_4710_,
        v___x_4711_,
        v_toApplicative_4712_,
        v_inst_4713_,
        v___f_4714_,
        v_____r_4715_,
    );
    lean_dec(v___x_4711_);
    return v_res_4716_;
}
pub unsafe fn l_Lean_PersistentArray_forM___redArg(
    mut v_inst_4717_: *mut LeanObject,
    mut v_t_4718_: *mut LeanObject,
    mut v_f_4719_: *mut LeanObject,
    mut v_start_4720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: u8 = 0;
    v___x_4721_ = lean_unsigned_to_nat(0);
    v___x_4722_ = lean_nat_dec_eq(v_start_4720_, v___x_4721_);
    if v___x_4722_ == 0 {
        let mut v_root_4723_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_4724_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_4725_: usize = 0;
        let mut v_tailOff_4726_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4727_: u8 = 0;
        v_root_4723_ = lean_ctor_get(v_t_4718_, 0);
        lean_inc_ref(v_root_4723_);
        v_tail_4724_ = lean_ctor_get(v_t_4718_, 1);
        lean_inc_ref(v_tail_4724_);
        v_shift_4725_ = lean_ctor_get_usize(v_t_4718_, 4);
        v_tailOff_4726_ = lean_ctor_get(v_t_4718_, 3);
        lean_inc(v_tailOff_4726_);
        lean_dec_ref(v_t_4718_);
        v___x_4727_ = lean_nat_dec_le(v_tailOff_4726_, v_start_4720_);
        if v___x_4727_ == 0 {
            let mut v_toApplicative_4728_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_4729_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_4730_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_4731_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4732_: usize = 0;
            let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_tailOff_4726_);
            v_toApplicative_4728_ = lean_ctor_get(v_inst_4717_, 0);
            v_toBind_4729_ = lean_ctor_get(v_inst_4717_, 1);
            lean_inc(v_toBind_4729_);
            lean_inc(v_f_4719_);
            v___f_4730_ = lean_alloc_closure(
                l_Lean_PersistentArray_forMFrom0___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                1,
            );
            lean_closure_set(v___f_4730_, 0, v_f_4719_);
            lean_inc_ref(v_inst_4717_);
            lean_inc_ref(v_toApplicative_4728_);
            v___f_4731_ = lean_alloc_closure(
                l_Lean_PersistentArray_forM___redArg___lam__1___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___f_4731_, 0, v_tail_4724_);
            lean_closure_set(v___f_4731_, 1, v___x_4721_);
            lean_closure_set(v___f_4731_, 2, v_toApplicative_4728_);
            lean_closure_set(v___f_4731_, 3, v_inst_4717_);
            lean_closure_set(v___f_4731_, 4, v___f_4730_);
            v___x_4732_ = lean_usize_of_nat(v_start_4720_);
            v___x_4733_ =
                l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(
                    v_inst_4717_,
                    v_f_4719_,
                    v_root_4723_,
                    v___x_4732_,
                    v_shift_4725_,
                );
            v___x_4734_ = lean_apply_4(
                v_toBind_4729_,
                lean_box(0),
                lean_box(0),
                v___x_4733_,
                v___f_4731_,
            );
            return v___x_4734_;
        } else {
            let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4738_: u8 = 0;
            lean_dec_ref(v_root_4723_);
            v___x_4735_ = lean_nat_sub(v_start_4720_, v_tailOff_4726_);
            lean_dec(v_tailOff_4726_);
            v___x_4736_ = lean_array_get_size(v_tail_4724_);
            v___x_4737_ = lean_box(0);
            v___x_4738_ = lean_nat_dec_lt(v___x_4735_, v___x_4736_);
            if v___x_4738_ == 0 {
                let mut v_toApplicative_4739_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_4740_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_4735_);
                lean_dec_ref(v_tail_4724_);
                lean_dec(v_f_4719_);
                v_toApplicative_4739_ = lean_ctor_get(v_inst_4717_, 0);
                lean_inc_ref(v_toApplicative_4739_);
                lean_dec_ref(v_inst_4717_);
                v_toPure_4740_ = lean_ctor_get(v_toApplicative_4739_, 1);
                lean_inc(v_toPure_4740_);
                lean_dec_ref(v_toApplicative_4739_);
                v___x_4741_ = lean_apply_2(v_toPure_4740_, lean_box(0), v___x_4737_);
                return v___x_4741_;
            } else {
                let mut v___f_4742_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4743_: u8 = 0;
                v___f_4742_ = lean_alloc_closure(
                    l_Lean_PersistentArray_forMFrom0___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_4742_, 0, v_f_4719_);
                v___x_4743_ = lean_nat_dec_le(v___x_4736_, v___x_4736_);
                if v___x_4743_ == 0 {
                    if v___x_4738_ == 0 {
                        let mut v_toApplicative_4744_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_toPure_4745_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref(v___f_4742_);
                        lean_dec(v___x_4735_);
                        lean_dec_ref(v_tail_4724_);
                        v_toApplicative_4744_ = lean_ctor_get(v_inst_4717_, 0);
                        lean_inc_ref(v_toApplicative_4744_);
                        lean_dec_ref(v_inst_4717_);
                        v_toPure_4745_ = lean_ctor_get(v_toApplicative_4744_, 1);
                        lean_inc(v_toPure_4745_);
                        lean_dec_ref(v_toApplicative_4744_);
                        v___x_4746_ = lean_apply_2(v_toPure_4745_, lean_box(0), v___x_4737_);
                        return v___x_4746_;
                    } else {
                        let mut v___x_4747_: usize = 0;
                        let mut v___x_4748_: usize = 0;
                        let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
                        v___x_4747_ = lean_usize_of_nat(v___x_4735_);
                        lean_dec(v___x_4735_);
                        v___x_4748_ = lean_usize_of_nat(v___x_4736_);
                        v___x_4749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
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
                    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4750_ = lean_usize_of_nat(v___x_4735_);
                    lean_dec(v___x_4735_);
                    v___x_4751_ = lean_usize_of_nat(v___x_4736_);
                    v___x_4752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
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
        let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
        v___x_4753_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_4717_, v_t_4718_, v_f_4719_);
        return v___x_4753_;
    }
}
pub unsafe fn l_Lean_PersistentArray_forM___redArg___boxed(
    mut v_inst_4754_: *mut LeanObject,
    mut v_t_4755_: *mut LeanObject,
    mut v_f_4756_: *mut LeanObject,
    mut v_start_4757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4758_: *mut LeanObject = core::ptr::null_mut();
    v_res_4758_ =
        l_Lean_PersistentArray_forM___redArg(v_inst_4754_, v_t_4755_, v_f_4756_, v_start_4757_);
    lean_dec(v_start_4757_);
    return v_res_4758_;
}
pub unsafe fn l_Lean_PersistentArray_forM(
    mut v_00_u03b1_4759_: *mut LeanObject,
    mut v_m_4760_: *mut LeanObject,
    mut v_inst_4761_: *mut LeanObject,
    mut v_t_4762_: *mut LeanObject,
    mut v_f_4763_: *mut LeanObject,
    mut v_start_4764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    v___x_4765_ =
        l_Lean_PersistentArray_forM___redArg(v_inst_4761_, v_t_4762_, v_f_4763_, v_start_4764_);
    return v___x_4765_;
}
pub unsafe fn l_Lean_PersistentArray_forM___boxed(
    mut v_00_u03b1_4766_: *mut LeanObject,
    mut v_m_4767_: *mut LeanObject,
    mut v_inst_4768_: *mut LeanObject,
    mut v_t_4769_: *mut LeanObject,
    mut v_f_4770_: *mut LeanObject,
    mut v_start_4771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4772_: *mut LeanObject = core::ptr::null_mut();
    v_res_4772_ = l_Lean_PersistentArray_forM(
        v_00_u03b1_4766_,
        v_m_4767_,
        v_inst_4768_,
        v_t_4769_,
        v_f_4770_,
        v_start_4771_,
    );
    lean_dec(v_start_4771_);
    return v_res_4772_;
}
pub unsafe fn l_Lean_PersistentArray_foldl___redArg___lam__0(
    mut v_f_4773_: *mut LeanObject,
    mut v_x1_4774_: *mut LeanObject,
    mut v_x2_4775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    v___x_4776_ = lean_apply_2(v_f_4773_, v_x1_4774_, v_x2_4775_);
    return v___x_4776_;
}
pub unsafe fn l_Lean_PersistentArray_foldl___redArg(
    mut v_t_4796_: *mut LeanObject,
    mut v_f_4797_: *mut LeanObject,
    mut v_init_4798_: *mut LeanObject,
    mut v_start_4799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    v___f_4800_ = lean_alloc_closure(
        l_Lean_PersistentArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4800_, 0, v_f_4797_);
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
    mut v_t_4803_: *mut LeanObject,
    mut v_f_4804_: *mut LeanObject,
    mut v_init_4805_: *mut LeanObject,
    mut v_start_4806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4807_: *mut LeanObject = core::ptr::null_mut();
    v_res_4807_ =
        l_Lean_PersistentArray_foldl___redArg(v_t_4803_, v_f_4804_, v_init_4805_, v_start_4806_);
    lean_dec(v_start_4806_);
    return v_res_4807_;
}
pub unsafe fn l_Lean_PersistentArray_foldl(
    mut v_00_u03b1_4808_: *mut LeanObject,
    mut v_00_u03b2_4809_: *mut LeanObject,
    mut v_t_4810_: *mut LeanObject,
    mut v_f_4811_: *mut LeanObject,
    mut v_init_4812_: *mut LeanObject,
    mut v_start_4813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    v___f_4814_ = lean_alloc_closure(
        l_Lean_PersistentArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4814_, 0, v_f_4811_);
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
    mut v_00_u03b1_4817_: *mut LeanObject,
    mut v_00_u03b2_4818_: *mut LeanObject,
    mut v_t_4819_: *mut LeanObject,
    mut v_f_4820_: *mut LeanObject,
    mut v_init_4821_: *mut LeanObject,
    mut v_start_4822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4823_: *mut LeanObject = core::ptr::null_mut();
    v_res_4823_ = l_Lean_PersistentArray_foldl(
        v_00_u03b1_4817_,
        v_00_u03b2_4818_,
        v_t_4819_,
        v_f_4820_,
        v_init_4821_,
        v_start_4822_,
    );
    lean_dec(v_start_4822_);
    return v_res_4823_;
}
pub unsafe fn l_Lean_PersistentArray_foldr___redArg(
    mut v_t_4824_: *mut LeanObject,
    mut v_f_4825_: *mut LeanObject,
    mut v_init_4826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    v___f_4827_ = lean_alloc_closure(
        l_Lean_PersistentArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4827_, 0, v_f_4825_);
    v___x_4828_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_4829_ =
        l_Lean_PersistentArray_foldrM___redArg(v___x_4828_, v_t_4824_, v___f_4827_, v_init_4826_);
    return v___x_4829_;
}
pub unsafe fn l_Lean_PersistentArray_foldr(
    mut v_00_u03b1_4830_: *mut LeanObject,
    mut v_00_u03b2_4831_: *mut LeanObject,
    mut v_t_4832_: *mut LeanObject,
    mut v_f_4833_: *mut LeanObject,
    mut v_init_4834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    v___f_4835_ = lean_alloc_closure(
        l_Lean_PersistentArray_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4835_, 0, v_f_4833_);
    v___x_4836_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_4837_ =
        l_Lean_PersistentArray_foldrM___redArg(v___x_4836_, v_t_4832_, v___f_4835_, v_init_4834_);
    return v___x_4837_;
}
pub unsafe fn l_Lean_PersistentArray_filter___redArg___lam__0(
    mut v_p_4838_: *mut LeanObject,
    mut v_x1_4839_: *mut LeanObject,
    mut v_x2_4840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: u8 = 0;
    lean_inc(v_x2_4840_);
    v___x_4841_ = lean_apply_1(v_p_4838_, v_x2_4840_);
    v___x_4842_ = (lean_unbox(v___x_4841_) as u8);
    if v___x_4842_ == 0 {
        lean_dec(v_x2_4840_);
        return v_x1_4839_;
    } else {
        let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
        v___x_4843_ = l_Lean_PersistentArray_push___redArg(v_x1_4839_, v_x2_4840_);
        return v___x_4843_;
    }
}
pub unsafe fn l_Lean_PersistentArray_filter___redArg(
    mut v_as_4844_: *mut LeanObject,
    mut v_p_4845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    v___f_4846_ = lean_alloc_closure(
        l_Lean_PersistentArray_filter___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4846_, 0, v_p_4845_);
    v___x_4847_ = lean_unsigned_to_nat(32);
    v___x_4848_ = lean_mk_empty_array_with_capacity(v___x_4847_);
    lean_dec_ref(v___x_4848_);
    v___x_4849_ = lean_unsigned_to_nat(0);
    v___x_4850_ = lean_obj_once(
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
    mut v_00_u03b1_4853_: *mut LeanObject,
    mut v_as_4854_: *mut LeanObject,
    mut v_p_4855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    v___f_4856_ = lean_alloc_closure(
        l_Lean_PersistentArray_filter___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4856_, 0, v_p_4855_);
    v___x_4857_ = lean_unsigned_to_nat(32);
    v___x_4858_ = lean_mk_empty_array_with_capacity(v___x_4857_);
    lean_dec_ref(v___x_4858_);
    v___x_4859_ = lean_unsigned_to_nat(0);
    v___x_4860_ = lean_obj_once(
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
    mut v_as_4863_: *mut LeanObject,
    mut v_i_4864_: usize,
    mut v_stop_4865_: usize,
    mut v_b_4866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4867_: u8 = 0;
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: usize = 0;
    let mut v___x_4871_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4867_ = lean_usize_dec_eq(v_i_4864_, v_stop_4865_);
                if v___x_4867_ == 0 {
                    v___x_4868_ = lean_array_uget_borrowed(v_as_4863_, v_i_4864_);
                    lean_inc(v___x_4868_);
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
    mut v_as_4873_: *mut LeanObject,
    mut v_i_4874_: *mut LeanObject,
    mut v_stop_4875_: *mut LeanObject,
    mut v_b_4876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4877_: usize = 0;
    let mut v_stop_boxed_4878_: usize = 0;
    let mut v_res_4879_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4877_ = lean_unbox_usize(v_i_4874_);
    lean_dec(v_i_4874_);
    v_stop_boxed_4878_ = lean_unbox_usize(v_stop_4875_);
    lean_dec(v_stop_4875_);
    v_res_4879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_4873_, v_i_boxed_4877_, v_stop_boxed_4878_, v_b_4876_);
    lean_dec_ref(v_as_4873_);
    return v_res_4879_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(
    mut v_x_4880_: *mut LeanObject,
    mut v_x_4881_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4880_) == 0 {
        let mut v_cs_4882_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4885_: u8 = 0;
        v_cs_4882_ = lean_ctor_get(v_x_4880_, 0);
        v___x_4883_ = lean_unsigned_to_nat(0);
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
                    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4887_ = 0usize;
                    v___x_4888_ = lean_usize_of_nat(v___x_4884_);
                    v___x_4889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_4882_, v___x_4887_, v___x_4888_, v_x_4881_);
                    return v___x_4889_;
                }
            } else {
                let mut v___x_4890_: usize = 0;
                let mut v___x_4891_: usize = 0;
                let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
                v___x_4890_ = 0usize;
                v___x_4891_ = lean_usize_of_nat(v___x_4884_);
                v___x_4892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_4882_, v___x_4890_, v___x_4891_, v_x_4881_);
                return v___x_4892_;
            }
        }
    } else {
        let mut v_vs_4893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4896_: u8 = 0;
        v_vs_4893_ = lean_ctor_get(v_x_4880_, 0);
        v___x_4894_ = lean_unsigned_to_nat(0);
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
                    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4898_ = 0usize;
                    v___x_4899_ = lean_usize_of_nat(v___x_4895_);
                    v___x_4900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_4893_, v___x_4898_, v___x_4899_, v_x_4881_);
                    return v___x_4900_;
                }
            } else {
                let mut v___x_4901_: usize = 0;
                let mut v___x_4902_: usize = 0;
                let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
                v___x_4901_ = 0usize;
                v___x_4902_ = lean_usize_of_nat(v___x_4895_);
                v___x_4903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_4893_, v___x_4901_, v___x_4902_, v_x_4881_);
                return v___x_4903_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(
    mut v_as_4904_: *mut LeanObject,
    mut v_i_4905_: usize,
    mut v_stop_4906_: usize,
    mut v_b_4907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4908_: u8 = 0;
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_as_4914_: *mut LeanObject,
    mut v_i_4915_: *mut LeanObject,
    mut v_stop_4916_: *mut LeanObject,
    mut v_b_4917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4918_: usize = 0;
    let mut v_stop_boxed_4919_: usize = 0;
    let mut v_res_4920_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4918_ = lean_unbox_usize(v_i_4915_);
    lean_dec(v_i_4915_);
    v_stop_boxed_4919_ = lean_unbox_usize(v_stop_4916_);
    lean_dec(v_stop_4916_);
    v_res_4920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_4914_, v_i_boxed_4918_, v_stop_boxed_4919_, v_b_4917_);
    lean_dec_ref(v_as_4914_);
    return v_res_4920_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg___boxed(
    mut v_x_4921_: *mut LeanObject,
    mut v_x_4922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4923_: *mut LeanObject = core::ptr::null_mut();
    v_res_4923_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_4921_, v_x_4922_);
    lean_dec_ref(v_x_4921_);
    return v_res_4923_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(
    mut v_x_4924_: *mut LeanObject,
    mut v_x_4925_: usize,
    mut v_x_4926_: usize,
    mut v_x_4927_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4924_) == 0 {
        let mut v_cs_4928_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4930_: usize = 0;
        let mut v_j_4931_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4933_: usize = 0;
        let mut v___x_4934_: usize = 0;
        let mut v___x_4935_: usize = 0;
        let mut v___x_4936_: usize = 0;
        let mut v___x_4937_: usize = 0;
        let mut v___x_4938_: usize = 0;
        let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4943_: u8 = 0;
        v_cs_4928_ = lean_ctor_get(v_x_4924_, 0);
        v___x_4929_ = lean_obj_once(
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
        v___x_4940_ = lean_unsigned_to_nat(1);
        v___x_4941_ = lean_nat_add(v_j_4931_, v___x_4940_);
        lean_dec(v_j_4931_);
        v___x_4942_ = lean_array_get_size(v_cs_4928_);
        v___x_4943_ = lean_nat_dec_lt(v___x_4941_, v___x_4942_);
        if v___x_4943_ == 0 {
            lean_dec(v___x_4941_);
            return v___x_4939_;
        } else {
            let mut v___x_4944_: u8 = 0;
            v___x_4944_ = lean_nat_dec_le(v___x_4942_, v___x_4942_);
            if v___x_4944_ == 0 {
                if v___x_4943_ == 0 {
                    lean_dec(v___x_4941_);
                    return v___x_4939_;
                } else {
                    let mut v___x_4945_: usize = 0;
                    let mut v___x_4946_: usize = 0;
                    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4945_ = lean_usize_of_nat(v___x_4941_);
                    lean_dec(v___x_4941_);
                    v___x_4946_ = lean_usize_of_nat(v___x_4942_);
                    v___x_4947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_4928_, v___x_4945_, v___x_4946_, v___x_4939_);
                    return v___x_4947_;
                }
            } else {
                let mut v___x_4948_: usize = 0;
                let mut v___x_4949_: usize = 0;
                let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
                v___x_4948_ = lean_usize_of_nat(v___x_4941_);
                lean_dec(v___x_4941_);
                v___x_4949_ = lean_usize_of_nat(v___x_4942_);
                v___x_4950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_4928_, v___x_4948_, v___x_4949_, v___x_4939_);
                return v___x_4950_;
            }
        }
    } else {
        let mut v_vs_4951_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4954_: u8 = 0;
        v_vs_4951_ = lean_ctor_get(v_x_4924_, 0);
        v___x_4952_ = lean_usize_to_nat(v_x_4925_);
        v___x_4953_ = lean_array_get_size(v_vs_4951_);
        v___x_4954_ = lean_nat_dec_lt(v___x_4952_, v___x_4953_);
        if v___x_4954_ == 0 {
            lean_dec(v___x_4952_);
            return v_x_4927_;
        } else {
            let mut v___x_4955_: u8 = 0;
            v___x_4955_ = lean_nat_dec_le(v___x_4953_, v___x_4953_);
            if v___x_4955_ == 0 {
                if v___x_4954_ == 0 {
                    lean_dec(v___x_4952_);
                    return v_x_4927_;
                } else {
                    let mut v___x_4956_: usize = 0;
                    let mut v___x_4957_: usize = 0;
                    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4956_ = lean_usize_of_nat(v___x_4952_);
                    lean_dec(v___x_4952_);
                    v___x_4957_ = lean_usize_of_nat(v___x_4953_);
                    v___x_4958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_4951_, v___x_4956_, v___x_4957_, v_x_4927_);
                    return v___x_4958_;
                }
            } else {
                let mut v___x_4959_: usize = 0;
                let mut v___x_4960_: usize = 0;
                let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
                v___x_4959_ = lean_usize_of_nat(v___x_4952_);
                lean_dec(v___x_4952_);
                v___x_4960_ = lean_usize_of_nat(v___x_4953_);
                v___x_4961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_4951_, v___x_4959_, v___x_4960_, v_x_4927_);
                return v___x_4961_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg___boxed(
    mut v_x_4962_: *mut LeanObject,
    mut v_x_4963_: *mut LeanObject,
    mut v_x_4964_: *mut LeanObject,
    mut v_x_4965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1497__boxed_4966_: usize = 0;
    let mut v_x_1498__boxed_4967_: usize = 0;
    let mut v_res_4968_: *mut LeanObject = core::ptr::null_mut();
    v_x_1497__boxed_4966_ = lean_unbox_usize(v_x_4963_);
    lean_dec(v_x_4963_);
    v_x_1498__boxed_4967_ = lean_unbox_usize(v_x_4964_);
    lean_dec(v_x_4964_);
    v_res_4968_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_4962_, v_x_1497__boxed_4966_, v_x_1498__boxed_4967_, v_x_4965_);
    lean_dec_ref(v_x_4962_);
    return v_res_4968_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(
    mut v_t_4969_: *mut LeanObject,
    mut v_init_4970_: *mut LeanObject,
    mut v_start_4971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: u8 = 0;
    v___x_4972_ = lean_unsigned_to_nat(0);
    v___x_4973_ = lean_nat_dec_eq(v_start_4971_, v___x_4972_);
    if v___x_4973_ == 0 {
        let mut v_root_4974_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_4975_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_4976_: usize = 0;
        let mut v_tailOff_4977_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4978_: u8 = 0;
        v_root_4974_ = lean_ctor_get(v_t_4969_, 0);
        v_tail_4975_ = lean_ctor_get(v_t_4969_, 1);
        v_shift_4976_ = lean_ctor_get_usize(v_t_4969_, 4);
        v_tailOff_4977_ = lean_ctor_get(v_t_4969_, 3);
        v___x_4978_ = lean_nat_dec_le(v_tailOff_4977_, v_start_4971_);
        if v___x_4978_ == 0 {
            let mut v___x_4979_: usize = 0;
            let mut v___x_4980_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
                        v___x_4984_ = 0usize;
                        v___x_4985_ = lean_usize_of_nat(v___x_4981_);
                        v___x_4986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_4975_, v___x_4984_, v___x_4985_, v___x_4980_);
                        return v___x_4986_;
                    }
                } else {
                    let mut v___x_4987_: usize = 0;
                    let mut v___x_4988_: usize = 0;
                    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4987_ = 0usize;
                    v___x_4988_ = lean_usize_of_nat(v___x_4981_);
                    v___x_4989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_4975_, v___x_4987_, v___x_4988_, v___x_4980_);
                    return v___x_4989_;
                }
            }
        } else {
            let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4992_: u8 = 0;
            v___x_4990_ = lean_nat_sub(v_start_4971_, v_tailOff_4977_);
            v___x_4991_ = lean_array_get_size(v_tail_4975_);
            v___x_4992_ = lean_nat_dec_lt(v___x_4990_, v___x_4991_);
            if v___x_4992_ == 0 {
                lean_dec(v___x_4990_);
                return v_init_4970_;
            } else {
                let mut v___x_4993_: u8 = 0;
                v___x_4993_ = lean_nat_dec_le(v___x_4991_, v___x_4991_);
                if v___x_4993_ == 0 {
                    if v___x_4992_ == 0 {
                        lean_dec(v___x_4990_);
                        return v_init_4970_;
                    } else {
                        let mut v___x_4994_: usize = 0;
                        let mut v___x_4995_: usize = 0;
                        let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
                        v___x_4994_ = lean_usize_of_nat(v___x_4990_);
                        lean_dec(v___x_4990_);
                        v___x_4995_ = lean_usize_of_nat(v___x_4991_);
                        v___x_4996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_4975_, v___x_4994_, v___x_4995_, v_init_4970_);
                        return v___x_4996_;
                    }
                } else {
                    let mut v___x_4997_: usize = 0;
                    let mut v___x_4998_: usize = 0;
                    let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4997_ = lean_usize_of_nat(v___x_4990_);
                    lean_dec(v___x_4990_);
                    v___x_4998_ = lean_usize_of_nat(v___x_4991_);
                    v___x_4999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_4975_, v___x_4997_, v___x_4998_, v_init_4970_);
                    return v___x_4999_;
                }
            }
        }
    } else {
        let mut v_root_5000_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_5001_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5004_: u8 = 0;
        v_root_5000_ = lean_ctor_get(v_t_4969_, 0);
        v_tail_5001_ = lean_ctor_get(v_t_4969_, 1);
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
                    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5006_ = 0usize;
                    v___x_5007_ = lean_usize_of_nat(v___x_5003_);
                    v___x_5008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_5001_, v___x_5006_, v___x_5007_, v___x_5002_);
                    return v___x_5008_;
                }
            } else {
                let mut v___x_5009_: usize = 0;
                let mut v___x_5010_: usize = 0;
                let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
                v___x_5009_ = 0usize;
                v___x_5010_ = lean_usize_of_nat(v___x_5003_);
                v___x_5011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_5001_, v___x_5009_, v___x_5010_, v___x_5002_);
                return v___x_5011_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg___boxed(
    mut v_t_5012_: *mut LeanObject,
    mut v_init_5013_: *mut LeanObject,
    mut v_start_5014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5015_: *mut LeanObject = core::ptr::null_mut();
    v_res_5015_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(
            v_t_5012_,
            v_init_5013_,
            v_start_5014_,
        );
    lean_dec(v_start_5014_);
    lean_dec_ref(v_t_5012_);
    return v_res_5015_;
}
pub unsafe fn l_Lean_PersistentArray_toArray___redArg(
    mut v_t_5016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    v___x_5017_ = lean_unsigned_to_nat(0);
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
    mut v_t_5020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5021_: *mut LeanObject = core::ptr::null_mut();
    v_res_5021_ = l_Lean_PersistentArray_toArray___redArg(v_t_5020_);
    lean_dec_ref(v_t_5020_);
    return v_res_5021_;
}
pub unsafe fn l_Lean_PersistentArray_toArray(
    mut v_00_u03b1_5022_: *mut LeanObject,
    mut v_t_5023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    v___x_5024_ = l_Lean_PersistentArray_toArray___redArg(v_t_5023_);
    return v___x_5024_;
}
pub unsafe fn l_Lean_PersistentArray_toArray___boxed(
    mut v_00_u03b1_5025_: *mut LeanObject,
    mut v_t_5026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5027_: *mut LeanObject = core::ptr::null_mut();
    v_res_5027_ = l_Lean_PersistentArray_toArray(v_00_u03b1_5025_, v_t_5026_);
    lean_dec_ref(v_t_5026_);
    return v_res_5027_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(
    mut v_00_u03b1_5028_: *mut LeanObject,
    mut v_t_5029_: *mut LeanObject,
    mut v_init_5030_: *mut LeanObject,
    mut v_start_5031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    v___x_5032_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(
            v_t_5029_,
            v_init_5030_,
            v_start_5031_,
        );
    return v___x_5032_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___boxed(
    mut v_00_u03b1_5033_: *mut LeanObject,
    mut v_t_5034_: *mut LeanObject,
    mut v_init_5035_: *mut LeanObject,
    mut v_start_5036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5037_: *mut LeanObject = core::ptr::null_mut();
    v_res_5037_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(
        v_00_u03b1_5033_,
        v_t_5034_,
        v_init_5035_,
        v_start_5036_,
    );
    lean_dec(v_start_5036_);
    lean_dec_ref(v_t_5034_);
    return v_res_5037_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(
    mut v_00_u03b1_5038_: *mut LeanObject,
    mut v_x_5039_: *mut LeanObject,
    mut v_x_5040_: usize,
    mut v_x_5041_: usize,
    mut v_x_5042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    v___x_5043_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_5039_, v_x_5040_, v_x_5041_, v_x_5042_);
    return v___x_5043_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___boxed(
    mut v_00_u03b1_5044_: *mut LeanObject,
    mut v_x_5045_: *mut LeanObject,
    mut v_x_5046_: *mut LeanObject,
    mut v_x_5047_: *mut LeanObject,
    mut v_x_5048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1655__boxed_5049_: usize = 0;
    let mut v_x_1656__boxed_5050_: usize = 0;
    let mut v_res_5051_: *mut LeanObject = core::ptr::null_mut();
    v_x_1655__boxed_5049_ = lean_unbox_usize(v_x_5046_);
    lean_dec(v_x_5046_);
    v_x_1656__boxed_5050_ = lean_unbox_usize(v_x_5047_);
    lean_dec(v_x_5047_);
    v_res_5051_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(v_00_u03b1_5044_, v_x_5045_, v_x_1655__boxed_5049_, v_x_1656__boxed_5050_, v_x_5048_);
    lean_dec_ref(v_x_5045_);
    return v_res_5051_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(
    mut v_00_u03b1_5052_: *mut LeanObject,
    mut v_as_5053_: *mut LeanObject,
    mut v_i_5054_: usize,
    mut v_stop_5055_: usize,
    mut v_b_5056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    v___x_5057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_5053_, v_i_5054_, v_stop_5055_, v_b_5056_);
    return v___x_5057_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___boxed(
    mut v_00_u03b1_5058_: *mut LeanObject,
    mut v_as_5059_: *mut LeanObject,
    mut v_i_5060_: *mut LeanObject,
    mut v_stop_5061_: *mut LeanObject,
    mut v_b_5062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5063_: usize = 0;
    let mut v_stop_boxed_5064_: usize = 0;
    let mut v_res_5065_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5063_ = lean_unbox_usize(v_i_5060_);
    lean_dec(v_i_5060_);
    v_stop_boxed_5064_ = lean_unbox_usize(v_stop_5061_);
    lean_dec(v_stop_5061_);
    v_res_5065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(v_00_u03b1_5058_, v_as_5059_, v_i_boxed_5063_, v_stop_boxed_5064_, v_b_5062_);
    lean_dec_ref(v_as_5059_);
    return v_res_5065_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(
    mut v_00_u03b1_5066_: *mut LeanObject,
    mut v_x_5067_: *mut LeanObject,
    mut v_x_5068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    v___x_5069_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_5067_, v_x_5068_);
    return v___x_5069_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___boxed(
    mut v_00_u03b1_5070_: *mut LeanObject,
    mut v_x_5071_: *mut LeanObject,
    mut v_x_5072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5073_: *mut LeanObject = core::ptr::null_mut();
    v_res_5073_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(v_00_u03b1_5070_, v_x_5071_, v_x_5072_);
    lean_dec_ref(v_x_5071_);
    return v_res_5073_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(
    mut v_00_u03b1_5074_: *mut LeanObject,
    mut v_as_5075_: *mut LeanObject,
    mut v_i_5076_: usize,
    mut v_stop_5077_: usize,
    mut v_b_5078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    v___x_5079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_5075_, v_i_5076_, v_stop_5077_, v_b_5078_);
    return v___x_5079_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_5080_: *mut LeanObject,
    mut v_as_5081_: *mut LeanObject,
    mut v_i_5082_: *mut LeanObject,
    mut v_stop_5083_: *mut LeanObject,
    mut v_b_5084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5085_: usize = 0;
    let mut v_stop_boxed_5086_: usize = 0;
    let mut v_res_5087_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5085_ = lean_unbox_usize(v_i_5082_);
    lean_dec(v_i_5082_);
    v_stop_boxed_5086_ = lean_unbox_usize(v_stop_5083_);
    lean_dec(v_stop_5083_);
    v_res_5087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(v_00_u03b1_5080_, v_as_5081_, v_i_boxed_5085_, v_stop_boxed_5086_, v_b_5084_);
    lean_dec_ref(v_as_5081_);
    return v_res_5087_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(
    mut v_as_5088_: *mut LeanObject,
    mut v_i_5089_: usize,
    mut v_stop_5090_: usize,
    mut v_b_5091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5092_: u8 = 0;
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: usize = 0;
    let mut v___x_5096_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5092_ = lean_usize_dec_eq(v_i_5089_, v_stop_5090_);
                if v___x_5092_ == 0 {
                    v___x_5093_ = lean_array_uget_borrowed(v_as_5088_, v_i_5089_);
                    lean_inc(v___x_5093_);
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
    mut v_as_5098_: *mut LeanObject,
    mut v_i_5099_: *mut LeanObject,
    mut v_stop_5100_: *mut LeanObject,
    mut v_b_5101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5102_: usize = 0;
    let mut v_stop_boxed_5103_: usize = 0;
    let mut v_res_5104_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5102_ = lean_unbox_usize(v_i_5099_);
    lean_dec(v_i_5099_);
    v_stop_boxed_5103_ = lean_unbox_usize(v_stop_5100_);
    lean_dec(v_stop_5100_);
    v_res_5104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_5098_, v_i_boxed_5102_, v_stop_boxed_5103_, v_b_5101_);
    lean_dec_ref(v_as_5098_);
    return v_res_5104_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(
    mut v_x_5105_: *mut LeanObject,
    mut v_x_5106_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5105_) == 0 {
        let mut v_cs_5107_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5110_: u8 = 0;
        v_cs_5107_ = lean_ctor_get(v_x_5105_, 0);
        v___x_5108_ = lean_unsigned_to_nat(0);
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
                    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5112_ = 0usize;
                    v___x_5113_ = lean_usize_of_nat(v___x_5109_);
                    v___x_5114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_5107_, v___x_5112_, v___x_5113_, v_x_5106_);
                    return v___x_5114_;
                }
            } else {
                let mut v___x_5115_: usize = 0;
                let mut v___x_5116_: usize = 0;
                let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
                v___x_5115_ = 0usize;
                v___x_5116_ = lean_usize_of_nat(v___x_5109_);
                v___x_5117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_5107_, v___x_5115_, v___x_5116_, v_x_5106_);
                return v___x_5117_;
            }
        }
    } else {
        let mut v_vs_5118_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5121_: u8 = 0;
        v_vs_5118_ = lean_ctor_get(v_x_5105_, 0);
        v___x_5119_ = lean_unsigned_to_nat(0);
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
                    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5123_ = 0usize;
                    v___x_5124_ = lean_usize_of_nat(v___x_5120_);
                    v___x_5125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_5118_, v___x_5123_, v___x_5124_, v_x_5106_);
                    return v___x_5125_;
                }
            } else {
                let mut v___x_5126_: usize = 0;
                let mut v___x_5127_: usize = 0;
                let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
                v___x_5126_ = 0usize;
                v___x_5127_ = lean_usize_of_nat(v___x_5120_);
                v___x_5128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_5118_, v___x_5126_, v___x_5127_, v_x_5106_);
                return v___x_5128_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(
    mut v_as_5129_: *mut LeanObject,
    mut v_i_5130_: usize,
    mut v_stop_5131_: usize,
    mut v_b_5132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5133_: u8 = 0;
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_as_5139_: *mut LeanObject,
    mut v_i_5140_: *mut LeanObject,
    mut v_stop_5141_: *mut LeanObject,
    mut v_b_5142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5143_: usize = 0;
    let mut v_stop_boxed_5144_: usize = 0;
    let mut v_res_5145_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5143_ = lean_unbox_usize(v_i_5140_);
    lean_dec(v_i_5140_);
    v_stop_boxed_5144_ = lean_unbox_usize(v_stop_5141_);
    lean_dec(v_stop_5141_);
    v_res_5145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_5139_, v_i_boxed_5143_, v_stop_boxed_5144_, v_b_5142_);
    lean_dec_ref(v_as_5139_);
    return v_res_5145_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg___boxed(
    mut v_x_5146_: *mut LeanObject,
    mut v_x_5147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5148_: *mut LeanObject = core::ptr::null_mut();
    v_res_5148_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_5146_, v_x_5147_);
    lean_dec_ref(v_x_5146_);
    return v_res_5148_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(
    mut v_x_5149_: *mut LeanObject,
    mut v_x_5150_: usize,
    mut v_x_5151_: usize,
    mut v_x_5152_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5149_) == 0 {
        let mut v_cs_5153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5155_: usize = 0;
        let mut v_j_5156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5158_: usize = 0;
        let mut v___x_5159_: usize = 0;
        let mut v___x_5160_: usize = 0;
        let mut v___x_5161_: usize = 0;
        let mut v___x_5162_: usize = 0;
        let mut v___x_5163_: usize = 0;
        let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5168_: u8 = 0;
        v_cs_5153_ = lean_ctor_get(v_x_5149_, 0);
        v___x_5154_ = lean_obj_once(
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
        v___x_5165_ = lean_unsigned_to_nat(1);
        v___x_5166_ = lean_nat_add(v_j_5156_, v___x_5165_);
        lean_dec(v_j_5156_);
        v___x_5167_ = lean_array_get_size(v_cs_5153_);
        v___x_5168_ = lean_nat_dec_lt(v___x_5166_, v___x_5167_);
        if v___x_5168_ == 0 {
            lean_dec(v___x_5166_);
            return v___x_5164_;
        } else {
            let mut v___x_5169_: u8 = 0;
            v___x_5169_ = lean_nat_dec_le(v___x_5167_, v___x_5167_);
            if v___x_5169_ == 0 {
                if v___x_5168_ == 0 {
                    lean_dec(v___x_5166_);
                    return v___x_5164_;
                } else {
                    let mut v___x_5170_: usize = 0;
                    let mut v___x_5171_: usize = 0;
                    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5170_ = lean_usize_of_nat(v___x_5166_);
                    lean_dec(v___x_5166_);
                    v___x_5171_ = lean_usize_of_nat(v___x_5167_);
                    v___x_5172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_5153_, v___x_5170_, v___x_5171_, v___x_5164_);
                    return v___x_5172_;
                }
            } else {
                let mut v___x_5173_: usize = 0;
                let mut v___x_5174_: usize = 0;
                let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
                v___x_5173_ = lean_usize_of_nat(v___x_5166_);
                lean_dec(v___x_5166_);
                v___x_5174_ = lean_usize_of_nat(v___x_5167_);
                v___x_5175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_5153_, v___x_5173_, v___x_5174_, v___x_5164_);
                return v___x_5175_;
            }
        }
    } else {
        let mut v_vs_5176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5179_: u8 = 0;
        v_vs_5176_ = lean_ctor_get(v_x_5149_, 0);
        v___x_5177_ = lean_usize_to_nat(v_x_5150_);
        v___x_5178_ = lean_array_get_size(v_vs_5176_);
        v___x_5179_ = lean_nat_dec_lt(v___x_5177_, v___x_5178_);
        if v___x_5179_ == 0 {
            lean_dec(v___x_5177_);
            return v_x_5152_;
        } else {
            let mut v___x_5180_: u8 = 0;
            v___x_5180_ = lean_nat_dec_le(v___x_5178_, v___x_5178_);
            if v___x_5180_ == 0 {
                if v___x_5179_ == 0 {
                    lean_dec(v___x_5177_);
                    return v_x_5152_;
                } else {
                    let mut v___x_5181_: usize = 0;
                    let mut v___x_5182_: usize = 0;
                    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5181_ = lean_usize_of_nat(v___x_5177_);
                    lean_dec(v___x_5177_);
                    v___x_5182_ = lean_usize_of_nat(v___x_5178_);
                    v___x_5183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_5176_, v___x_5181_, v___x_5182_, v_x_5152_);
                    return v___x_5183_;
                }
            } else {
                let mut v___x_5184_: usize = 0;
                let mut v___x_5185_: usize = 0;
                let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
                v___x_5184_ = lean_usize_of_nat(v___x_5177_);
                lean_dec(v___x_5177_);
                v___x_5185_ = lean_usize_of_nat(v___x_5178_);
                v___x_5186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_5176_, v___x_5184_, v___x_5185_, v_x_5152_);
                return v___x_5186_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg___boxed(
    mut v_x_5187_: *mut LeanObject,
    mut v_x_5188_: *mut LeanObject,
    mut v_x_5189_: *mut LeanObject,
    mut v_x_5190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1523__boxed_5191_: usize = 0;
    let mut v_x_1524__boxed_5192_: usize = 0;
    let mut v_res_5193_: *mut LeanObject = core::ptr::null_mut();
    v_x_1523__boxed_5191_ = lean_unbox_usize(v_x_5188_);
    lean_dec(v_x_5188_);
    v_x_1524__boxed_5192_ = lean_unbox_usize(v_x_5189_);
    lean_dec(v_x_5189_);
    v_res_5193_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_5187_, v_x_1523__boxed_5191_, v_x_1524__boxed_5192_, v_x_5190_);
    lean_dec_ref(v_x_5187_);
    return v_res_5193_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(
    mut v_t_5194_: *mut LeanObject,
    mut v_init_5195_: *mut LeanObject,
    mut v_start_5196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: u8 = 0;
    v___x_5197_ = lean_unsigned_to_nat(0);
    v___x_5198_ = lean_nat_dec_eq(v_start_5196_, v___x_5197_);
    if v___x_5198_ == 0 {
        let mut v_root_5199_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_5200_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_5201_: usize = 0;
        let mut v_tailOff_5202_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5203_: u8 = 0;
        v_root_5199_ = lean_ctor_get(v_t_5194_, 0);
        v_tail_5200_ = lean_ctor_get(v_t_5194_, 1);
        v_shift_5201_ = lean_ctor_get_usize(v_t_5194_, 4);
        v_tailOff_5202_ = lean_ctor_get(v_t_5194_, 3);
        v___x_5203_ = lean_nat_dec_le(v_tailOff_5202_, v_start_5196_);
        if v___x_5203_ == 0 {
            let mut v___x_5204_: usize = 0;
            let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
                        v___x_5209_ = 0usize;
                        v___x_5210_ = lean_usize_of_nat(v___x_5206_);
                        v___x_5211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_5200_, v___x_5209_, v___x_5210_, v___x_5205_);
                        return v___x_5211_;
                    }
                } else {
                    let mut v___x_5212_: usize = 0;
                    let mut v___x_5213_: usize = 0;
                    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5212_ = 0usize;
                    v___x_5213_ = lean_usize_of_nat(v___x_5206_);
                    v___x_5214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_5200_, v___x_5212_, v___x_5213_, v___x_5205_);
                    return v___x_5214_;
                }
            }
        } else {
            let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5217_: u8 = 0;
            v___x_5215_ = lean_nat_sub(v_start_5196_, v_tailOff_5202_);
            v___x_5216_ = lean_array_get_size(v_tail_5200_);
            v___x_5217_ = lean_nat_dec_lt(v___x_5215_, v___x_5216_);
            if v___x_5217_ == 0 {
                lean_dec(v___x_5215_);
                return v_init_5195_;
            } else {
                let mut v___x_5218_: u8 = 0;
                v___x_5218_ = lean_nat_dec_le(v___x_5216_, v___x_5216_);
                if v___x_5218_ == 0 {
                    if v___x_5217_ == 0 {
                        lean_dec(v___x_5215_);
                        return v_init_5195_;
                    } else {
                        let mut v___x_5219_: usize = 0;
                        let mut v___x_5220_: usize = 0;
                        let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
                        v___x_5219_ = lean_usize_of_nat(v___x_5215_);
                        lean_dec(v___x_5215_);
                        v___x_5220_ = lean_usize_of_nat(v___x_5216_);
                        v___x_5221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_5200_, v___x_5219_, v___x_5220_, v_init_5195_);
                        return v___x_5221_;
                    }
                } else {
                    let mut v___x_5222_: usize = 0;
                    let mut v___x_5223_: usize = 0;
                    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5222_ = lean_usize_of_nat(v___x_5215_);
                    lean_dec(v___x_5215_);
                    v___x_5223_ = lean_usize_of_nat(v___x_5216_);
                    v___x_5224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_5200_, v___x_5222_, v___x_5223_, v_init_5195_);
                    return v___x_5224_;
                }
            }
        }
    } else {
        let mut v_root_5225_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_5226_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5229_: u8 = 0;
        v_root_5225_ = lean_ctor_get(v_t_5194_, 0);
        v_tail_5226_ = lean_ctor_get(v_t_5194_, 1);
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
                    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5231_ = 0usize;
                    v___x_5232_ = lean_usize_of_nat(v___x_5228_);
                    v___x_5233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_5226_, v___x_5231_, v___x_5232_, v___x_5227_);
                    return v___x_5233_;
                }
            } else {
                let mut v___x_5234_: usize = 0;
                let mut v___x_5235_: usize = 0;
                let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
                v___x_5234_ = 0usize;
                v___x_5235_ = lean_usize_of_nat(v___x_5228_);
                v___x_5236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_5226_, v___x_5234_, v___x_5235_, v___x_5227_);
                return v___x_5236_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg___boxed(
    mut v_t_5237_: *mut LeanObject,
    mut v_init_5238_: *mut LeanObject,
    mut v_start_5239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5240_: *mut LeanObject = core::ptr::null_mut();
    v_res_5240_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(
            v_t_5237_,
            v_init_5238_,
            v_start_5239_,
        );
    lean_dec(v_start_5239_);
    lean_dec_ref(v_t_5237_);
    return v_res_5240_;
}
pub unsafe fn l_Lean_PersistentArray_append___redArg(
    mut v_t_u2081_5241_: *mut LeanObject,
    mut v_t_u2082_5242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5243_: u8 = 0;
    v___x_5243_ = l_Lean_PersistentArray_isEmpty___redArg(v_t_u2081_5241_);
    if v___x_5243_ == 0 {
        let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
        v___x_5244_ = lean_unsigned_to_nat(0);
        v___x_5245_ =
            l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(
                v_t_u2082_5242_,
                v_t_u2081_5241_,
                v___x_5244_,
            );
        return v___x_5245_;
    } else {
        lean_dec_ref(v_t_u2081_5241_);
        lean_inc_ref(v_t_u2082_5242_);
        return v_t_u2082_5242_;
    }
}
pub unsafe fn l_Lean_PersistentArray_append___redArg___boxed(
    mut v_t_u2081_5246_: *mut LeanObject,
    mut v_t_u2082_5247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5248_: *mut LeanObject = core::ptr::null_mut();
    v_res_5248_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_5246_, v_t_u2082_5247_);
    lean_dec_ref(v_t_u2082_5247_);
    return v_res_5248_;
}
pub unsafe fn l_Lean_PersistentArray_append(
    mut v_00_u03b1_5249_: *mut LeanObject,
    mut v_t_u2081_5250_: *mut LeanObject,
    mut v_t_u2082_5251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    v___x_5252_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_5250_, v_t_u2082_5251_);
    return v___x_5252_;
}
pub unsafe fn l_Lean_PersistentArray_append___boxed(
    mut v_00_u03b1_5253_: *mut LeanObject,
    mut v_t_u2081_5254_: *mut LeanObject,
    mut v_t_u2082_5255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5256_: *mut LeanObject = core::ptr::null_mut();
    v_res_5256_ = l_Lean_PersistentArray_append(v_00_u03b1_5253_, v_t_u2081_5254_, v_t_u2082_5255_);
    lean_dec_ref(v_t_u2082_5255_);
    return v_res_5256_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(
    mut v_00_u03b1_5257_: *mut LeanObject,
    mut v_t_5258_: *mut LeanObject,
    mut v_init_5259_: *mut LeanObject,
    mut v_start_5260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    v___x_5261_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(
            v_t_5258_,
            v_init_5259_,
            v_start_5260_,
        );
    return v___x_5261_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___boxed(
    mut v_00_u03b1_5262_: *mut LeanObject,
    mut v_t_5263_: *mut LeanObject,
    mut v_init_5264_: *mut LeanObject,
    mut v_start_5265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5266_: *mut LeanObject = core::ptr::null_mut();
    v_res_5266_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(
        v_00_u03b1_5262_,
        v_t_5263_,
        v_init_5264_,
        v_start_5265_,
    );
    lean_dec(v_start_5265_);
    lean_dec_ref(v_t_5263_);
    return v_res_5266_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(
    mut v_00_u03b1_5267_: *mut LeanObject,
    mut v_x_5268_: *mut LeanObject,
    mut v_x_5269_: usize,
    mut v_x_5270_: usize,
    mut v_x_5271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    v___x_5272_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_5268_, v_x_5269_, v_x_5270_, v_x_5271_);
    return v___x_5272_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___boxed(
    mut v_00_u03b1_5273_: *mut LeanObject,
    mut v_x_5274_: *mut LeanObject,
    mut v_x_5275_: *mut LeanObject,
    mut v_x_5276_: *mut LeanObject,
    mut v_x_5277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1679__boxed_5278_: usize = 0;
    let mut v_x_1680__boxed_5279_: usize = 0;
    let mut v_res_5280_: *mut LeanObject = core::ptr::null_mut();
    v_x_1679__boxed_5278_ = lean_unbox_usize(v_x_5275_);
    lean_dec(v_x_5275_);
    v_x_1680__boxed_5279_ = lean_unbox_usize(v_x_5276_);
    lean_dec(v_x_5276_);
    v_res_5280_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(v_00_u03b1_5273_, v_x_5274_, v_x_1679__boxed_5278_, v_x_1680__boxed_5279_, v_x_5277_);
    lean_dec_ref(v_x_5274_);
    return v_res_5280_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(
    mut v_00_u03b1_5281_: *mut LeanObject,
    mut v_as_5282_: *mut LeanObject,
    mut v_i_5283_: usize,
    mut v_stop_5284_: usize,
    mut v_b_5285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    v___x_5286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_5282_, v_i_5283_, v_stop_5284_, v_b_5285_);
    return v___x_5286_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___boxed(
    mut v_00_u03b1_5287_: *mut LeanObject,
    mut v_as_5288_: *mut LeanObject,
    mut v_i_5289_: *mut LeanObject,
    mut v_stop_5290_: *mut LeanObject,
    mut v_b_5291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5292_: usize = 0;
    let mut v_stop_boxed_5293_: usize = 0;
    let mut v_res_5294_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5292_ = lean_unbox_usize(v_i_5289_);
    lean_dec(v_i_5289_);
    v_stop_boxed_5293_ = lean_unbox_usize(v_stop_5290_);
    lean_dec(v_stop_5290_);
    v_res_5294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(v_00_u03b1_5287_, v_as_5288_, v_i_boxed_5292_, v_stop_boxed_5293_, v_b_5291_);
    lean_dec_ref(v_as_5288_);
    return v_res_5294_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(
    mut v_00_u03b1_5295_: *mut LeanObject,
    mut v_x_5296_: *mut LeanObject,
    mut v_x_5297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    v___x_5298_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_5296_, v_x_5297_);
    return v___x_5298_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___boxed(
    mut v_00_u03b1_5299_: *mut LeanObject,
    mut v_x_5300_: *mut LeanObject,
    mut v_x_5301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5302_: *mut LeanObject = core::ptr::null_mut();
    v_res_5302_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(v_00_u03b1_5299_, v_x_5300_, v_x_5301_);
    lean_dec_ref(v_x_5300_);
    return v_res_5302_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(
    mut v_00_u03b1_5303_: *mut LeanObject,
    mut v_as_5304_: *mut LeanObject,
    mut v_i_5305_: usize,
    mut v_stop_5306_: usize,
    mut v_b_5307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
    v___x_5308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_5304_, v_i_5305_, v_stop_5306_, v_b_5307_);
    return v___x_5308_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_5309_: *mut LeanObject,
    mut v_as_5310_: *mut LeanObject,
    mut v_i_5311_: *mut LeanObject,
    mut v_stop_5312_: *mut LeanObject,
    mut v_b_5313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5314_: usize = 0;
    let mut v_stop_boxed_5315_: usize = 0;
    let mut v_res_5316_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5314_ = lean_unbox_usize(v_i_5311_);
    lean_dec(v_i_5311_);
    v_stop_boxed_5315_ = lean_unbox_usize(v_stop_5312_);
    lean_dec(v_stop_5312_);
    v_res_5316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(v_00_u03b1_5309_, v_as_5310_, v_i_boxed_5314_, v_stop_boxed_5315_, v_b_5313_);
    lean_dec_ref(v_as_5310_);
    return v_res_5316_;
}
pub unsafe fn l_Lean_PersistentArray_instAppend(
    mut v_00_u03b1_5318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    v___x_5319_ = l_Lean_PersistentArray_instAppend___closed__0;
    return v___x_5319_;
}
pub unsafe fn l_Lean_PersistentArray_findSome_x3f___redArg___lam__0(
    mut v_f_5320_: *mut LeanObject,
    mut v_x_5321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    v___x_5322_ = lean_apply_1(v_f_5320_, v_x_5321_);
    return v___x_5322_;
}
pub unsafe fn l_Lean_PersistentArray_findSome_x3f___redArg(
    mut v_t_5323_: *mut LeanObject,
    mut v_f_5324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    v___f_5325_ = lean_alloc_closure(
        l_Lean_PersistentArray_findSome_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5325_, 0, v_f_5324_);
    v___x_5326_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5327_ =
        l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_5326_, v_t_5323_, v___f_5325_);
    return v___x_5327_;
}
pub unsafe fn l_Lean_PersistentArray_findSome_x3f(
    mut v_00_u03b1_5328_: *mut LeanObject,
    mut v_00_u03b2_5329_: *mut LeanObject,
    mut v_t_5330_: *mut LeanObject,
    mut v_f_5331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    v___f_5332_ = lean_alloc_closure(
        l_Lean_PersistentArray_findSome_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5332_, 0, v_f_5331_);
    v___x_5333_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5334_ =
        l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_5333_, v_t_5330_, v___f_5332_);
    return v___x_5334_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRev_x3f___redArg(
    mut v_t_5335_: *mut LeanObject,
    mut v_f_5336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    v___f_5337_ = lean_alloc_closure(
        l_Lean_PersistentArray_findSome_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5337_, 0, v_f_5336_);
    v___x_5338_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5339_ =
        l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_5338_, v_t_5335_, v___f_5337_);
    return v___x_5339_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRev_x3f(
    mut v_00_u03b1_5340_: *mut LeanObject,
    mut v_00_u03b2_5341_: *mut LeanObject,
    mut v_t_5342_: *mut LeanObject,
    mut v_f_5343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    v___f_5344_ = lean_alloc_closure(
        l_Lean_PersistentArray_findSome_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5344_, 0, v_f_5343_);
    v___x_5345_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5346_ =
        l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_5345_, v_t_5342_, v___f_5344_);
    return v___x_5346_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(
    mut v_as_5347_: *mut LeanObject,
    mut v_i_5348_: usize,
    mut v_stop_5349_: usize,
    mut v_b_5350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5351_: u8 = 0;
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: usize = 0;
    let mut v___x_5355_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5351_ = lean_usize_dec_eq(v_i_5348_, v_stop_5349_);
                if v___x_5351_ == 0 {
                    v___x_5352_ = lean_array_uget_borrowed(v_as_5347_, v_i_5348_);
                    lean_inc(v___x_5352_);
                    v___x_5353_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_5353_, 0, v___x_5352_);
                    lean_ctor_set(v___x_5353_, 1, v_b_5350_);
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
    mut v_as_5357_: *mut LeanObject,
    mut v_i_5358_: *mut LeanObject,
    mut v_stop_5359_: *mut LeanObject,
    mut v_b_5360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5361_: usize = 0;
    let mut v_stop_boxed_5362_: usize = 0;
    let mut v_res_5363_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5361_ = lean_unbox_usize(v_i_5358_);
    lean_dec(v_i_5358_);
    v_stop_boxed_5362_ = lean_unbox_usize(v_stop_5359_);
    lean_dec(v_stop_5359_);
    v_res_5363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_5357_, v_i_boxed_5361_, v_stop_boxed_5362_, v_b_5360_);
    lean_dec_ref(v_as_5357_);
    return v_res_5363_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(
    mut v_x_5364_: *mut LeanObject,
    mut v_x_5365_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5364_) == 0 {
        let mut v_cs_5366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5369_: u8 = 0;
        v_cs_5366_ = lean_ctor_get(v_x_5364_, 0);
        v___x_5367_ = lean_unsigned_to_nat(0);
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
                    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5371_ = 0usize;
                    v___x_5372_ = lean_usize_of_nat(v___x_5368_);
                    v___x_5373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_5366_, v___x_5371_, v___x_5372_, v_x_5365_);
                    return v___x_5373_;
                }
            } else {
                let mut v___x_5374_: usize = 0;
                let mut v___x_5375_: usize = 0;
                let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
                v___x_5374_ = 0usize;
                v___x_5375_ = lean_usize_of_nat(v___x_5368_);
                v___x_5376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_5366_, v___x_5374_, v___x_5375_, v_x_5365_);
                return v___x_5376_;
            }
        }
    } else {
        let mut v_vs_5377_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5380_: u8 = 0;
        v_vs_5377_ = lean_ctor_get(v_x_5364_, 0);
        v___x_5378_ = lean_unsigned_to_nat(0);
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
                    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5382_ = 0usize;
                    v___x_5383_ = lean_usize_of_nat(v___x_5379_);
                    v___x_5384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_5377_, v___x_5382_, v___x_5383_, v_x_5365_);
                    return v___x_5384_;
                }
            } else {
                let mut v___x_5385_: usize = 0;
                let mut v___x_5386_: usize = 0;
                let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
                v___x_5385_ = 0usize;
                v___x_5386_ = lean_usize_of_nat(v___x_5379_);
                v___x_5387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_5377_, v___x_5385_, v___x_5386_, v_x_5365_);
                return v___x_5387_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(
    mut v_as_5388_: *mut LeanObject,
    mut v_i_5389_: usize,
    mut v_stop_5390_: usize,
    mut v_b_5391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5392_: u8 = 0;
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_as_5398_: *mut LeanObject,
    mut v_i_5399_: *mut LeanObject,
    mut v_stop_5400_: *mut LeanObject,
    mut v_b_5401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5402_: usize = 0;
    let mut v_stop_boxed_5403_: usize = 0;
    let mut v_res_5404_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5402_ = lean_unbox_usize(v_i_5399_);
    lean_dec(v_i_5399_);
    v_stop_boxed_5403_ = lean_unbox_usize(v_stop_5400_);
    lean_dec(v_stop_5400_);
    v_res_5404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_5398_, v_i_boxed_5402_, v_stop_boxed_5403_, v_b_5401_);
    lean_dec_ref(v_as_5398_);
    return v_res_5404_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg___boxed(
    mut v_x_5405_: *mut LeanObject,
    mut v_x_5406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5407_: *mut LeanObject = core::ptr::null_mut();
    v_res_5407_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_5405_, v_x_5406_);
    lean_dec_ref(v_x_5405_);
    return v_res_5407_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(
    mut v_x_5408_: *mut LeanObject,
    mut v_x_5409_: usize,
    mut v_x_5410_: usize,
    mut v_x_5411_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5408_) == 0 {
        let mut v_cs_5412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5414_: usize = 0;
        let mut v_j_5415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5417_: usize = 0;
        let mut v___x_5418_: usize = 0;
        let mut v___x_5419_: usize = 0;
        let mut v___x_5420_: usize = 0;
        let mut v___x_5421_: usize = 0;
        let mut v___x_5422_: usize = 0;
        let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5427_: u8 = 0;
        v_cs_5412_ = lean_ctor_get(v_x_5408_, 0);
        v___x_5413_ = lean_obj_once(
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
        v___x_5424_ = lean_unsigned_to_nat(1);
        v___x_5425_ = lean_nat_add(v_j_5415_, v___x_5424_);
        lean_dec(v_j_5415_);
        v___x_5426_ = lean_array_get_size(v_cs_5412_);
        v___x_5427_ = lean_nat_dec_lt(v___x_5425_, v___x_5426_);
        if v___x_5427_ == 0 {
            lean_dec(v___x_5425_);
            return v___x_5423_;
        } else {
            let mut v___x_5428_: u8 = 0;
            v___x_5428_ = lean_nat_dec_le(v___x_5426_, v___x_5426_);
            if v___x_5428_ == 0 {
                if v___x_5427_ == 0 {
                    lean_dec(v___x_5425_);
                    return v___x_5423_;
                } else {
                    let mut v___x_5429_: usize = 0;
                    let mut v___x_5430_: usize = 0;
                    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5429_ = lean_usize_of_nat(v___x_5425_);
                    lean_dec(v___x_5425_);
                    v___x_5430_ = lean_usize_of_nat(v___x_5426_);
                    v___x_5431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_5412_, v___x_5429_, v___x_5430_, v___x_5423_);
                    return v___x_5431_;
                }
            } else {
                let mut v___x_5432_: usize = 0;
                let mut v___x_5433_: usize = 0;
                let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
                v___x_5432_ = lean_usize_of_nat(v___x_5425_);
                lean_dec(v___x_5425_);
                v___x_5433_ = lean_usize_of_nat(v___x_5426_);
                v___x_5434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_5412_, v___x_5432_, v___x_5433_, v___x_5423_);
                return v___x_5434_;
            }
        }
    } else {
        let mut v_vs_5435_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5438_: u8 = 0;
        v_vs_5435_ = lean_ctor_get(v_x_5408_, 0);
        v___x_5436_ = lean_usize_to_nat(v_x_5409_);
        v___x_5437_ = lean_array_get_size(v_vs_5435_);
        v___x_5438_ = lean_nat_dec_lt(v___x_5436_, v___x_5437_);
        if v___x_5438_ == 0 {
            lean_dec(v___x_5436_);
            return v_x_5411_;
        } else {
            let mut v___x_5439_: u8 = 0;
            v___x_5439_ = lean_nat_dec_le(v___x_5437_, v___x_5437_);
            if v___x_5439_ == 0 {
                if v___x_5438_ == 0 {
                    lean_dec(v___x_5436_);
                    return v_x_5411_;
                } else {
                    let mut v___x_5440_: usize = 0;
                    let mut v___x_5441_: usize = 0;
                    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5440_ = lean_usize_of_nat(v___x_5436_);
                    lean_dec(v___x_5436_);
                    v___x_5441_ = lean_usize_of_nat(v___x_5437_);
                    v___x_5442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_5435_, v___x_5440_, v___x_5441_, v_x_5411_);
                    return v___x_5442_;
                }
            } else {
                let mut v___x_5443_: usize = 0;
                let mut v___x_5444_: usize = 0;
                let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
                v___x_5443_ = lean_usize_of_nat(v___x_5436_);
                lean_dec(v___x_5436_);
                v___x_5444_ = lean_usize_of_nat(v___x_5437_);
                v___x_5445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_5435_, v___x_5443_, v___x_5444_, v_x_5411_);
                return v___x_5445_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg___boxed(
    mut v_x_5446_: *mut LeanObject,
    mut v_x_5447_: *mut LeanObject,
    mut v_x_5448_: *mut LeanObject,
    mut v_x_5449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1497__boxed_5450_: usize = 0;
    let mut v_x_1498__boxed_5451_: usize = 0;
    let mut v_res_5452_: *mut LeanObject = core::ptr::null_mut();
    v_x_1497__boxed_5450_ = lean_unbox_usize(v_x_5447_);
    lean_dec(v_x_5447_);
    v_x_1498__boxed_5451_ = lean_unbox_usize(v_x_5448_);
    lean_dec(v_x_5448_);
    v_res_5452_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_5446_, v_x_1497__boxed_5450_, v_x_1498__boxed_5451_, v_x_5449_);
    lean_dec_ref(v_x_5446_);
    return v_res_5452_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(
    mut v_t_5453_: *mut LeanObject,
    mut v_init_5454_: *mut LeanObject,
    mut v_start_5455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: u8 = 0;
    v___x_5456_ = lean_unsigned_to_nat(0);
    v___x_5457_ = lean_nat_dec_eq(v_start_5455_, v___x_5456_);
    if v___x_5457_ == 0 {
        let mut v_root_5458_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_5459_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_5460_: usize = 0;
        let mut v_tailOff_5461_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5462_: u8 = 0;
        v_root_5458_ = lean_ctor_get(v_t_5453_, 0);
        v_tail_5459_ = lean_ctor_get(v_t_5453_, 1);
        v_shift_5460_ = lean_ctor_get_usize(v_t_5453_, 4);
        v_tailOff_5461_ = lean_ctor_get(v_t_5453_, 3);
        v___x_5462_ = lean_nat_dec_le(v_tailOff_5461_, v_start_5455_);
        if v___x_5462_ == 0 {
            let mut v___x_5463_: usize = 0;
            let mut v___x_5464_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
                        v___x_5468_ = 0usize;
                        v___x_5469_ = lean_usize_of_nat(v___x_5465_);
                        v___x_5470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_5459_, v___x_5468_, v___x_5469_, v___x_5464_);
                        return v___x_5470_;
                    }
                } else {
                    let mut v___x_5471_: usize = 0;
                    let mut v___x_5472_: usize = 0;
                    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5471_ = 0usize;
                    v___x_5472_ = lean_usize_of_nat(v___x_5465_);
                    v___x_5473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_5459_, v___x_5471_, v___x_5472_, v___x_5464_);
                    return v___x_5473_;
                }
            }
        } else {
            let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5476_: u8 = 0;
            v___x_5474_ = lean_nat_sub(v_start_5455_, v_tailOff_5461_);
            v___x_5475_ = lean_array_get_size(v_tail_5459_);
            v___x_5476_ = lean_nat_dec_lt(v___x_5474_, v___x_5475_);
            if v___x_5476_ == 0 {
                lean_dec(v___x_5474_);
                return v_init_5454_;
            } else {
                let mut v___x_5477_: u8 = 0;
                v___x_5477_ = lean_nat_dec_le(v___x_5475_, v___x_5475_);
                if v___x_5477_ == 0 {
                    if v___x_5476_ == 0 {
                        lean_dec(v___x_5474_);
                        return v_init_5454_;
                    } else {
                        let mut v___x_5478_: usize = 0;
                        let mut v___x_5479_: usize = 0;
                        let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
                        v___x_5478_ = lean_usize_of_nat(v___x_5474_);
                        lean_dec(v___x_5474_);
                        v___x_5479_ = lean_usize_of_nat(v___x_5475_);
                        v___x_5480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_5459_, v___x_5478_, v___x_5479_, v_init_5454_);
                        return v___x_5480_;
                    }
                } else {
                    let mut v___x_5481_: usize = 0;
                    let mut v___x_5482_: usize = 0;
                    let mut v___x_5483_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5481_ = lean_usize_of_nat(v___x_5474_);
                    lean_dec(v___x_5474_);
                    v___x_5482_ = lean_usize_of_nat(v___x_5475_);
                    v___x_5483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_5459_, v___x_5481_, v___x_5482_, v_init_5454_);
                    return v___x_5483_;
                }
            }
        }
    } else {
        let mut v_root_5484_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_5485_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5488_: u8 = 0;
        v_root_5484_ = lean_ctor_get(v_t_5453_, 0);
        v_tail_5485_ = lean_ctor_get(v_t_5453_, 1);
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
                    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5490_ = 0usize;
                    v___x_5491_ = lean_usize_of_nat(v___x_5487_);
                    v___x_5492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_5485_, v___x_5490_, v___x_5491_, v___x_5486_);
                    return v___x_5492_;
                }
            } else {
                let mut v___x_5493_: usize = 0;
                let mut v___x_5494_: usize = 0;
                let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
                v___x_5493_ = 0usize;
                v___x_5494_ = lean_usize_of_nat(v___x_5487_);
                v___x_5495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_5485_, v___x_5493_, v___x_5494_, v___x_5486_);
                return v___x_5495_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg___boxed(
    mut v_t_5496_: *mut LeanObject,
    mut v_init_5497_: *mut LeanObject,
    mut v_start_5498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5499_: *mut LeanObject = core::ptr::null_mut();
    v_res_5499_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(
            v_t_5496_,
            v_init_5497_,
            v_start_5498_,
        );
    lean_dec(v_start_5498_);
    lean_dec_ref(v_t_5496_);
    return v_res_5499_;
}
pub unsafe fn l_Lean_PersistentArray_toList___redArg(
    mut v_t_5500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    v___x_5501_ = lean_box(0);
    v___x_5502_ = lean_unsigned_to_nat(0);
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
    mut v_t_5505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5506_: *mut LeanObject = core::ptr::null_mut();
    v_res_5506_ = l_Lean_PersistentArray_toList___redArg(v_t_5505_);
    lean_dec_ref(v_t_5505_);
    return v_res_5506_;
}
pub unsafe fn l_Lean_PersistentArray_toList(
    mut v_00_u03b1_5507_: *mut LeanObject,
    mut v_t_5508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    v___x_5509_ = l_Lean_PersistentArray_toList___redArg(v_t_5508_);
    return v___x_5509_;
}
pub unsafe fn l_Lean_PersistentArray_toList___boxed(
    mut v_00_u03b1_5510_: *mut LeanObject,
    mut v_t_5511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5512_: *mut LeanObject = core::ptr::null_mut();
    v_res_5512_ = l_Lean_PersistentArray_toList(v_00_u03b1_5510_, v_t_5511_);
    lean_dec_ref(v_t_5511_);
    return v_res_5512_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(
    mut v_00_u03b1_5513_: *mut LeanObject,
    mut v_t_5514_: *mut LeanObject,
    mut v_init_5515_: *mut LeanObject,
    mut v_start_5516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    v___x_5517_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(
            v_t_5514_,
            v_init_5515_,
            v_start_5516_,
        );
    return v___x_5517_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___boxed(
    mut v_00_u03b1_5518_: *mut LeanObject,
    mut v_t_5519_: *mut LeanObject,
    mut v_init_5520_: *mut LeanObject,
    mut v_start_5521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5522_: *mut LeanObject = core::ptr::null_mut();
    v_res_5522_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(
        v_00_u03b1_5518_,
        v_t_5519_,
        v_init_5520_,
        v_start_5521_,
    );
    lean_dec(v_start_5521_);
    lean_dec_ref(v_t_5519_);
    return v_res_5522_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(
    mut v_00_u03b1_5523_: *mut LeanObject,
    mut v_x_5524_: *mut LeanObject,
    mut v_x_5525_: usize,
    mut v_x_5526_: usize,
    mut v_x_5527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    v___x_5528_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_5524_, v_x_5525_, v_x_5526_, v_x_5527_);
    return v___x_5528_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___boxed(
    mut v_00_u03b1_5529_: *mut LeanObject,
    mut v_x_5530_: *mut LeanObject,
    mut v_x_5531_: *mut LeanObject,
    mut v_x_5532_: *mut LeanObject,
    mut v_x_5533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1655__boxed_5534_: usize = 0;
    let mut v_x_1656__boxed_5535_: usize = 0;
    let mut v_res_5536_: *mut LeanObject = core::ptr::null_mut();
    v_x_1655__boxed_5534_ = lean_unbox_usize(v_x_5531_);
    lean_dec(v_x_5531_);
    v_x_1656__boxed_5535_ = lean_unbox_usize(v_x_5532_);
    lean_dec(v_x_5532_);
    v_res_5536_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(v_00_u03b1_5529_, v_x_5530_, v_x_1655__boxed_5534_, v_x_1656__boxed_5535_, v_x_5533_);
    lean_dec_ref(v_x_5530_);
    return v_res_5536_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(
    mut v_00_u03b1_5537_: *mut LeanObject,
    mut v_as_5538_: *mut LeanObject,
    mut v_i_5539_: usize,
    mut v_stop_5540_: usize,
    mut v_b_5541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    v___x_5542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_5538_, v_i_5539_, v_stop_5540_, v_b_5541_);
    return v___x_5542_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___boxed(
    mut v_00_u03b1_5543_: *mut LeanObject,
    mut v_as_5544_: *mut LeanObject,
    mut v_i_5545_: *mut LeanObject,
    mut v_stop_5546_: *mut LeanObject,
    mut v_b_5547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5548_: usize = 0;
    let mut v_stop_boxed_5549_: usize = 0;
    let mut v_res_5550_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5548_ = lean_unbox_usize(v_i_5545_);
    lean_dec(v_i_5545_);
    v_stop_boxed_5549_ = lean_unbox_usize(v_stop_5546_);
    lean_dec(v_stop_5546_);
    v_res_5550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(v_00_u03b1_5543_, v_as_5544_, v_i_boxed_5548_, v_stop_boxed_5549_, v_b_5547_);
    lean_dec_ref(v_as_5544_);
    return v_res_5550_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(
    mut v_00_u03b1_5551_: *mut LeanObject,
    mut v_x_5552_: *mut LeanObject,
    mut v_x_5553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
    v___x_5554_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_5552_, v_x_5553_);
    return v___x_5554_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___boxed(
    mut v_00_u03b1_5555_: *mut LeanObject,
    mut v_x_5556_: *mut LeanObject,
    mut v_x_5557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5558_: *mut LeanObject = core::ptr::null_mut();
    v_res_5558_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(v_00_u03b1_5555_, v_x_5556_, v_x_5557_);
    lean_dec_ref(v_x_5556_);
    return v_res_5558_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(
    mut v_00_u03b1_5559_: *mut LeanObject,
    mut v_as_5560_: *mut LeanObject,
    mut v_i_5561_: usize,
    mut v_stop_5562_: usize,
    mut v_b_5563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    v___x_5564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_5560_, v_i_5561_, v_stop_5562_, v_b_5563_);
    return v___x_5564_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_5565_: *mut LeanObject,
    mut v_as_5566_: *mut LeanObject,
    mut v_i_5567_: *mut LeanObject,
    mut v_stop_5568_: *mut LeanObject,
    mut v_b_5569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5570_: usize = 0;
    let mut v_stop_boxed_5571_: usize = 0;
    let mut v_res_5572_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5570_ = lean_unbox_usize(v_i_5567_);
    lean_dec(v_i_5567_);
    v_stop_boxed_5571_ = lean_unbox_usize(v_stop_5568_);
    lean_dec(v_stop_5568_);
    v_res_5572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(v_00_u03b1_5565_, v_as_5566_, v_i_boxed_5570_, v_stop_boxed_5571_, v_b_5569_);
    lean_dec_ref(v_as_5566_);
    return v_res_5572_;
}
pub unsafe fn l_Lean_PersistentArray_anyMAux___redArg(
    mut v_inst_5573_: *mut LeanObject,
    mut v_p_5574_: *mut LeanObject,
    mut v_x_5575_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5575_) == 0 {
        let mut v_cs_5576_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5579_: u8 = 0;
        v_cs_5576_ = lean_ctor_get(v_x_5575_, 0);
        lean_inc_ref(v_cs_5576_);
        lean_dec_ref_known(v_x_5575_, 1);
        v___x_5577_ = lean_unsigned_to_nat(0);
        v___x_5578_ = lean_array_get_size(v_cs_5576_);
        v___x_5579_ = lean_nat_dec_lt(v___x_5577_, v___x_5578_);
        if v___x_5579_ == 0 {
            let mut v_toApplicative_5580_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5581_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_cs_5576_);
            lean_dec(v_p_5574_);
            v_toApplicative_5580_ = lean_ctor_get(v_inst_5573_, 0);
            lean_inc_ref(v_toApplicative_5580_);
            lean_dec_ref(v_inst_5573_);
            v_toPure_5581_ = lean_ctor_get(v_toApplicative_5580_, 1);
            lean_inc(v_toPure_5581_);
            lean_dec_ref(v_toApplicative_5580_);
            v___x_5582_ = lean_box((v___x_5579_) as usize);
            v___x_5583_ = lean_apply_2(v_toPure_5581_, lean_box(0), v___x_5582_);
            return v___x_5583_;
        } else {
            if v___x_5579_ == 0 {
                let mut v_toApplicative_5584_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_5585_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_cs_5576_);
                lean_dec(v_p_5574_);
                v_toApplicative_5584_ = lean_ctor_get(v_inst_5573_, 0);
                lean_inc_ref(v_toApplicative_5584_);
                lean_dec_ref(v_inst_5573_);
                v_toPure_5585_ = lean_ctor_get(v_toApplicative_5584_, 1);
                lean_inc(v_toPure_5585_);
                lean_dec_ref(v_toApplicative_5584_);
                v___x_5586_ = lean_box((v___x_5579_) as usize);
                v___x_5587_ = lean_apply_2(v_toPure_5585_, lean_box(0), v___x_5586_);
                return v___x_5587_;
            } else {
                let mut v___f_5588_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5589_: usize = 0;
                let mut v___x_5590_: usize = 0;
                let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
                lean_inc_ref(v_inst_5573_);
                v___f_5588_ = lean_alloc_closure(
                    l_Lean_PersistentArray_anyMAux___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_5588_, 0, v_inst_5573_);
                lean_closure_set(v___f_5588_, 1, v_p_5574_);
                v___x_5589_ = 0usize;
                v___x_5590_ = lean_usize_of_nat(v___x_5578_);
                v___x_5591_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                    lean_box(0),
                    lean_box(0),
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
        let mut v_vs_5592_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5595_: u8 = 0;
        v_vs_5592_ = lean_ctor_get(v_x_5575_, 0);
        lean_inc_ref(v_vs_5592_);
        lean_dec_ref_known(v_x_5575_, 1);
        v___x_5593_ = lean_unsigned_to_nat(0);
        v___x_5594_ = lean_array_get_size(v_vs_5592_);
        v___x_5595_ = lean_nat_dec_lt(v___x_5593_, v___x_5594_);
        if v___x_5595_ == 0 {
            let mut v_toApplicative_5596_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_5597_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_vs_5592_);
            lean_dec(v_p_5574_);
            v_toApplicative_5596_ = lean_ctor_get(v_inst_5573_, 0);
            lean_inc_ref(v_toApplicative_5596_);
            lean_dec_ref(v_inst_5573_);
            v_toPure_5597_ = lean_ctor_get(v_toApplicative_5596_, 1);
            lean_inc(v_toPure_5597_);
            lean_dec_ref(v_toApplicative_5596_);
            v___x_5598_ = lean_box((v___x_5595_) as usize);
            v___x_5599_ = lean_apply_2(v_toPure_5597_, lean_box(0), v___x_5598_);
            return v___x_5599_;
        } else {
            if v___x_5595_ == 0 {
                let mut v_toApplicative_5600_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_5601_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_vs_5592_);
                lean_dec(v_p_5574_);
                v_toApplicative_5600_ = lean_ctor_get(v_inst_5573_, 0);
                lean_inc_ref(v_toApplicative_5600_);
                lean_dec_ref(v_inst_5573_);
                v_toPure_5601_ = lean_ctor_get(v_toApplicative_5600_, 1);
                lean_inc(v_toPure_5601_);
                lean_dec_ref(v_toApplicative_5600_);
                v___x_5602_ = lean_box((v___x_5595_) as usize);
                v___x_5603_ = lean_apply_2(v_toPure_5601_, lean_box(0), v___x_5602_);
                return v___x_5603_;
            } else {
                let mut v___x_5604_: usize = 0;
                let mut v___x_5605_: usize = 0;
                let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
                v___x_5604_ = 0usize;
                v___x_5605_ = lean_usize_of_nat(v___x_5594_);
                v___x_5606_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_5607_: *mut LeanObject,
    mut v_p_5608_: *mut LeanObject,
    mut v_c_5609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    v___x_5610_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_5607_, v_p_5608_, v_c_5609_);
    return v___x_5610_;
}
pub unsafe fn l_Lean_PersistentArray_anyMAux(
    mut v_00_u03b1_5611_: *mut LeanObject,
    mut v_m_5612_: *mut LeanObject,
    mut v_inst_5613_: *mut LeanObject,
    mut v_p_5614_: *mut LeanObject,
    mut v_x_5615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    v___x_5616_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_5613_, v_p_5614_, v_x_5615_);
    return v___x_5616_;
}
pub unsafe fn l_Lean_PersistentArray_anyM___redArg___lam__0(
    mut v_tail_5617_: *mut LeanObject,
    mut v_toPure_5618_: *mut LeanObject,
    mut v_inst_5619_: *mut LeanObject,
    mut v_p_5620_: *mut LeanObject,
    mut v_b_5621_: u8,
) -> *mut LeanObject {
    if v_b_5621_ == 0 {
        let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5624_: u8 = 0;
        v___x_5622_ = lean_unsigned_to_nat(0);
        v___x_5623_ = lean_array_get_size(v_tail_5617_);
        v___x_5624_ = lean_nat_dec_lt(v___x_5622_, v___x_5623_);
        if v___x_5624_ == 0 {
            let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_p_5620_);
            lean_dec_ref(v_inst_5619_);
            lean_dec_ref(v_tail_5617_);
            v___x_5625_ = lean_box((v_b_5621_) as usize);
            v___x_5626_ = lean_apply_2(v_toPure_5618_, lean_box(0), v___x_5625_);
            return v___x_5626_;
        } else {
            if v___x_5624_ == 0 {
                let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_p_5620_);
                lean_dec_ref(v_inst_5619_);
                lean_dec_ref(v_tail_5617_);
                v___x_5627_ = lean_box((v_b_5621_) as usize);
                v___x_5628_ = lean_apply_2(v_toPure_5618_, lean_box(0), v___x_5627_);
                return v___x_5628_;
            } else {
                let mut v___x_5629_: usize = 0;
                let mut v___x_5630_: usize = 0;
                let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_toPure_5618_);
                v___x_5629_ = 0usize;
                v___x_5630_ = lean_usize_of_nat(v___x_5623_);
                v___x_5631_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                    lean_box(0),
                    lean_box(0),
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
        let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_p_5620_);
        lean_dec_ref(v_inst_5619_);
        lean_dec_ref(v_tail_5617_);
        v___x_5632_ = lean_box((v_b_5621_) as usize);
        v___x_5633_ = lean_apply_2(v_toPure_5618_, lean_box(0), v___x_5632_);
        return v___x_5633_;
    }
}
pub unsafe fn l_Lean_PersistentArray_anyM___redArg___lam__0___boxed(
    mut v_tail_5634_: *mut LeanObject,
    mut v_toPure_5635_: *mut LeanObject,
    mut v_inst_5636_: *mut LeanObject,
    mut v_p_5637_: *mut LeanObject,
    mut v_b_5638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_5639_: u8 = 0;
    let mut v_res_5640_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_5639_ = (lean_unbox(v_b_5638_) as u8);
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
    mut v_inst_5641_: *mut LeanObject,
    mut v_t_5642_: *mut LeanObject,
    mut v_p_5643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5644_ = lean_ctor_get(v_inst_5641_, 0);
    v_toBind_5645_ = lean_ctor_get(v_inst_5641_, 1);
    lean_inc(v_toBind_5645_);
    v_root_5646_ = lean_ctor_get(v_t_5642_, 0);
    lean_inc_ref(v_root_5646_);
    v_tail_5647_ = lean_ctor_get(v_t_5642_, 1);
    lean_inc_ref(v_tail_5647_);
    lean_dec_ref(v_t_5642_);
    v_toPure_5648_ = lean_ctor_get(v_toApplicative_5644_, 1);
    lean_inc(v_toPure_5648_);
    lean_inc(v_p_5643_);
    lean_inc_ref(v_inst_5641_);
    v___x_5649_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_5641_, v_p_5643_, v_root_5646_);
    v___f_5650_ = lean_alloc_closure(
        l_Lean_PersistentArray_anyM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5650_, 0, v_tail_5647_);
    lean_closure_set(v___f_5650_, 1, v_toPure_5648_);
    lean_closure_set(v___f_5650_, 2, v_inst_5641_);
    lean_closure_set(v___f_5650_, 3, v_p_5643_);
    v___x_5651_ = lean_apply_4(
        v_toBind_5645_,
        lean_box(0),
        lean_box(0),
        v___x_5649_,
        v___f_5650_,
    );
    return v___x_5651_;
}
pub unsafe fn l_Lean_PersistentArray_anyM(
    mut v_00_u03b1_5652_: *mut LeanObject,
    mut v_m_5653_: *mut LeanObject,
    mut v_inst_5654_: *mut LeanObject,
    mut v_t_5655_: *mut LeanObject,
    mut v_p_5656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    v___x_5657_ = l_Lean_PersistentArray_anyM___redArg(v_inst_5654_, v_t_5655_, v_p_5656_);
    return v___x_5657_;
}
pub unsafe fn l_Lean_PersistentArray_allM___redArg___lam__0(
    mut v_toPure_5658_: *mut LeanObject,
    mut v_b_5659_: u8,
) -> *mut LeanObject {
    if v_b_5659_ == 0 {
        let mut v___x_5660_: u8 = 0;
        let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
        v___x_5660_ = 1;
        v___x_5661_ = lean_box((v___x_5660_) as usize);
        v___x_5662_ = lean_apply_2(v_toPure_5658_, lean_box(0), v___x_5661_);
        return v___x_5662_;
    } else {
        let mut v___x_5663_: u8 = 0;
        let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
        v___x_5663_ = 0;
        v___x_5664_ = lean_box((v___x_5663_) as usize);
        v___x_5665_ = lean_apply_2(v_toPure_5658_, lean_box(0), v___x_5664_);
        return v___x_5665_;
    }
}
pub unsafe fn l_Lean_PersistentArray_allM___redArg___lam__0___boxed(
    mut v_toPure_5666_: *mut LeanObject,
    mut v_b_5667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_5668_: u8 = 0;
    let mut v_res_5669_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_5668_ = (lean_unbox(v_b_5667_) as u8);
    v_res_5669_ = l_Lean_PersistentArray_allM___redArg___lam__0(v_toPure_5666_, v_b_boxed_5668_);
    return v_res_5669_;
}
pub unsafe fn l_Lean_PersistentArray_allM___redArg___lam__1(
    mut v_p_5670_: *mut LeanObject,
    mut v_toBind_5671_: *mut LeanObject,
    mut v___f_5672_: *mut LeanObject,
    mut v_v_5673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    v___x_5674_ = lean_apply_1(v_p_5670_, v_v_5673_);
    v___x_5675_ = lean_apply_4(
        v_toBind_5671_,
        lean_box(0),
        lean_box(0),
        v___x_5674_,
        v___f_5672_,
    );
    return v___x_5675_;
}
pub unsafe fn l_Lean_PersistentArray_allM___redArg(
    mut v_inst_5676_: *mut LeanObject,
    mut v_a_5677_: *mut LeanObject,
    mut v_p_5678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5679_ = lean_ctor_get(v_inst_5676_, 0);
    v_toBind_5680_ = lean_ctor_get(v_inst_5676_, 1);
    lean_inc_n(v_toBind_5680_, 2);
    v_toPure_5681_ = lean_ctor_get(v_toApplicative_5679_, 1);
    lean_inc(v_toPure_5681_);
    v___f_5682_ = lean_alloc_closure(
        l_Lean_PersistentArray_allM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5682_, 0, v_toPure_5681_);
    lean_inc_ref(v___f_5682_);
    v___f_5683_ = lean_alloc_closure(
        l_Lean_PersistentArray_allM___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_5683_, 0, v_p_5678_);
    lean_closure_set(v___f_5683_, 1, v_toBind_5680_);
    lean_closure_set(v___f_5683_, 2, v___f_5682_);
    v___x_5684_ = l_Lean_PersistentArray_anyM___redArg(v_inst_5676_, v_a_5677_, v___f_5683_);
    v___x_5685_ = lean_apply_4(
        v_toBind_5680_,
        lean_box(0),
        lean_box(0),
        v___x_5684_,
        v___f_5682_,
    );
    return v___x_5685_;
}
pub unsafe fn l_Lean_PersistentArray_allM(
    mut v_00_u03b1_5686_: *mut LeanObject,
    mut v_m_5687_: *mut LeanObject,
    mut v_inst_5688_: *mut LeanObject,
    mut v_a_5689_: *mut LeanObject,
    mut v_p_5690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5691_ = lean_ctor_get(v_inst_5688_, 0);
    v_toBind_5692_ = lean_ctor_get(v_inst_5688_, 1);
    lean_inc_n(v_toBind_5692_, 2);
    v_toPure_5693_ = lean_ctor_get(v_toApplicative_5691_, 1);
    lean_inc(v_toPure_5693_);
    v___f_5694_ = lean_alloc_closure(
        l_Lean_PersistentArray_allM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5694_, 0, v_toPure_5693_);
    lean_inc_ref(v___f_5694_);
    v___f_5695_ = lean_alloc_closure(
        l_Lean_PersistentArray_allM___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_5695_, 0, v_p_5690_);
    lean_closure_set(v___f_5695_, 1, v_toBind_5692_);
    lean_closure_set(v___f_5695_, 2, v___f_5694_);
    v___x_5696_ = l_Lean_PersistentArray_anyM___redArg(v_inst_5688_, v_a_5689_, v___f_5695_);
    v___x_5697_ = lean_apply_4(
        v_toBind_5692_,
        lean_box(0),
        lean_box(0),
        v___x_5696_,
        v___f_5694_,
    );
    return v___x_5697_;
}
pub unsafe fn l_Lean_PersistentArray_any___redArg___lam__0(
    mut v_p_5698_: *mut LeanObject,
    mut v_x_5699_: *mut LeanObject,
) -> u8 {
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: u8 = 0;
    v___x_5700_ = lean_apply_1(v_p_5698_, v_x_5699_);
    v___x_5701_ = (lean_unbox(v___x_5700_) as u8);
    return v___x_5701_;
}
pub unsafe fn l_Lean_PersistentArray_any___redArg___lam__0___boxed(
    mut v_p_5702_: *mut LeanObject,
    mut v_x_5703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5704_: u8 = 0;
    let mut v_r_5705_: *mut LeanObject = core::ptr::null_mut();
    v_res_5704_ = l_Lean_PersistentArray_any___redArg___lam__0(v_p_5702_, v_x_5703_);
    v_r_5705_ = lean_box((v_res_5704_) as usize);
    return v_r_5705_;
}
pub unsafe fn l_Lean_PersistentArray_any___redArg(
    mut v_a_5706_: *mut LeanObject,
    mut v_p_5707_: *mut LeanObject,
) -> u8 {
    let mut v___f_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: u8 = 0;
    v___f_5708_ = lean_alloc_closure(
        l_Lean_PersistentArray_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5708_, 0, v_p_5707_);
    v___x_5709_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5710_ = l_Lean_PersistentArray_anyM___redArg(v___x_5709_, v_a_5706_, v___f_5708_);
    v___x_5711_ = (lean_unbox(v___x_5710_) as u8);
    lean_dec(v___x_5710_);
    return v___x_5711_;
}
pub unsafe fn l_Lean_PersistentArray_any___redArg___boxed(
    mut v_a_5712_: *mut LeanObject,
    mut v_p_5713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5714_: u8 = 0;
    let mut v_r_5715_: *mut LeanObject = core::ptr::null_mut();
    v_res_5714_ = l_Lean_PersistentArray_any___redArg(v_a_5712_, v_p_5713_);
    v_r_5715_ = lean_box((v_res_5714_) as usize);
    return v_r_5715_;
}
pub unsafe fn l_Lean_PersistentArray_any(
    mut v_00_u03b1_5716_: *mut LeanObject,
    mut v_a_5717_: *mut LeanObject,
    mut v_p_5718_: *mut LeanObject,
) -> u8 {
    let mut v___f_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: u8 = 0;
    v___f_5719_ = lean_alloc_closure(
        l_Lean_PersistentArray_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5719_, 0, v_p_5718_);
    v___x_5720_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5721_ = l_Lean_PersistentArray_anyM___redArg(v___x_5720_, v_a_5717_, v___f_5719_);
    v___x_5722_ = (lean_unbox(v___x_5721_) as u8);
    lean_dec(v___x_5721_);
    return v___x_5722_;
}
pub unsafe fn l_Lean_PersistentArray_any___boxed(
    mut v_00_u03b1_5723_: *mut LeanObject,
    mut v_a_5724_: *mut LeanObject,
    mut v_p_5725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5726_: u8 = 0;
    let mut v_r_5727_: *mut LeanObject = core::ptr::null_mut();
    v_res_5726_ = l_Lean_PersistentArray_any(v_00_u03b1_5723_, v_a_5724_, v_p_5725_);
    v_r_5727_ = lean_box((v_res_5726_) as usize);
    return v_r_5727_;
}
pub unsafe fn l_Lean_PersistentArray_all___redArg___lam__0(
    mut v_p_5728_: *mut LeanObject,
    mut v_x_5729_: *mut LeanObject,
) -> u8 {
    let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: u8 = 0;
    v___x_5730_ = lean_apply_1(v_p_5728_, v_x_5729_);
    v___x_5731_ = (lean_unbox(v___x_5730_) as u8);
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
    mut v_p_5734_: *mut LeanObject,
    mut v_x_5735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5736_: u8 = 0;
    let mut v_r_5737_: *mut LeanObject = core::ptr::null_mut();
    v_res_5736_ = l_Lean_PersistentArray_all___redArg___lam__0(v_p_5734_, v_x_5735_);
    v_r_5737_ = lean_box((v_res_5736_) as usize);
    return v_r_5737_;
}
pub unsafe fn l_Lean_PersistentArray_all___redArg(
    mut v_a_5738_: *mut LeanObject,
    mut v_p_5739_: *mut LeanObject,
) -> u8 {
    let mut v___f_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: u8 = 0;
    v___f_5740_ = lean_alloc_closure(
        l_Lean_PersistentArray_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5740_, 0, v_p_5739_);
    v___x_5741_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5742_ = l_Lean_PersistentArray_anyM___redArg(v___x_5741_, v_a_5738_, v___f_5740_);
    v___x_5743_ = (lean_unbox(v___x_5742_) as u8);
    lean_dec(v___x_5742_);
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
    mut v_a_5746_: *mut LeanObject,
    mut v_p_5747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5748_: u8 = 0;
    let mut v_r_5749_: *mut LeanObject = core::ptr::null_mut();
    v_res_5748_ = l_Lean_PersistentArray_all___redArg(v_a_5746_, v_p_5747_);
    v_r_5749_ = lean_box((v_res_5748_) as usize);
    return v_r_5749_;
}
pub unsafe fn l_Lean_PersistentArray_all(
    mut v_00_u03b1_5750_: *mut LeanObject,
    mut v_a_5751_: *mut LeanObject,
    mut v_p_5752_: *mut LeanObject,
) -> u8 {
    let mut v___f_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: u8 = 0;
    v___f_5753_ = lean_alloc_closure(
        l_Lean_PersistentArray_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5753_, 0, v_p_5752_);
    v___x_5754_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5755_ = l_Lean_PersistentArray_anyM___redArg(v___x_5754_, v_a_5751_, v___f_5753_);
    v___x_5756_ = (lean_unbox(v___x_5755_) as u8);
    lean_dec(v___x_5755_);
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
    mut v_00_u03b1_5759_: *mut LeanObject,
    mut v_a_5760_: *mut LeanObject,
    mut v_p_5761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5762_: u8 = 0;
    let mut v_r_5763_: *mut LeanObject = core::ptr::null_mut();
    v_res_5762_ = l_Lean_PersistentArray_all(v_00_u03b1_5759_, v_a_5760_, v_p_5761_);
    v_r_5763_ = lean_box((v_res_5762_) as usize);
    return v_r_5763_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___redArg___lam__0(
    mut v_cs_5764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    v___x_5765_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5765_, 0, v_cs_5764_);
    return v___x_5765_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___redArg___lam__2(
    mut v_vs_5766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5767_: *mut LeanObject = core::ptr::null_mut();
    v___x_5767_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5767_, 0, v_vs_5766_);
    return v___x_5767_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___redArg(
    mut v_inst_5770_: *mut LeanObject,
    mut v_f_5771_: *mut LeanObject,
    mut v_x_5772_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5772_) == 0 {
        let mut v_toApplicative_5773_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toFunctor_5774_: *mut LeanObject = core::ptr::null_mut();
        let mut v_cs_5775_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_5776_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5777_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5778_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_5779_: usize = 0;
        let mut v___x_5780_: usize = 0;
        let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_5773_ = lean_ctor_get(v_inst_5770_, 0);
        v_toFunctor_5774_ = lean_ctor_get(v_toApplicative_5773_, 0);
        v_cs_5775_ = lean_ctor_get(v_x_5772_, 0);
        lean_inc_ref(v_cs_5775_);
        lean_dec_ref_known(v_x_5772_, 1);
        v_map_5776_ = lean_ctor_get(v_toFunctor_5774_, 0);
        lean_inc(v_map_5776_);
        v___f_5777_ = l_Lean_PersistentArray_mapMAux___redArg___closed__0;
        lean_inc_ref(v_inst_5770_);
        v___f_5778_ = lean_alloc_closure(
            l_Lean_PersistentArray_mapMAux___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_5778_, 0, v_inst_5770_);
        lean_closure_set(v___f_5778_, 1, v_f_5771_);
        v_sz_5779_ = lean_array_size(v_cs_5775_);
        v___x_5780_ = 0usize;
        v___x_5781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
            lean_box(0),
            lean_box(0),
            lean_box(0),
            v_inst_5770_,
            v___f_5778_,
            v_sz_5779_,
            v___x_5780_,
            v_cs_5775_,
        );
        v___x_5782_ = lean_apply_4(
            v_map_5776_,
            lean_box(0),
            lean_box(0),
            v___f_5777_,
            v___x_5781_,
        );
        return v___x_5782_;
    } else {
        let mut v_toApplicative_5783_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toFunctor_5784_: *mut LeanObject = core::ptr::null_mut();
        let mut v_vs_5785_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_5786_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5787_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_5788_: usize = 0;
        let mut v___x_5789_: usize = 0;
        let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_5783_ = lean_ctor_get(v_inst_5770_, 0);
        v_toFunctor_5784_ = lean_ctor_get(v_toApplicative_5783_, 0);
        v_vs_5785_ = lean_ctor_get(v_x_5772_, 0);
        lean_inc_ref(v_vs_5785_);
        lean_dec_ref_known(v_x_5772_, 1);
        v_map_5786_ = lean_ctor_get(v_toFunctor_5784_, 0);
        lean_inc(v_map_5786_);
        v___f_5787_ = l_Lean_PersistentArray_mapMAux___redArg___closed__1;
        v_sz_5788_ = lean_array_size(v_vs_5785_);
        v___x_5789_ = 0usize;
        v___x_5790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
            lean_box(0),
            lean_box(0),
            lean_box(0),
            v_inst_5770_,
            v_f_5771_,
            v_sz_5788_,
            v___x_5789_,
            v_vs_5785_,
        );
        v___x_5791_ = lean_apply_4(
            v_map_5786_,
            lean_box(0),
            lean_box(0),
            v___f_5787_,
            v___x_5790_,
        );
        return v___x_5791_;
    }
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___redArg___lam__1(
    mut v_inst_5792_: *mut LeanObject,
    mut v_f_5793_: *mut LeanObject,
    mut v_c_5794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    v___x_5795_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_5792_, v_f_5793_, v_c_5794_);
    return v___x_5795_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux(
    mut v_00_u03b1_5796_: *mut LeanObject,
    mut v_m_5797_: *mut LeanObject,
    mut v_inst_5798_: *mut LeanObject,
    mut v_00_u03b2_5799_: *mut LeanObject,
    mut v_f_5800_: *mut LeanObject,
    mut v_x_5801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5802_: *mut LeanObject = core::ptr::null_mut();
    v___x_5802_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_5798_, v_f_5800_, v_x_5801_);
    return v___x_5802_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___redArg___lam__0(
    mut v_root_5803_: *mut LeanObject,
    mut v_size_5804_: *mut LeanObject,
    mut v_shift_5805_: usize,
    mut v_tailOff_5806_: *mut LeanObject,
    mut v_toPure_5807_: *mut LeanObject,
    mut v_tail_5808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    v___x_5809_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_5809_, 0, v_root_5803_);
    lean_ctor_set(v___x_5809_, 1, v_tail_5808_);
    lean_ctor_set(v___x_5809_, 2, v_size_5804_);
    lean_ctor_set(v___x_5809_, 3, v_tailOff_5806_);
    lean_ctor_set_usize(v___x_5809_, 4, v_shift_5805_);
    v___x_5810_ = lean_apply_2(v_toPure_5807_, lean_box(0), v___x_5809_);
    return v___x_5810_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___redArg___lam__0___boxed(
    mut v_root_5811_: *mut LeanObject,
    mut v_size_5812_: *mut LeanObject,
    mut v_shift_5813_: *mut LeanObject,
    mut v_tailOff_5814_: *mut LeanObject,
    mut v_toPure_5815_: *mut LeanObject,
    mut v_tail_5816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shift_boxed_5817_: usize = 0;
    let mut v_res_5818_: *mut LeanObject = core::ptr::null_mut();
    v_shift_boxed_5817_ = lean_unbox_usize(v_shift_5813_);
    lean_dec(v_shift_5813_);
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
    mut v_size_5819_: *mut LeanObject,
    mut v_shift_5820_: usize,
    mut v_tailOff_5821_: *mut LeanObject,
    mut v_toPure_5822_: *mut LeanObject,
    mut v_tail_5823_: *mut LeanObject,
    mut v_inst_5824_: *mut LeanObject,
    mut v_f_5825_: *mut LeanObject,
    mut v_toBind_5826_: *mut LeanObject,
    mut v_root_5827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5830_: usize = 0;
    let mut v___x_5831_: usize = 0;
    let mut v___x_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut LeanObject = core::ptr::null_mut();
    v___x_5828_ = lean_box_usize(v_shift_5820_);
    v___f_5829_ = lean_alloc_closure(
        l_Lean_PersistentArray_mapM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_5829_, 0, v_root_5827_);
    lean_closure_set(v___f_5829_, 1, v_size_5819_);
    lean_closure_set(v___f_5829_, 2, v___x_5828_);
    lean_closure_set(v___f_5829_, 3, v_tailOff_5821_);
    lean_closure_set(v___f_5829_, 4, v_toPure_5822_);
    v_sz_5830_ = lean_array_size(v_tail_5823_);
    v___x_5831_ = 0usize;
    v___x_5832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_5824_,
        v_f_5825_,
        v_sz_5830_,
        v___x_5831_,
        v_tail_5823_,
    );
    v___x_5833_ = lean_apply_4(
        v_toBind_5826_,
        lean_box(0),
        lean_box(0),
        v___x_5832_,
        v___f_5829_,
    );
    return v___x_5833_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___redArg___lam__1___boxed(
    mut v_size_5834_: *mut LeanObject,
    mut v_shift_5835_: *mut LeanObject,
    mut v_tailOff_5836_: *mut LeanObject,
    mut v_toPure_5837_: *mut LeanObject,
    mut v_tail_5838_: *mut LeanObject,
    mut v_inst_5839_: *mut LeanObject,
    mut v_f_5840_: *mut LeanObject,
    mut v_toBind_5841_: *mut LeanObject,
    mut v_root_5842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shift_boxed_5843_: usize = 0;
    let mut v_res_5844_: *mut LeanObject = core::ptr::null_mut();
    v_shift_boxed_5843_ = lean_unbox_usize(v_shift_5835_);
    lean_dec(v_shift_5835_);
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
    mut v_inst_5845_: *mut LeanObject,
    mut v_f_5846_: *mut LeanObject,
    mut v_t_5847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_5853_: usize = 0;
    let mut v_tailOff_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5848_ = lean_ctor_get(v_inst_5845_, 0);
    v_toBind_5849_ = lean_ctor_get(v_inst_5845_, 1);
    lean_inc_n(v_toBind_5849_, 2);
    v_root_5850_ = lean_ctor_get(v_t_5847_, 0);
    lean_inc_ref(v_root_5850_);
    v_tail_5851_ = lean_ctor_get(v_t_5847_, 1);
    lean_inc_ref(v_tail_5851_);
    v_size_5852_ = lean_ctor_get(v_t_5847_, 2);
    lean_inc(v_size_5852_);
    v_shift_5853_ = lean_ctor_get_usize(v_t_5847_, 4);
    v_tailOff_5854_ = lean_ctor_get(v_t_5847_, 3);
    lean_inc(v_tailOff_5854_);
    lean_dec_ref(v_t_5847_);
    v_toPure_5855_ = lean_ctor_get(v_toApplicative_5848_, 1);
    lean_inc(v_toPure_5855_);
    lean_inc(v_f_5846_);
    lean_inc_ref(v_inst_5845_);
    v___x_5856_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_5845_, v_f_5846_, v_root_5850_);
    v___x_5857_ = lean_box_usize(v_shift_5853_);
    v___f_5858_ = lean_alloc_closure(
        l_Lean_PersistentArray_mapM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_5858_, 0, v_size_5852_);
    lean_closure_set(v___f_5858_, 1, v___x_5857_);
    lean_closure_set(v___f_5858_, 2, v_tailOff_5854_);
    lean_closure_set(v___f_5858_, 3, v_toPure_5855_);
    lean_closure_set(v___f_5858_, 4, v_tail_5851_);
    lean_closure_set(v___f_5858_, 5, v_inst_5845_);
    lean_closure_set(v___f_5858_, 6, v_f_5846_);
    lean_closure_set(v___f_5858_, 7, v_toBind_5849_);
    v___x_5859_ = lean_apply_4(
        v_toBind_5849_,
        lean_box(0),
        lean_box(0),
        v___x_5856_,
        v___f_5858_,
    );
    return v___x_5859_;
}
pub unsafe fn l_Lean_PersistentArray_mapM(
    mut v_00_u03b1_5860_: *mut LeanObject,
    mut v_m_5861_: *mut LeanObject,
    mut v_inst_5862_: *mut LeanObject,
    mut v_00_u03b2_5863_: *mut LeanObject,
    mut v_f_5864_: *mut LeanObject,
    mut v_t_5865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    v___x_5866_ = l_Lean_PersistentArray_mapM___redArg(v_inst_5862_, v_f_5864_, v_t_5865_);
    return v___x_5866_;
}
pub unsafe fn l_Lean_PersistentArray_map___redArg___lam__0(
    mut v_f_5867_: *mut LeanObject,
    mut v_x_5868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    v___x_5869_ = lean_apply_1(v_f_5867_, v_x_5868_);
    return v___x_5869_;
}
pub unsafe fn l_Lean_PersistentArray_map___redArg(
    mut v_f_5870_: *mut LeanObject,
    mut v_t_5871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    v___f_5872_ = lean_alloc_closure(
        l_Lean_PersistentArray_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5872_, 0, v_f_5870_);
    v___x_5873_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5874_ = l_Lean_PersistentArray_mapM___redArg(v___x_5873_, v___f_5872_, v_t_5871_);
    return v___x_5874_;
}
pub unsafe fn l_Lean_PersistentArray_map(
    mut v_00_u03b1_5875_: *mut LeanObject,
    mut v_00_u03b2_5876_: *mut LeanObject,
    mut v_f_5877_: *mut LeanObject,
    mut v_t_5878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
    v___f_5879_ = lean_alloc_closure(
        l_Lean_PersistentArray_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5879_, 0, v_f_5877_);
    v___x_5880_ = l_Lean_PersistentArray_foldl___redArg___closed__9;
    v___x_5881_ = l_Lean_PersistentArray_mapM___redArg(v___x_5880_, v___f_5879_, v_t_5878_);
    return v___x_5881_;
}
pub unsafe fn l_Lean_PersistentArray_collectStats___redArg(
    mut v_x_5882_: *mut LeanObject,
    mut v_x_5883_: *mut LeanObject,
    mut v_x_5884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numNodes_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_depth_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tailSize_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5891_: u8 = 0;
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: u8 = 0;
    let mut v___x_5901_: u8 = 0;
    let mut v___x_5902_: usize = 0;
    let mut v___x_5903_: usize = 0;
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: usize = 0;
    let mut v___x_5906_: usize = 0;
    let mut v___x_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: u8 = 0;
    let mut v_isSharedCheck_5910_: u8 = 0;
    let mut v_numNodes_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_depth_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tailSize_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v___x_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: u8 = 0;
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5882_) == 0 {
                    v_cs_5885_ = lean_ctor_get(v_x_5882_, 0);
                    v_numNodes_5886_ = lean_ctor_get(v_x_5883_, 0);
                    v_depth_5887_ = lean_ctor_get(v_x_5883_, 1);
                    v_tailSize_5888_ = lean_ctor_get(v_x_5883_, 2);
                    v_isSharedCheck_5910_ = (!lean_is_exclusive(v_x_5883_)) as u8;
                    if v_isSharedCheck_5910_ == 0 {
                        v___x_5890_ = v_x_5883_;
                        v_isShared_5891_ = v_isSharedCheck_5910_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tailSize_5888_);
                        lean_inc(v_depth_5887_);
                        lean_inc(v_numNodes_5886_);
                        lean_dec(v_x_5883_);
                        v___x_5890_ = lean_box(0);
                        v_isShared_5891_ = v_isSharedCheck_5910_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_numNodes_5911_ = lean_ctor_get(v_x_5883_, 0);
                    v_depth_5912_ = lean_ctor_get(v_x_5883_, 1);
                    v_tailSize_5913_ = lean_ctor_get(v_x_5883_, 2);
                    v_isSharedCheck_5926_ = (!lean_is_exclusive(v_x_5883_)) as u8;
                    if v_isSharedCheck_5926_ == 0 {
                        v___x_5915_ = v_x_5883_;
                        v_isShared_5916_ = v_isSharedCheck_5926_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_tailSize_5913_);
                        lean_inc(v_depth_5912_);
                        lean_inc(v_numNodes_5911_);
                        lean_dec(v_x_5883_);
                        v___x_5915_ = lean_box(0);
                        v_isShared_5916_ = v_isSharedCheck_5926_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5892_ = lean_unsigned_to_nat(1);
                v___x_5893_ = lean_nat_add(v_numNodes_5886_, v___x_5892_);
                lean_dec(v_numNodes_5886_);
                v___x_5909_ = lean_nat_dec_le(v_x_5884_, v_depth_5887_);
                if v___x_5909_ == 0 {
                    lean_dec(v_depth_5887_);
                    lean_inc(v_x_5884_);
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
                    lean_ctor_set(v___x_5890_, 1, v___y_5895_);
                    lean_ctor_set(v___x_5890_, 0, v___x_5893_);
                    v___x_5897_ = v___x_5890_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5908_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5908_, 0, v___x_5893_);
                    lean_ctor_set(v_reuseFailAlloc_5908_, 1, v___y_5895_);
                    lean_ctor_set(v_reuseFailAlloc_5908_, 2, v_tailSize_5888_);
                    v___x_5897_ = v_reuseFailAlloc_5908_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5898_ = lean_unsigned_to_nat(0);
                v___x_5899_ = lean_array_get_size(v_cs_5885_);
                v___x_5900_ = lean_nat_dec_lt(v___x_5898_, v___x_5899_);
                if v___x_5900_ == 0 {
                    lean_dec(v_x_5884_);
                    return v___x_5897_;
                } else {
                    v___x_5901_ = lean_nat_dec_le(v___x_5899_, v___x_5899_);
                    if v___x_5901_ == 0 {
                        if v___x_5900_ == 0 {
                            lean_dec(v_x_5884_);
                            return v___x_5897_;
                        } else {
                            v___x_5902_ = 0usize;
                            v___x_5903_ = lean_usize_of_nat(v___x_5899_);
                            v___x_5904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_5884_, v_cs_5885_, v___x_5902_, v___x_5903_, v___x_5897_);
                            lean_dec(v_x_5884_);
                            return v___x_5904_;
                        }
                    } else {
                        v___x_5905_ = 0usize;
                        v___x_5906_ = lean_usize_of_nat(v___x_5899_);
                        v___x_5907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_5884_, v_cs_5885_, v___x_5905_, v___x_5906_, v___x_5897_);
                        lean_dec(v_x_5884_);
                        return v___x_5907_;
                    }
                }
            }
            4 => {
                v___x_5917_ = lean_unsigned_to_nat(1);
                v___x_5918_ = lean_nat_add(v_numNodes_5911_, v___x_5917_);
                lean_dec(v_numNodes_5911_);
                v___x_5919_ = lean_nat_dec_le(v_x_5884_, v_depth_5912_);
                if v___x_5919_ == 0 {
                    lean_dec(v_depth_5912_);
                    if v_isShared_5916_ == 0 {
                        lean_ctor_set(v___x_5915_, 1, v_x_5884_);
                        lean_ctor_set(v___x_5915_, 0, v___x_5918_);
                        v___x_5921_ = v___x_5915_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5922_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5922_, 0, v___x_5918_);
                        lean_ctor_set(v_reuseFailAlloc_5922_, 1, v_x_5884_);
                        lean_ctor_set(v_reuseFailAlloc_5922_, 2, v_tailSize_5913_);
                        v___x_5921_ = v_reuseFailAlloc_5922_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_x_5884_);
                    if v_isShared_5916_ == 0 {
                        lean_ctor_set(v___x_5915_, 0, v___x_5918_);
                        v___x_5924_ = v___x_5915_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5925_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5925_, 0, v___x_5918_);
                        lean_ctor_set(v_reuseFailAlloc_5925_, 1, v_depth_5912_);
                        lean_ctor_set(v_reuseFailAlloc_5925_, 2, v_tailSize_5913_);
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
    mut v_x_5927_: *mut LeanObject,
    mut v_as_5928_: *mut LeanObject,
    mut v_i_5929_: usize,
    mut v_stop_5930_: usize,
    mut v_b_5931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5932_: u8 = 0;
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: usize = 0;
    let mut v___x_5938_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5932_ = lean_usize_dec_eq(v_i_5929_, v_stop_5930_);
                if v___x_5932_ == 0 {
                    v___x_5933_ = lean_array_uget_borrowed(v_as_5928_, v_i_5929_);
                    v___x_5934_ = lean_unsigned_to_nat(1);
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
    mut v_x_5940_: *mut LeanObject,
    mut v_as_5941_: *mut LeanObject,
    mut v_i_5942_: *mut LeanObject,
    mut v_stop_5943_: *mut LeanObject,
    mut v_b_5944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5945_: usize = 0;
    let mut v_stop_boxed_5946_: usize = 0;
    let mut v_res_5947_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5945_ = lean_unbox_usize(v_i_5942_);
    lean_dec(v_i_5942_);
    v_stop_boxed_5946_ = lean_unbox_usize(v_stop_5943_);
    lean_dec(v_stop_5943_);
    v_res_5947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_5940_, v_as_5941_, v_i_boxed_5945_, v_stop_boxed_5946_, v_b_5944_);
    lean_dec_ref(v_as_5941_);
    lean_dec(v_x_5940_);
    return v_res_5947_;
}
pub unsafe fn l_Lean_PersistentArray_collectStats___redArg___boxed(
    mut v_x_5948_: *mut LeanObject,
    mut v_x_5949_: *mut LeanObject,
    mut v_x_5950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5951_: *mut LeanObject = core::ptr::null_mut();
    v_res_5951_ = l_Lean_PersistentArray_collectStats___redArg(v_x_5948_, v_x_5949_, v_x_5950_);
    lean_dec_ref(v_x_5948_);
    return v_res_5951_;
}
pub unsafe fn l_Lean_PersistentArray_collectStats(
    mut v_00_u03b1_5952_: *mut LeanObject,
    mut v_x_5953_: *mut LeanObject,
    mut v_x_5954_: *mut LeanObject,
    mut v_x_5955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    v___x_5956_ = l_Lean_PersistentArray_collectStats___redArg(v_x_5953_, v_x_5954_, v_x_5955_);
    return v___x_5956_;
}
pub unsafe fn l_Lean_PersistentArray_collectStats___boxed(
    mut v_00_u03b1_5957_: *mut LeanObject,
    mut v_x_5958_: *mut LeanObject,
    mut v_x_5959_: *mut LeanObject,
    mut v_x_5960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5961_: *mut LeanObject = core::ptr::null_mut();
    v_res_5961_ =
        l_Lean_PersistentArray_collectStats(v_00_u03b1_5957_, v_x_5958_, v_x_5959_, v_x_5960_);
    lean_dec_ref(v_x_5958_);
    return v_res_5961_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(
    mut v_00_u03b1_5962_: *mut LeanObject,
    mut v_x_5963_: *mut LeanObject,
    mut v_as_5964_: *mut LeanObject,
    mut v_i_5965_: usize,
    mut v_stop_5966_: usize,
    mut v_b_5967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    v___x_5968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_5963_, v_as_5964_, v_i_5965_, v_stop_5966_, v_b_5967_);
    return v___x_5968_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___boxed(
    mut v_00_u03b1_5969_: *mut LeanObject,
    mut v_x_5970_: *mut LeanObject,
    mut v_as_5971_: *mut LeanObject,
    mut v_i_5972_: *mut LeanObject,
    mut v_stop_5973_: *mut LeanObject,
    mut v_b_5974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5975_: usize = 0;
    let mut v_stop_boxed_5976_: usize = 0;
    let mut v_res_5977_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5975_ = lean_unbox_usize(v_i_5972_);
    lean_dec(v_i_5972_);
    v_stop_boxed_5976_ = lean_unbox_usize(v_stop_5973_);
    lean_dec(v_stop_5973_);
    v_res_5977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(v_00_u03b1_5969_, v_x_5970_, v_as_5971_, v_i_boxed_5975_, v_stop_boxed_5976_, v_b_5974_);
    lean_dec_ref(v_as_5971_);
    lean_dec(v_x_5970_);
    return v_res_5977_;
}
pub unsafe fn l_Lean_PersistentArray_stats___redArg(
    mut v_r_5978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    v_root_5979_ = lean_ctor_get(v_r_5978_, 0);
    v_tail_5980_ = lean_ctor_get(v_r_5978_, 1);
    v___x_5981_ = lean_unsigned_to_nat(0);
    v___x_5982_ = lean_array_get_size(v_tail_5980_);
    v___x_5983_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_5983_, 0, v___x_5981_);
    lean_ctor_set(v___x_5983_, 1, v___x_5981_);
    lean_ctor_set(v___x_5983_, 2, v___x_5982_);
    v___x_5984_ =
        l_Lean_PersistentArray_collectStats___redArg(v_root_5979_, v___x_5983_, v___x_5981_);
    return v___x_5984_;
}
pub unsafe fn l_Lean_PersistentArray_stats___redArg___boxed(
    mut v_r_5985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5986_: *mut LeanObject = core::ptr::null_mut();
    v_res_5986_ = l_Lean_PersistentArray_stats___redArg(v_r_5985_);
    lean_dec_ref(v_r_5985_);
    return v_res_5986_;
}
pub unsafe fn l_Lean_PersistentArray_stats(
    mut v_00_u03b1_5987_: *mut LeanObject,
    mut v_r_5988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    v___x_5989_ = l_Lean_PersistentArray_stats___redArg(v_r_5988_);
    return v___x_5989_;
}
pub unsafe fn l_Lean_PersistentArray_stats___boxed(
    mut v_00_u03b1_5990_: *mut LeanObject,
    mut v_r_5991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5992_: *mut LeanObject = core::ptr::null_mut();
    v_res_5992_ = l_Lean_PersistentArray_stats(v_00_u03b1_5990_, v_r_5991_);
    lean_dec_ref(v_r_5991_);
    return v_res_5992_;
}
pub unsafe fn l_Lean_PersistentArray_Stats_toString(
    mut v_s_5997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numNodes_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_depth_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tailSize_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut LeanObject = core::ptr::null_mut();
    v_numNodes_5998_ = lean_ctor_get(v_s_5997_, 0);
    lean_inc(v_numNodes_5998_);
    v_depth_5999_ = lean_ctor_get(v_s_5997_, 1);
    lean_inc(v_depth_5999_);
    v_tailSize_6000_ = lean_ctor_get(v_s_5997_, 2);
    lean_inc(v_tailSize_6000_);
    lean_dec_ref(v_s_5997_);
    v___x_6001_ = l_Lean_PersistentArray_Stats_toString___closed__0;
    v___x_6002_ = l_Nat_reprFast(v_numNodes_5998_);
    v___x_6003_ = lean_string_append(v___x_6001_, v___x_6002_);
    lean_dec_ref(v___x_6002_);
    v___x_6004_ = l_Lean_PersistentArray_Stats_toString___closed__1;
    v___x_6005_ = lean_string_append(v___x_6003_, v___x_6004_);
    v___x_6006_ = l_Nat_reprFast(v_depth_5999_);
    v___x_6007_ = lean_string_append(v___x_6005_, v___x_6006_);
    lean_dec_ref(v___x_6006_);
    v___x_6008_ = l_Lean_PersistentArray_Stats_toString___closed__2;
    v___x_6009_ = lean_string_append(v___x_6007_, v___x_6008_);
    v___x_6010_ = l_Nat_reprFast(v_tailSize_6000_);
    v___x_6011_ = lean_string_append(v___x_6009_, v___x_6010_);
    lean_dec_ref(v___x_6010_);
    v___x_6012_ = l_Lean_PersistentArray_Stats_toString___closed__3;
    v___x_6013_ = lean_string_append(v___x_6011_, v___x_6012_);
    return v___x_6013_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(
    mut v_v_6016_: *mut LeanObject,
    mut v_j_6017_: *mut LeanObject,
    mut v_a_6018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6020_: u8 = 0;
    let mut v_one_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6019_ = lean_unsigned_to_nat(0);
                v_isZero_6020_ = lean_nat_dec_eq(v_j_6017_, v_zero_6019_);
                if v_isZero_6020_ == 1 {
                    lean_dec(v_j_6017_);
                    lean_dec(v_v_6016_);
                    return v_a_6018_;
                } else {
                    v_one_6021_ = lean_unsigned_to_nat(1);
                    v_n_6022_ = lean_nat_sub(v_j_6017_, v_one_6021_);
                    lean_dec(v_j_6017_);
                    lean_inc(v_v_6016_);
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
pub unsafe fn _init_l_Lean_mkPersistentArray___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    v___x_6025_ = l_Lean_PersistentArray_empty(lean_box(0));
    return v___x_6025_;
}
pub unsafe fn l_Lean_mkPersistentArray___redArg(
    mut v_n_6026_: *mut LeanObject,
    mut v_v_6027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    v___x_6028_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkPersistentArray___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_mkPersistentArray___redArg___closed__0_once),
        _init_l_Lean_mkPersistentArray___redArg___closed__0,
    );
    v___x_6029_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_6027_, v_n_6026_, v___x_6028_);
    return v___x_6029_;
}
pub unsafe fn l_Lean_mkPersistentArray(
    mut v_00_u03b1_6030_: *mut LeanObject,
    mut v_n_6031_: *mut LeanObject,
    mut v_v_6032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6033_: *mut LeanObject = core::ptr::null_mut();
    v___x_6033_ = l_Lean_mkPersistentArray___redArg(v_n_6031_, v_v_6032_);
    return v___x_6033_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(
    mut v_00_u03b1_6034_: *mut LeanObject,
    mut v_v_6035_: *mut LeanObject,
    mut v_n_6036_: *mut LeanObject,
    mut v_j_6037_: *mut LeanObject,
    mut v_a_6038_: *mut LeanObject,
    mut v_a_6039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
    v___x_6040_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_6035_, v_j_6037_, v_a_6039_);
    return v___x_6040_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___boxed(
    mut v_00_u03b1_6041_: *mut LeanObject,
    mut v_v_6042_: *mut LeanObject,
    mut v_n_6043_: *mut LeanObject,
    mut v_j_6044_: *mut LeanObject,
    mut v_a_6045_: *mut LeanObject,
    mut v_a_6046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6047_: *mut LeanObject = core::ptr::null_mut();
    v_res_6047_ =
        l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(
            v_00_u03b1_6041_,
            v_v_6042_,
            v_n_6043_,
            v_j_6044_,
            v_a_6045_,
            v_a_6046_,
        );
    lean_dec(v_n_6043_);
    return v_res_6047_;
}
pub unsafe fn l_Lean_mkPArray___redArg(
    mut v_n_6048_: *mut LeanObject,
    mut v_v_6049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    v___x_6050_ = l_Lean_mkPersistentArray___redArg(v_n_6048_, v_v_6049_);
    return v___x_6050_;
}
pub unsafe fn l_Lean_mkPArray(
    mut v_00_u03b1_6051_: *mut LeanObject,
    mut v_n_6052_: *mut LeanObject,
    mut v_v_6053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6054_: *mut LeanObject = core::ptr::null_mut();
    v___x_6054_ = l_Lean_mkPersistentArray___redArg(v_n_6052_, v_v_6053_);
    return v___x_6054_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(
    mut v_a_6055_: *mut LeanObject,
    mut v_a_6056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6055_) == 0 {
                    return v_a_6056_;
                } else {
                    v_head_6057_ = lean_ctor_get(v_a_6055_, 0);
                    lean_inc(v_head_6057_);
                    v_tail_6058_ = lean_ctor_get(v_a_6055_, 1);
                    lean_inc(v_tail_6058_);
                    lean_dec_ref_known(v_a_6055_, 2);
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
    mut v_00_u03b1_6061_: *mut LeanObject,
    mut v_a_6062_: *mut LeanObject,
    mut v_a_6063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    v___x_6064_ = l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(
        v_a_6062_, v_a_6063_,
    );
    return v___x_6064_;
}
pub unsafe fn l_List_toPArray_x27___redArg(mut v_xs_6065_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut LeanObject = core::ptr::null_mut();
    v___x_6066_ = lean_unsigned_to_nat(32);
    v___x_6067_ = lean_mk_empty_array_with_capacity(v___x_6066_);
    lean_dec_ref(v___x_6067_);
    v___x_6068_ = lean_obj_once(
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
    mut v_00_u03b1_6070_: *mut LeanObject,
    mut v_xs_6071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    v___x_6072_ = l_List_toPArray_x27___redArg(v_xs_6071_);
    return v___x_6072_;
}
pub unsafe fn l_Array_toPArray_x27___redArg(mut v_xs_6073_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: u8 = 0;
    v___x_6074_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkPersistentArray___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_mkPersistentArray___redArg___closed__0_once),
        _init_l_Lean_mkPersistentArray___redArg___closed__0,
    );
    v___x_6075_ = lean_unsigned_to_nat(0);
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
                let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
                v___x_6079_ = 0usize;
                v___x_6080_ = lean_usize_of_nat(v___x_6076_);
                v___x_6081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_6073_, v___x_6079_, v___x_6080_, v___x_6074_);
                return v___x_6081_;
            }
        } else {
            let mut v___x_6082_: usize = 0;
            let mut v___x_6083_: usize = 0;
            let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
            v___x_6082_ = 0usize;
            v___x_6083_ = lean_usize_of_nat(v___x_6076_);
            v___x_6084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_6073_, v___x_6082_, v___x_6083_, v___x_6074_);
            return v___x_6084_;
        }
    }
}
pub unsafe fn l_Array_toPArray_x27___redArg___boxed(
    mut v_xs_6085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6086_: *mut LeanObject = core::ptr::null_mut();
    v_res_6086_ = l_Array_toPArray_x27___redArg(v_xs_6085_);
    lean_dec_ref(v_xs_6085_);
    return v_res_6086_;
}
pub unsafe fn l_Array_toPArray_x27(
    mut v_00_u03b1_6087_: *mut LeanObject,
    mut v_xs_6088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    v___x_6089_ = l_Array_toPArray_x27___redArg(v_xs_6088_);
    return v___x_6089_;
}
pub unsafe fn l_Array_toPArray_x27___boxed(
    mut v_00_u03b1_6090_: *mut LeanObject,
    mut v_xs_6091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6092_: *mut LeanObject = core::ptr::null_mut();
    v_res_6092_ = l_Array_toPArray_x27(v_00_u03b1_6090_, v_xs_6091_);
    lean_dec_ref(v_xs_6091_);
    return v_res_6092_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_PersistentArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Fold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_PersistentArray_initShift = _init_l_Lean_PersistentArray_initShift();
    l_Lean_PersistentArray_branching = _init_l_Lean_PersistentArray_branching();
    l_Lean_PersistentArray_tooBig = _init_l_Lean_PersistentArray_tooBig();
    lean_mark_persistent(l_Lean_PersistentArray_tooBig);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_PersistentArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_PersistentArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Fold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_PersistentArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_PersistentArray(builtin);
}
