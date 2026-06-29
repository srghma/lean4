// Lean compiler output
// Module: Lean.Data.SMap
// Imports: Std.Data.HashMap.Basic Lean.Data.PersistentHashMap Std.Data.HashMap.Iterator Lean.Data.Iterators.Producers.PersistentHashMap Init.Data.Iterators.Combinators.Append
use crate::r#gen::Init::Control::Except::{
    l_ExceptT_bind, l_ExceptT_instMonad___redArg___lam__1, l_ExceptT_instMonad___redArg___lam__4,
    l_ExceptT_instMonad___redArg___lam__7, l_ExceptT_instMonad___redArg___lam__9, l_ExceptT_map,
    l_ExceptT_pure,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Iterators::Combinators::Append::{
    initialize_Init_Data_Iterators_Combinators_Append,
    runtime_initialize_Init_Data_Iterators_Combinators_Append,
};
use crate::r#gen::Init::Data::Repr::{
    l_List_repr___redArg, l_Prod_repr___boxed, l_Repr_addAppParen,
    l_instReprTupleOfRepr___redArg___lam__0,
};
use crate::r#gen::Init::Prelude::{l_List_foldl___redArg, l_panic___redArg};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Iterators::Producers::PersistentHashMap::{
    initialize_Lean_Data_Iterators_Producers_PersistentHashMap,
    l_Lean_PersistentHashMap_Zipper_prependNode___redArg,
    runtime_initialize_Lean_Data_Iterators_Producers_PersistentHashMap,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    initialize_Lean_Data_PersistentHashMap, l_Lean_PersistentHashMap_contains___redArg,
    l_Lean_PersistentHashMap_find_x3f___redArg, l_Lean_PersistentHashMap_foldl___redArg,
    l_Lean_PersistentHashMap_foldlMAux___redArg, l_Lean_PersistentHashMap_forM___redArg,
    l_Lean_PersistentHashMap_insert___redArg, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
    runtime_initialize_Lean_Data_PersistentHashMap,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::l_Std_DHashMap_Internal_AssocList_foldlM___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
use crate::r#gen::Std::Data::DHashMap::Raw::l_Std_DHashMap_Raw_Internal_numBuckets___redArg;
use crate::r#gen::Std::Data::HashMap::Basic::{
    initialize_Std_Data_HashMap_Basic, runtime_initialize_Std_Data_HashMap_Basic,
};
use crate::r#gen::Std::Data::HashMap::Iterator::{
    initialize_Std_Data_HashMap_Iterator, runtime_initialize_Std_Data_HashMap_Iterator,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_dec_le, lean_nat_dec_lt,
};
static mut l_Lean_SMap_instInhabited___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SMap_instInhabited___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_SMap_instInhabited___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SMap_instInhabited___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_SMap_instInhabited___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SMap_instInhabited___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_SMap_instInhabited___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SMap_instInhabited___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_SMap_instInhabited___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SMap_instInhabited___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_SMap_find_x21___redArg___closed__0_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 83, 77, 97, 112, 0,
        ],
    };
static mut l_Lean_SMap_find_x21___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_find_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_SMap_find_x21___redArg___closed__1_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            76, 101, 97, 110, 46, 83, 77, 97, 112, 46, 102, 105, 110, 100, 33, 0,
        ],
    };
static mut l_Lean_SMap_find_x21___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_find_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_SMap_find_x21___redArg___closed__2_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32,
            109, 97, 112, 0,
        ],
    };
static mut l_Lean_SMap_find_x21___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_find_x21___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_SMap_find_x21___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SMap_find_x21___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_SMap_fold___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SMap_fold___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SMap_fold___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SMap_fold___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SMap_fold___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SMap_fold___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SMap_fold___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SMap_fold___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_SMap_fold___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_SMap_fold___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_SMap_fold___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_SMap_toList___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_SMap_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SMap_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprSMap___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [46, 116, 111, 83, 77, 97, 112, 0],
};
static mut l_Lean_instReprSMap___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprSMap___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprSMap___redArg___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprSMap___redArg___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprSMap___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprSMap___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_SMap_instInhabited___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_770_ = crate::leanh::lean_box(0);
    v___x_771_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_772_ = lean_mk_array(v___x_771_, v___x_770_);
    return v___x_772_;
}
pub unsafe fn _init_l_Lean_SMap_instInhabited___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_773_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__0_once),
        _init_l_Lean_SMap_instInhabited___closed__0,
    );
    v___x_774_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_775_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_775_, 0, v___x_774_);
    crate::leanh::lean_ctor_set(v___x_775_, 1, v___x_773_);
    return v___x_775_;
}
pub unsafe fn _init_l_Lean_SMap_instInhabited___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_776_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_776_;
}
pub unsafe fn _init_l_Lean_SMap_instInhabited___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_777_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__2),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__2_once),
        _init_l_Lean_SMap_instInhabited___closed__2,
    );
    v___x_778_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_778_, 0, v___x_777_);
    return v___x_778_;
}
pub unsafe fn _init_l_Lean_SMap_instInhabited___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: u8 = 0;
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_779_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__3),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__3_once),
        _init_l_Lean_SMap_instInhabited___closed__3,
    );
    v___x_780_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__1),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__1_once),
        _init_l_Lean_SMap_instInhabited___closed__1,
    );
    v___x_781_ = 1;
    v___x_782_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_782_, 0, v___x_780_);
    crate::leanh::lean_ctor_set(v___x_782_, 1, v___x_779_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_782_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v___x_781_,
    );
    return v___x_782_;
}
pub unsafe fn l_Lean_SMap_instInhabited(
    mut v_00_u03b1_783_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_784_: *mut crate::leanh::LeanObject,
    mut v_inst_785_: *mut crate::leanh::LeanObject,
    mut v_inst_786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_787_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__4),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__4_once),
        _init_l_Lean_SMap_instInhabited___closed__4,
    );
    return v___x_787_;
}
pub unsafe fn l_Lean_SMap_instInhabited___boxed(
    mut v_00_u03b1_788_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_789_: *mut crate::leanh::LeanObject,
    mut v_inst_790_: *mut crate::leanh::LeanObject,
    mut v_inst_791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_792_ =
        l_Lean_SMap_instInhabited(v_00_u03b1_788_, v_00_u03b2_789_, v_inst_790_, v_inst_791_);
    crate::leanh::lean_dec_ref(v_inst_791_);
    crate::leanh::lean_dec_ref(v_inst_790_);
    return v_res_792_;
}
pub unsafe fn l_Lean_SMap_empty(
    mut v_00_u03b1_793_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_794_: *mut crate::leanh::LeanObject,
    mut v_inst_795_: *mut crate::leanh::LeanObject,
    mut v_inst_796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_797_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__4),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__4_once),
        _init_l_Lean_SMap_instInhabited___closed__4,
    );
    return v___x_797_;
}
pub unsafe fn l_Lean_SMap_empty___boxed(
    mut v_00_u03b1_798_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_799_: *mut crate::leanh::LeanObject,
    mut v_inst_800_: *mut crate::leanh::LeanObject,
    mut v_inst_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_802_ = l_Lean_SMap_empty(v_00_u03b1_798_, v_00_u03b2_799_, v_inst_800_, v_inst_801_);
    crate::leanh::lean_dec_ref(v_inst_801_);
    crate::leanh::lean_dec_ref(v_inst_800_);
    return v_res_802_;
}
pub unsafe fn l_Lean_SMap_fromHashMap___redArg(
    mut v_m_803_: *mut crate::leanh::LeanObject,
    mut v_stage_u2081_804_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_805_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__3),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__3_once),
        _init_l_Lean_SMap_instInhabited___closed__3,
    );
    v___x_806_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_806_, 0, v_m_803_);
    crate::leanh::lean_ctor_set(v___x_806_, 1, v___x_805_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_806_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v_stage_u2081_804_,
    );
    return v___x_806_;
}
pub unsafe fn l_Lean_SMap_fromHashMap___redArg___boxed(
    mut v_m_807_: *mut crate::leanh::LeanObject,
    mut v_stage_u2081_808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_boxed_809_: u8 = 0;
    let mut v_res_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stage_u2081_boxed_809_ = (crate::leanh::lean_unbox(v_stage_u2081_808_) as u8);
    v_res_810_ = l_Lean_SMap_fromHashMap___redArg(v_m_807_, v_stage_u2081_boxed_809_);
    return v_res_810_;
}
pub unsafe fn l_Lean_SMap_fromHashMap(
    mut v_00_u03b1_811_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_812_: *mut crate::leanh::LeanObject,
    mut v_inst_813_: *mut crate::leanh::LeanObject,
    mut v_inst_814_: *mut crate::leanh::LeanObject,
    mut v_m_815_: *mut crate::leanh::LeanObject,
    mut v_stage_u2081_816_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_817_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__3),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__3_once),
        _init_l_Lean_SMap_instInhabited___closed__3,
    );
    v___x_818_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_818_, 0, v_m_815_);
    crate::leanh::lean_ctor_set(v___x_818_, 1, v___x_817_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_818_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v_stage_u2081_816_,
    );
    return v___x_818_;
}
pub unsafe fn l_Lean_SMap_fromHashMap___boxed(
    mut v_00_u03b1_819_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_820_: *mut crate::leanh::LeanObject,
    mut v_inst_821_: *mut crate::leanh::LeanObject,
    mut v_inst_822_: *mut crate::leanh::LeanObject,
    mut v_m_823_: *mut crate::leanh::LeanObject,
    mut v_stage_u2081_824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_boxed_825_: u8 = 0;
    let mut v_res_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stage_u2081_boxed_825_ = (crate::leanh::lean_unbox(v_stage_u2081_824_) as u8);
    v_res_826_ = l_Lean_SMap_fromHashMap(
        v_00_u03b1_819_,
        v_00_u03b2_820_,
        v_inst_821_,
        v_inst_822_,
        v_m_823_,
        v_stage_u2081_boxed_825_,
    );
    crate::leanh::lean_dec_ref(v_inst_822_);
    crate::leanh::lean_dec_ref(v_inst_821_);
    return v_res_826_;
}
pub unsafe fn l_Lean_SMap_insert___redArg(
    mut v_inst_827_: *mut crate::leanh::LeanObject,
    mut v_inst_828_: *mut crate::leanh::LeanObject,
    mut v_x_829_: *mut crate::leanh::LeanObject,
    mut v_x_830_: *mut crate::leanh::LeanObject,
    mut v_x_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_832_: u8 = 0;
    let mut v_map_u2081_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_837_: u8 = 0;
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_842_: u8 = 0;
    let mut v_map_u2081_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_847_: u8 = 0;
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_852_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_832_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_829_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_832_ == 0 {
                    v_map_u2081_833_ = crate::leanh::lean_ctor_get(v_x_829_, 0);
                    v_map_u2082_834_ = crate::leanh::lean_ctor_get(v_x_829_, 1);
                    v_isSharedCheck_842_ = (!crate::leanh::lean_is_exclusive(v_x_829_)) as u8;
                    if v_isSharedCheck_842_ == 0 {
                        v___x_836_ = v_x_829_;
                        v_isShared_837_ = v_isSharedCheck_842_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_u2082_834_);
                        crate::leanh::lean_inc(v_map_u2081_833_);
                        crate::leanh::lean_dec(v_x_829_);
                        v___x_836_ = crate::leanh::lean_box(0);
                        v_isShared_837_ = v_isSharedCheck_842_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_843_ = crate::leanh::lean_ctor_get(v_x_829_, 0);
                    v_map_u2082_844_ = crate::leanh::lean_ctor_get(v_x_829_, 1);
                    v_isSharedCheck_852_ = (!crate::leanh::lean_is_exclusive(v_x_829_)) as u8;
                    if v_isSharedCheck_852_ == 0 {
                        v___x_846_ = v_x_829_;
                        v_isShared_847_ = v_isSharedCheck_852_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_u2082_844_);
                        crate::leanh::lean_inc(v_map_u2081_843_);
                        crate::leanh::lean_dec(v_x_829_);
                        v___x_846_ = crate::leanh::lean_box(0);
                        v_isShared_847_ = v_isSharedCheck_852_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_838_ = l_Lean_PersistentHashMap_insert___redArg(
                    v_inst_827_,
                    v_inst_828_,
                    v_map_u2082_834_,
                    v_x_830_,
                    v_x_831_,
                );
                if v_isShared_837_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_836_, 1, v___x_838_);
                    v___x_840_ = v___x_836_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_841_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_841_, 0, v_map_u2081_833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_838_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_841_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_832_,
                    );
                    v___x_840_ = v_reuseFailAlloc_841_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_840_;
            }
            3 => {
                v___x_848_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v_inst_827_,
                    v_inst_828_,
                    v_map_u2081_843_,
                    v_x_830_,
                    v_x_831_,
                );
                if v_isShared_847_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_846_, 0, v___x_848_);
                    v___x_850_ = v___x_846_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_851_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_851_, 1, v_map_u2082_844_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_851_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_832_,
                    );
                    v___x_850_ = v_reuseFailAlloc_851_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_850_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_insert(
    mut v_00_u03b1_853_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_854_: *mut crate::leanh::LeanObject,
    mut v_inst_855_: *mut crate::leanh::LeanObject,
    mut v_inst_856_: *mut crate::leanh::LeanObject,
    mut v_x_857_: *mut crate::leanh::LeanObject,
    mut v_x_858_: *mut crate::leanh::LeanObject,
    mut v_x_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ =
        l_Lean_SMap_insert___redArg(v_inst_855_, v_inst_856_, v_x_857_, v_x_858_, v_x_859_);
    return v___x_860_;
}
pub unsafe fn l_Lean_SMap_insert_x27___redArg(
    mut v_inst_861_: *mut crate::leanh::LeanObject,
    mut v_inst_862_: *mut crate::leanh::LeanObject,
    mut v_x_863_: *mut crate::leanh::LeanObject,
    mut v_x_864_: *mut crate::leanh::LeanObject,
    mut v_x_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_866_: u8 = 0;
    let mut v_map_u2081_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_871_: u8 = 0;
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_876_: u8 = 0;
    let mut v_map_u2081_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_881_: u8 = 0;
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_866_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_863_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_866_ == 0 {
                    v_map_u2081_867_ = crate::leanh::lean_ctor_get(v_x_863_, 0);
                    v_map_u2082_868_ = crate::leanh::lean_ctor_get(v_x_863_, 1);
                    v_isSharedCheck_876_ = (!crate::leanh::lean_is_exclusive(v_x_863_)) as u8;
                    if v_isSharedCheck_876_ == 0 {
                        v___x_870_ = v_x_863_;
                        v_isShared_871_ = v_isSharedCheck_876_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_u2082_868_);
                        crate::leanh::lean_inc(v_map_u2081_867_);
                        crate::leanh::lean_dec(v_x_863_);
                        v___x_870_ = crate::leanh::lean_box(0);
                        v_isShared_871_ = v_isSharedCheck_876_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_877_ = crate::leanh::lean_ctor_get(v_x_863_, 0);
                    v_map_u2082_878_ = crate::leanh::lean_ctor_get(v_x_863_, 1);
                    v_isSharedCheck_886_ = (!crate::leanh::lean_is_exclusive(v_x_863_)) as u8;
                    if v_isSharedCheck_886_ == 0 {
                        v___x_880_ = v_x_863_;
                        v_isShared_881_ = v_isSharedCheck_886_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_u2082_878_);
                        crate::leanh::lean_inc(v_map_u2081_877_);
                        crate::leanh::lean_dec(v_x_863_);
                        v___x_880_ = crate::leanh::lean_box(0);
                        v_isShared_881_ = v_isSharedCheck_886_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_872_ = l_Lean_PersistentHashMap_insert___redArg(
                    v_inst_861_,
                    v_inst_862_,
                    v_map_u2082_868_,
                    v_x_864_,
                    v_x_865_,
                );
                if v_isShared_871_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_870_, 1, v___x_872_);
                    v___x_874_ = v___x_870_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_875_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_875_, 0, v_map_u2081_867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_872_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_875_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_866_,
                    );
                    v___x_874_ = v_reuseFailAlloc_875_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_874_;
            }
            3 => {
                v___x_882_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v_inst_861_,
                    v_inst_862_,
                    v_map_u2081_877_,
                    v_x_864_,
                    v_x_865_,
                );
                if v_isShared_881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_880_, 0, v___x_882_);
                    v___x_884_ = v___x_880_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_885_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 1, v_map_u2082_878_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_885_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_866_,
                    );
                    v___x_884_ = v_reuseFailAlloc_885_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_insert_x27(
    mut v_00_u03b1_887_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_888_: *mut crate::leanh::LeanObject,
    mut v_inst_889_: *mut crate::leanh::LeanObject,
    mut v_inst_890_: *mut crate::leanh::LeanObject,
    mut v_x_891_: *mut crate::leanh::LeanObject,
    mut v_x_892_: *mut crate::leanh::LeanObject,
    mut v_x_893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_894_ =
        l_Lean_SMap_insert_x27___redArg(v_inst_889_, v_inst_890_, v_x_891_, v_x_892_, v_x_893_);
    return v___x_894_;
}
pub unsafe fn l_Lean_SMap_find_x3f___redArg(
    mut v_inst_895_: *mut crate::leanh::LeanObject,
    mut v_inst_896_: *mut crate::leanh::LeanObject,
    mut v_x_897_: *mut crate::leanh::LeanObject,
    mut v_x_898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_899_: u8 = 0;
    v_stage_u2081_899_ = crate::leanh::lean_ctor_get_uint8(
        v_x_897_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_899_ == 0 {
        let mut v_map_u2081_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_900_ = crate::leanh::lean_ctor_get(v_x_897_, 0);
        v_map_u2082_901_ = crate::leanh::lean_ctor_get(v_x_897_, 1);
        crate::leanh::lean_inc(v_x_898_);
        crate::leanh::lean_inc_ref(v_inst_896_);
        crate::leanh::lean_inc_ref(v_inst_895_);
        v___x_902_ = l_Lean_PersistentHashMap_find_x3f___redArg(
            v_inst_895_,
            v_inst_896_,
            v_map_u2082_901_,
            v_x_898_,
        );
        if crate::leanh::lean_obj_tag(v___x_902_) == 0 {
            let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                v_inst_895_,
                v_inst_896_,
                v_map_u2081_900_,
                v_x_898_,
            );
            return v___x_903_;
        } else {
            crate::leanh::lean_dec(v_x_898_);
            crate::leanh::lean_dec_ref(v_inst_896_);
            crate::leanh::lean_dec_ref(v_inst_895_);
            return v___x_902_;
        }
    } else {
        let mut v_map_u2081_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_904_ = crate::leanh::lean_ctor_get(v_x_897_, 0);
        v___x_905_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
            v_inst_895_,
            v_inst_896_,
            v_map_u2081_904_,
            v_x_898_,
        );
        return v___x_905_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___redArg___boxed(
    mut v_inst_906_: *mut crate::leanh::LeanObject,
    mut v_inst_907_: *mut crate::leanh::LeanObject,
    mut v_x_908_: *mut crate::leanh::LeanObject,
    mut v_x_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_910_ = l_Lean_SMap_find_x3f___redArg(v_inst_906_, v_inst_907_, v_x_908_, v_x_909_);
    crate::leanh::lean_dec_ref(v_x_908_);
    return v_res_910_;
}
pub unsafe fn l_Lean_SMap_find_x3f(
    mut v_00_u03b1_911_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_912_: *mut crate::leanh::LeanObject,
    mut v_inst_913_: *mut crate::leanh::LeanObject,
    mut v_inst_914_: *mut crate::leanh::LeanObject,
    mut v_x_915_: *mut crate::leanh::LeanObject,
    mut v_x_916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_917_ = l_Lean_SMap_find_x3f___redArg(v_inst_913_, v_inst_914_, v_x_915_, v_x_916_);
    return v___x_917_;
}
pub unsafe fn l_Lean_SMap_find_x3f___boxed(
    mut v_00_u03b1_918_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_919_: *mut crate::leanh::LeanObject,
    mut v_inst_920_: *mut crate::leanh::LeanObject,
    mut v_inst_921_: *mut crate::leanh::LeanObject,
    mut v_x_922_: *mut crate::leanh::LeanObject,
    mut v_x_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_924_ = l_Lean_SMap_find_x3f(
        v_00_u03b1_918_,
        v_00_u03b2_919_,
        v_inst_920_,
        v_inst_921_,
        v_x_922_,
        v_x_923_,
    );
    crate::leanh::lean_dec_ref(v_x_922_);
    return v_res_924_;
}
pub unsafe fn l_Lean_SMap_findD___redArg(
    mut v_inst_925_: *mut crate::leanh::LeanObject,
    mut v_inst_926_: *mut crate::leanh::LeanObject,
    mut v_m_927_: *mut crate::leanh::LeanObject,
    mut v_a_928_: *mut crate::leanh::LeanObject,
    mut v_b_u2080_929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_930_ = l_Lean_SMap_find_x3f___redArg(v_inst_925_, v_inst_926_, v_m_927_, v_a_928_);
    if crate::leanh::lean_obj_tag(v___x_930_) == 0 {
        crate::leanh::lean_inc(v_b_u2080_929_);
        return v_b_u2080_929_;
    } else {
        let mut v_val_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_931_ = crate::leanh::lean_ctor_get(v___x_930_, 0);
        crate::leanh::lean_inc(v_val_931_);
        crate::leanh::lean_dec_ref_known(v___x_930_, 1);
        return v_val_931_;
    }
}
pub unsafe fn l_Lean_SMap_findD___redArg___boxed(
    mut v_inst_932_: *mut crate::leanh::LeanObject,
    mut v_inst_933_: *mut crate::leanh::LeanObject,
    mut v_m_934_: *mut crate::leanh::LeanObject,
    mut v_a_935_: *mut crate::leanh::LeanObject,
    mut v_b_u2080_936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_937_ =
        l_Lean_SMap_findD___redArg(v_inst_932_, v_inst_933_, v_m_934_, v_a_935_, v_b_u2080_936_);
    crate::leanh::lean_dec(v_b_u2080_936_);
    crate::leanh::lean_dec_ref(v_m_934_);
    return v_res_937_;
}
pub unsafe fn l_Lean_SMap_findD(
    mut v_00_u03b1_938_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_939_: *mut crate::leanh::LeanObject,
    mut v_inst_940_: *mut crate::leanh::LeanObject,
    mut v_inst_941_: *mut crate::leanh::LeanObject,
    mut v_m_942_: *mut crate::leanh::LeanObject,
    mut v_a_943_: *mut crate::leanh::LeanObject,
    mut v_b_u2080_944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_945_ = l_Lean_SMap_find_x3f___redArg(v_inst_940_, v_inst_941_, v_m_942_, v_a_943_);
    if crate::leanh::lean_obj_tag(v___x_945_) == 0 {
        crate::leanh::lean_inc(v_b_u2080_944_);
        return v_b_u2080_944_;
    } else {
        let mut v_val_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_946_ = crate::leanh::lean_ctor_get(v___x_945_, 0);
        crate::leanh::lean_inc(v_val_946_);
        crate::leanh::lean_dec_ref_known(v___x_945_, 1);
        return v_val_946_;
    }
}
pub unsafe fn l_Lean_SMap_findD___boxed(
    mut v_00_u03b1_947_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_948_: *mut crate::leanh::LeanObject,
    mut v_inst_949_: *mut crate::leanh::LeanObject,
    mut v_inst_950_: *mut crate::leanh::LeanObject,
    mut v_m_951_: *mut crate::leanh::LeanObject,
    mut v_a_952_: *mut crate::leanh::LeanObject,
    mut v_b_u2080_953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_954_ = l_Lean_SMap_findD(
        v_00_u03b1_947_,
        v_00_u03b2_948_,
        v_inst_949_,
        v_inst_950_,
        v_m_951_,
        v_a_952_,
        v_b_u2080_953_,
    );
    crate::leanh::lean_dec(v_b_u2080_953_);
    crate::leanh::lean_dec_ref(v_m_951_);
    return v_res_954_;
}
pub unsafe fn _init_l_Lean_SMap_find_x21___redArg___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_958_ = l_Lean_SMap_find_x21___redArg___closed__2;
    v___x_959_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_960_ = crate::leanh::lean_unsigned_to_nat(70);
    v___x_961_ = l_Lean_SMap_find_x21___redArg___closed__1;
    v___x_962_ = l_Lean_SMap_find_x21___redArg___closed__0;
    v___x_963_ =
        l_mkPanicMessageWithDecl(v___x_962_, v___x_961_, v___x_960_, v___x_959_, v___x_958_);
    return v___x_963_;
}
pub unsafe fn l_Lean_SMap_find_x21___redArg(
    mut v_inst_964_: *mut crate::leanh::LeanObject,
    mut v_inst_965_: *mut crate::leanh::LeanObject,
    mut v_inst_966_: *mut crate::leanh::LeanObject,
    mut v_m_967_: *mut crate::leanh::LeanObject,
    mut v_a_968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_969_ = l_Lean_SMap_find_x3f___redArg(v_inst_964_, v_inst_965_, v_m_967_, v_a_968_);
    if crate::leanh::lean_obj_tag(v___x_969_) == 0 {
        let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_970_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_SMap_find_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Lean_SMap_find_x21___redArg___closed__3_once),
            _init_l_Lean_SMap_find_x21___redArg___closed__3,
        );
        v___x_971_ = l_panic___redArg(v_inst_966_, v___x_970_);
        return v___x_971_;
    } else {
        let mut v_val_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_972_ = crate::leanh::lean_ctor_get(v___x_969_, 0);
        crate::leanh::lean_inc(v_val_972_);
        crate::leanh::lean_dec_ref_known(v___x_969_, 1);
        return v_val_972_;
    }
}
pub unsafe fn l_Lean_SMap_find_x21___redArg___boxed(
    mut v_inst_973_: *mut crate::leanh::LeanObject,
    mut v_inst_974_: *mut crate::leanh::LeanObject,
    mut v_inst_975_: *mut crate::leanh::LeanObject,
    mut v_m_976_: *mut crate::leanh::LeanObject,
    mut v_a_977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_978_ =
        l_Lean_SMap_find_x21___redArg(v_inst_973_, v_inst_974_, v_inst_975_, v_m_976_, v_a_977_);
    crate::leanh::lean_dec_ref(v_m_976_);
    crate::leanh::lean_dec(v_inst_975_);
    return v_res_978_;
}
pub unsafe fn l_Lean_SMap_find_x21(
    mut v_00_u03b1_979_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_980_: *mut crate::leanh::LeanObject,
    mut v_inst_981_: *mut crate::leanh::LeanObject,
    mut v_inst_982_: *mut crate::leanh::LeanObject,
    mut v_inst_983_: *mut crate::leanh::LeanObject,
    mut v_m_984_: *mut crate::leanh::LeanObject,
    mut v_a_985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_986_ = l_Lean_SMap_find_x3f___redArg(v_inst_981_, v_inst_982_, v_m_984_, v_a_985_);
    if crate::leanh::lean_obj_tag(v___x_986_) == 0 {
        let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_987_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_SMap_find_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Lean_SMap_find_x21___redArg___closed__3_once),
            _init_l_Lean_SMap_find_x21___redArg___closed__3,
        );
        v___x_988_ = l_panic___redArg(v_inst_983_, v___x_987_);
        return v___x_988_;
    } else {
        let mut v_val_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_989_ = crate::leanh::lean_ctor_get(v___x_986_, 0);
        crate::leanh::lean_inc(v_val_989_);
        crate::leanh::lean_dec_ref_known(v___x_986_, 1);
        return v_val_989_;
    }
}
pub unsafe fn l_Lean_SMap_find_x21___boxed(
    mut v_00_u03b1_990_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_991_: *mut crate::leanh::LeanObject,
    mut v_inst_992_: *mut crate::leanh::LeanObject,
    mut v_inst_993_: *mut crate::leanh::LeanObject,
    mut v_inst_994_: *mut crate::leanh::LeanObject,
    mut v_m_995_: *mut crate::leanh::LeanObject,
    mut v_a_996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_997_ = l_Lean_SMap_find_x21(
        v_00_u03b1_990_,
        v_00_u03b2_991_,
        v_inst_992_,
        v_inst_993_,
        v_inst_994_,
        v_m_995_,
        v_a_996_,
    );
    crate::leanh::lean_dec_ref(v_m_995_);
    crate::leanh::lean_dec(v_inst_994_);
    return v_res_997_;
}
pub unsafe fn l_Lean_SMap_contains___redArg(
    mut v_inst_998_: *mut crate::leanh::LeanObject,
    mut v_inst_999_: *mut crate::leanh::LeanObject,
    mut v_x_1000_: *mut crate::leanh::LeanObject,
    mut v_x_1001_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_stage_u2081_1002_: u8 = 0;
    v_stage_u2081_1002_ = crate::leanh::lean_ctor_get_uint8(
        v_x_1000_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_1002_ == 0 {
        let mut v_map_u2081_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1005_: u8 = 0;
        v_map_u2081_1003_ = crate::leanh::lean_ctor_get(v_x_1000_, 0);
        crate::leanh::lean_inc_ref(v_map_u2081_1003_);
        v_map_u2082_1004_ = crate::leanh::lean_ctor_get(v_x_1000_, 1);
        crate::leanh::lean_inc_ref(v_map_u2082_1004_);
        crate::leanh::lean_dec_ref(v_x_1000_);
        crate::leanh::lean_inc(v_x_1001_);
        crate::leanh::lean_inc_ref(v_inst_999_);
        crate::leanh::lean_inc_ref(v_inst_998_);
        v___x_1005_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v_inst_998_,
            v_inst_999_,
            v_map_u2081_1003_,
            v_x_1001_,
        );
        crate::leanh::lean_dec_ref(v_map_u2081_1003_);
        if v___x_1005_ == 0 {
            let mut v___x_1006_: u8 = 0;
            v___x_1006_ = l_Lean_PersistentHashMap_contains___redArg(
                v_inst_998_,
                v_inst_999_,
                v_map_u2082_1004_,
                v_x_1001_,
            );
            return v___x_1006_;
        } else {
            crate::leanh::lean_dec_ref(v_map_u2082_1004_);
            crate::leanh::lean_dec(v_x_1001_);
            crate::leanh::lean_dec_ref(v_inst_999_);
            crate::leanh::lean_dec_ref(v_inst_998_);
            return v___x_1005_;
        }
    } else {
        let mut v_map_u2081_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1008_: u8 = 0;
        v_map_u2081_1007_ = crate::leanh::lean_ctor_get(v_x_1000_, 0);
        crate::leanh::lean_inc_ref(v_map_u2081_1007_);
        crate::leanh::lean_dec_ref(v_x_1000_);
        v___x_1008_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v_inst_998_,
            v_inst_999_,
            v_map_u2081_1007_,
            v_x_1001_,
        );
        crate::leanh::lean_dec_ref(v_map_u2081_1007_);
        return v___x_1008_;
    }
}
pub unsafe fn l_Lean_SMap_contains___redArg___boxed(
    mut v_inst_1009_: *mut crate::leanh::LeanObject,
    mut v_inst_1010_: *mut crate::leanh::LeanObject,
    mut v_x_1011_: *mut crate::leanh::LeanObject,
    mut v_x_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1013_: u8 = 0;
    let mut v_r_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Lean_SMap_contains___redArg(v_inst_1009_, v_inst_1010_, v_x_1011_, v_x_1012_);
    v_r_1014_ = crate::leanh::lean_box((v_res_1013_) as usize);
    return v_r_1014_;
}
pub unsafe fn l_Lean_SMap_contains(
    mut v_00_u03b1_1015_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1016_: *mut crate::leanh::LeanObject,
    mut v_inst_1017_: *mut crate::leanh::LeanObject,
    mut v_inst_1018_: *mut crate::leanh::LeanObject,
    mut v_x_1019_: *mut crate::leanh::LeanObject,
    mut v_x_1020_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1021_: u8 = 0;
    v___x_1021_ = l_Lean_SMap_contains___redArg(v_inst_1017_, v_inst_1018_, v_x_1019_, v_x_1020_);
    return v___x_1021_;
}
pub unsafe fn l_Lean_SMap_contains___boxed(
    mut v_00_u03b1_1022_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1023_: *mut crate::leanh::LeanObject,
    mut v_inst_1024_: *mut crate::leanh::LeanObject,
    mut v_inst_1025_: *mut crate::leanh::LeanObject,
    mut v_x_1026_: *mut crate::leanh::LeanObject,
    mut v_x_1027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1028_: u8 = 0;
    let mut v_r_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1028_ = l_Lean_SMap_contains(
        v_00_u03b1_1022_,
        v_00_u03b2_1023_,
        v_inst_1024_,
        v_inst_1025_,
        v_x_1026_,
        v_x_1027_,
    );
    v_r_1029_ = crate::leanh::lean_box((v_res_1028_) as usize);
    return v_r_1029_;
}
pub unsafe fn l_Lean_SMap_find_x3f_x27___redArg(
    mut v_inst_1030_: *mut crate::leanh::LeanObject,
    mut v_inst_1031_: *mut crate::leanh::LeanObject,
    mut v_x_1032_: *mut crate::leanh::LeanObject,
    mut v_x_1033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_1034_: u8 = 0;
    v_stage_u2081_1034_ = crate::leanh::lean_ctor_get_uint8(
        v_x_1032_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_1034_ == 0 {
        let mut v_map_u2081_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_1035_ = crate::leanh::lean_ctor_get(v_x_1032_, 0);
        v_map_u2082_1036_ = crate::leanh::lean_ctor_get(v_x_1032_, 1);
        crate::leanh::lean_inc(v_x_1033_);
        crate::leanh::lean_inc_ref(v_inst_1031_);
        crate::leanh::lean_inc_ref(v_inst_1030_);
        v___x_1037_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
            v_inst_1030_,
            v_inst_1031_,
            v_map_u2081_1035_,
            v_x_1033_,
        );
        if crate::leanh::lean_obj_tag(v___x_1037_) == 0 {
            let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1038_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                v_inst_1030_,
                v_inst_1031_,
                v_map_u2082_1036_,
                v_x_1033_,
            );
            return v___x_1038_;
        } else {
            crate::leanh::lean_dec(v_x_1033_);
            crate::leanh::lean_dec_ref(v_inst_1031_);
            crate::leanh::lean_dec_ref(v_inst_1030_);
            return v___x_1037_;
        }
    } else {
        let mut v_map_u2081_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_1039_ = crate::leanh::lean_ctor_get(v_x_1032_, 0);
        v___x_1040_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
            v_inst_1030_,
            v_inst_1031_,
            v_map_u2081_1039_,
            v_x_1033_,
        );
        return v___x_1040_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f_x27___redArg___boxed(
    mut v_inst_1041_: *mut crate::leanh::LeanObject,
    mut v_inst_1042_: *mut crate::leanh::LeanObject,
    mut v_x_1043_: *mut crate::leanh::LeanObject,
    mut v_x_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1045_ =
        l_Lean_SMap_find_x3f_x27___redArg(v_inst_1041_, v_inst_1042_, v_x_1043_, v_x_1044_);
    crate::leanh::lean_dec_ref(v_x_1043_);
    return v_res_1045_;
}
pub unsafe fn l_Lean_SMap_find_x3f_x27(
    mut v_00_u03b1_1046_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1047_: *mut crate::leanh::LeanObject,
    mut v_inst_1048_: *mut crate::leanh::LeanObject,
    mut v_inst_1049_: *mut crate::leanh::LeanObject,
    mut v_x_1050_: *mut crate::leanh::LeanObject,
    mut v_x_1051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1052_ =
        l_Lean_SMap_find_x3f_x27___redArg(v_inst_1048_, v_inst_1049_, v_x_1050_, v_x_1051_);
    return v___x_1052_;
}
pub unsafe fn l_Lean_SMap_find_x3f_x27___boxed(
    mut v_00_u03b1_1053_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1054_: *mut crate::leanh::LeanObject,
    mut v_inst_1055_: *mut crate::leanh::LeanObject,
    mut v_inst_1056_: *mut crate::leanh::LeanObject,
    mut v_x_1057_: *mut crate::leanh::LeanObject,
    mut v_x_1058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1059_ = l_Lean_SMap_find_x3f_x27(
        v_00_u03b1_1053_,
        v_00_u03b2_1054_,
        v_inst_1055_,
        v_inst_1056_,
        v_x_1057_,
        v_x_1058_,
    );
    crate::leanh::lean_dec_ref(v_x_1057_);
    return v_res_1059_;
}
pub unsafe fn l_Lean_SMap_forM___redArg___lam__0(
    mut v_inst_1060_: *mut crate::leanh::LeanObject,
    mut v_map_u2082_1061_: *mut crate::leanh::LeanObject,
    mut v_f_1062_: *mut crate::leanh::LeanObject,
    mut v_____r_1063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ =
        l_Lean_PersistentHashMap_forM___redArg(v_inst_1060_, v_map_u2082_1061_, v_f_1062_);
    return v___x_1064_;
}
pub unsafe fn l_Lean_SMap_forM___redArg___lam__1(
    mut v_f_1065_: *mut crate::leanh::LeanObject,
    mut v_x_1066_: *mut crate::leanh::LeanObject,
    mut v___y_1067_: *mut crate::leanh::LeanObject,
    mut v___y_1068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1069_ = crate::leanh::lean_apply_2(v_f_1065_, v___y_1067_, v___y_1068_);
    return v___x_1069_;
}
pub unsafe fn l_Lean_SMap_forM___redArg___lam__2(
    mut v_inst_1070_: *mut crate::leanh::LeanObject,
    mut v___f_1071_: *mut crate::leanh::LeanObject,
    mut v_x_1072_: *mut crate::leanh::LeanObject,
    mut v___y_1073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ = crate::leanh::lean_box(0);
    v___x_1075_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1070_,
        v___f_1071_,
        v___x_1074_,
        v___y_1073_,
    );
    return v___x_1075_;
}
pub unsafe fn l_Lean_SMap_forM___redArg(
    mut v_inst_1076_: *mut crate::leanh::LeanObject,
    mut v_s_1077_: *mut crate::leanh::LeanObject,
    mut v_f_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_u2081_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: u8 = 0;
    v_map_u2081_1079_ = crate::leanh::lean_ctor_get(v_s_1077_, 0);
    crate::leanh::lean_inc_ref(v_map_u2081_1079_);
    v_toApplicative_1080_ = crate::leanh::lean_ctor_get(v_inst_1076_, 0);
    v_toBind_1081_ = crate::leanh::lean_ctor_get(v_inst_1076_, 1);
    crate::leanh::lean_inc(v_toBind_1081_);
    v_map_u2082_1082_ = crate::leanh::lean_ctor_get(v_s_1077_, 1);
    crate::leanh::lean_inc_ref(v_map_u2082_1082_);
    crate::leanh::lean_dec_ref(v_s_1077_);
    v_buckets_1083_ = crate::leanh::lean_ctor_get(v_map_u2081_1079_, 1);
    crate::leanh::lean_inc_ref(v_buckets_1083_);
    crate::leanh::lean_dec_ref(v_map_u2081_1079_);
    crate::leanh::lean_inc(v_f_1078_);
    crate::leanh::lean_inc_ref(v_inst_1076_);
    v___f_1084_ = crate::leanh::lean_alloc_closure(
        l_Lean_SMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1084_, 0, v_inst_1076_);
    crate::leanh::lean_closure_set(v___f_1084_, 1, v_map_u2082_1082_);
    crate::leanh::lean_closure_set(v___f_1084_, 2, v_f_1078_);
    v___x_1085_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1086_ = lean_array_get_size(v_buckets_1083_);
    v___x_1087_ = crate::leanh::lean_box(0);
    v___x_1088_ = lean_nat_dec_lt(v___x_1085_, v___x_1086_);
    if v___x_1088_ == 0 {
        let mut v_toPure_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_toApplicative_1080_);
        crate::leanh::lean_dec_ref(v_buckets_1083_);
        crate::leanh::lean_dec(v_f_1078_);
        crate::leanh::lean_dec_ref(v_inst_1076_);
        v_toPure_1089_ = crate::leanh::lean_ctor_get(v_toApplicative_1080_, 1);
        crate::leanh::lean_inc(v_toPure_1089_);
        crate::leanh::lean_dec_ref(v_toApplicative_1080_);
        v___x_1090_ =
            crate::leanh::lean_apply_2(v_toPure_1089_, crate::leanh::lean_box(0), v___x_1087_);
        v___x_1091_ = crate::leanh::lean_apply_4(
            v_toBind_1081_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1090_,
            v___f_1084_,
        );
        return v___x_1091_;
    } else {
        let mut v___f_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1094_: u8 = 0;
        v___f_1092_ = crate::leanh::lean_alloc_closure(
            l_Lean_SMap_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1092_, 0, v_f_1078_);
        crate::leanh::lean_inc_ref(v_inst_1076_);
        v___f_1093_ = crate::leanh::lean_alloc_closure(
            l_Lean_SMap_forM___redArg___lam__2 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_1093_, 0, v_inst_1076_);
        crate::leanh::lean_closure_set(v___f_1093_, 1, v___f_1092_);
        v___x_1094_ = lean_nat_dec_le(v___x_1086_, v___x_1086_);
        if v___x_1094_ == 0 {
            if v___x_1088_ == 0 {
                let mut v_toPure_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc_ref(v_toApplicative_1080_);
                crate::leanh::lean_dec_ref(v___f_1093_);
                crate::leanh::lean_dec_ref(v_buckets_1083_);
                crate::leanh::lean_dec_ref(v_inst_1076_);
                v_toPure_1095_ = crate::leanh::lean_ctor_get(v_toApplicative_1080_, 1);
                crate::leanh::lean_inc(v_toPure_1095_);
                crate::leanh::lean_dec_ref(v_toApplicative_1080_);
                v___x_1096_ = crate::leanh::lean_apply_2(
                    v_toPure_1095_,
                    crate::leanh::lean_box(0),
                    v___x_1087_,
                );
                v___x_1097_ = crate::leanh::lean_apply_4(
                    v_toBind_1081_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1096_,
                    v___f_1084_,
                );
                return v___x_1097_;
            } else {
                let mut v___x_1098_: usize = 0;
                let mut v___x_1099_: usize = 0;
                let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1098_ = 0usize;
                v___x_1099_ = lean_usize_of_nat(v___x_1086_);
                v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_1076_,
                    v___f_1093_,
                    v_buckets_1083_,
                    v___x_1098_,
                    v___x_1099_,
                    v___x_1087_,
                );
                v___x_1101_ = crate::leanh::lean_apply_4(
                    v_toBind_1081_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1100_,
                    v___f_1084_,
                );
                return v___x_1101_;
            }
        } else {
            let mut v___x_1102_: usize = 0;
            let mut v___x_1103_: usize = 0;
            let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1102_ = 0usize;
            v___x_1103_ = lean_usize_of_nat(v___x_1086_);
            v___x_1104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_1076_,
                v___f_1093_,
                v_buckets_1083_,
                v___x_1102_,
                v___x_1103_,
                v___x_1087_,
            );
            v___x_1105_ = crate::leanh::lean_apply_4(
                v_toBind_1081_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1104_,
                v___f_1084_,
            );
            return v___x_1105_;
        }
    }
}
pub unsafe fn l_Lean_SMap_forM(
    mut v_00_u03b1_1106_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1107_: *mut crate::leanh::LeanObject,
    mut v_inst_1108_: *mut crate::leanh::LeanObject,
    mut v_inst_1109_: *mut crate::leanh::LeanObject,
    mut v_m_1110_: *mut crate::leanh::LeanObject,
    mut v_inst_1111_: *mut crate::leanh::LeanObject,
    mut v_s_1112_: *mut crate::leanh::LeanObject,
    mut v_f_1113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1114_ = l_Lean_SMap_forM___redArg(v_inst_1111_, v_s_1112_, v_f_1113_);
    return v___x_1114_;
}
pub unsafe fn l_Lean_SMap_forM___boxed(
    mut v_00_u03b1_1115_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1116_: *mut crate::leanh::LeanObject,
    mut v_inst_1117_: *mut crate::leanh::LeanObject,
    mut v_inst_1118_: *mut crate::leanh::LeanObject,
    mut v_m_1119_: *mut crate::leanh::LeanObject,
    mut v_inst_1120_: *mut crate::leanh::LeanObject,
    mut v_s_1121_: *mut crate::leanh::LeanObject,
    mut v_f_1122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1123_ = l_Lean_SMap_forM(
        v_00_u03b1_1115_,
        v_00_u03b2_1116_,
        v_inst_1117_,
        v_inst_1118_,
        v_m_1119_,
        v_inst_1120_,
        v_s_1121_,
        v_f_1122_,
    );
    crate::leanh::lean_dec_ref(v_inst_1118_);
    crate::leanh::lean_dec_ref(v_inst_1117_);
    return v_res_1123_;
}
pub unsafe fn l_Lean_SMap_instForMProdOfMonad___redArg___lam__0(
    mut v_f_1124_: *mut crate::leanh::LeanObject,
    mut v_x_1125_: *mut crate::leanh::LeanObject,
    mut v_y_1126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1127_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1127_, 0, v_x_1125_);
    crate::leanh::lean_ctor_set(v___x_1127_, 1, v_y_1126_);
    v___x_1128_ = crate::leanh::lean_apply_1(v_f_1124_, v___x_1127_);
    return v___x_1128_;
}
pub unsafe fn l_Lean_SMap_instForMProdOfMonad___redArg___lam__1(
    mut v_inst_1129_: *mut crate::leanh::LeanObject,
    mut v_s_1130_: *mut crate::leanh::LeanObject,
    mut v_f_1131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1132_ = crate::leanh::lean_alloc_closure(
        l_Lean_SMap_instForMProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1132_, 0, v_f_1131_);
    v___x_1133_ = l_Lean_SMap_forM___redArg(v_inst_1129_, v_s_1130_, v___f_1132_);
    return v___x_1133_;
}
pub unsafe fn l_Lean_SMap_instForMProdOfMonad___redArg(
    mut v_inst_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1135_ = crate::leanh::lean_alloc_closure(
        l_Lean_SMap_instForMProdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1135_, 0, v_inst_1134_);
    return v___f_1135_;
}
pub unsafe fn l_Lean_SMap_instForMProdOfMonad(
    mut v_00_u03b1_1136_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1137_: *mut crate::leanh::LeanObject,
    mut v_inst_1138_: *mut crate::leanh::LeanObject,
    mut v_inst_1139_: *mut crate::leanh::LeanObject,
    mut v_m_1140_: *mut crate::leanh::LeanObject,
    mut v_inst_1141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1142_ = crate::leanh::lean_alloc_closure(
        l_Lean_SMap_instForMProdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1142_, 0, v_inst_1141_);
    return v___f_1142_;
}
pub unsafe fn l_Lean_SMap_instForMProdOfMonad___boxed(
    mut v_00_u03b1_1143_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1144_: *mut crate::leanh::LeanObject,
    mut v_inst_1145_: *mut crate::leanh::LeanObject,
    mut v_inst_1146_: *mut crate::leanh::LeanObject,
    mut v_m_1147_: *mut crate::leanh::LeanObject,
    mut v_inst_1148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1149_ = l_Lean_SMap_instForMProdOfMonad(
        v_00_u03b1_1143_,
        v_00_u03b2_1144_,
        v_inst_1145_,
        v_inst_1146_,
        v_m_1147_,
        v_inst_1148_,
    );
    crate::leanh::lean_dec_ref(v_inst_1146_);
    crate::leanh::lean_dec_ref(v_inst_1145_);
    return v_res_1149_;
}
pub unsafe fn l_Lean_SMap_instForInProdOfMonad___redArg___lam__0(
    mut v_toPure_1150_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1151_) == 0 {
        let mut v_a_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1152_ = crate::leanh::lean_ctor_get(v_____do__lift_1151_, 0);
        crate::leanh::lean_inc(v_a_1152_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1151_, 1);
        v___x_1153_ =
            crate::leanh::lean_apply_2(v_toPure_1150_, crate::leanh::lean_box(0), v_a_1152_);
        return v___x_1153_;
    } else {
        let mut v_a_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1154_ = crate::leanh::lean_ctor_get(v_____do__lift_1151_, 0);
        crate::leanh::lean_inc(v_a_1154_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1151_, 1);
        v_snd_1155_ = crate::leanh::lean_ctor_get(v_a_1154_, 1);
        crate::leanh::lean_inc(v_snd_1155_);
        crate::leanh::lean_dec(v_a_1154_);
        v___x_1156_ =
            crate::leanh::lean_apply_2(v_toPure_1150_, crate::leanh::lean_box(0), v_snd_1155_);
        return v___x_1156_;
    }
}
pub unsafe fn l_Lean_SMap_instForInProdOfMonad___redArg___lam__1(
    mut v_toPure_1157_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1162_: u8 = 0;
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1167_: u8 = 0;
    let mut v_a_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1171_: u8 = 0;
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_1158_) == 0 {
                    v_a_1159_ = crate::leanh::lean_ctor_get(v_____do__lift_1158_, 0);
                    v_isSharedCheck_1167_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_1158_)) as u8;
                    if v_isSharedCheck_1167_ == 0 {
                        v___x_1161_ = v_____do__lift_1158_;
                        v_isShared_1162_ = v_isSharedCheck_1167_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1159_);
                        crate::leanh::lean_dec(v_____do__lift_1158_);
                        v___x_1161_ = crate::leanh::lean_box(0);
                        v_isShared_1162_ = v_isSharedCheck_1167_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1168_ = crate::leanh::lean_ctor_get(v_____do__lift_1158_, 0);
                    v_isSharedCheck_1178_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_1158_)) as u8;
                    if v_isSharedCheck_1178_ == 0 {
                        v___x_1170_ = v_____do__lift_1158_;
                        v_isShared_1171_ = v_isSharedCheck_1178_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1168_);
                        crate::leanh::lean_dec(v_____do__lift_1158_);
                        v___x_1170_ = crate::leanh::lean_box(0);
                        v_isShared_1171_ = v_isSharedCheck_1178_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1162_ == 0 {
                    v___x_1164_ = v___x_1161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1166_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1159_);
                    v___x_1164_ = v_reuseFailAlloc_1166_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1165_ = crate::leanh::lean_apply_2(
                    v_toPure_1157_,
                    crate::leanh::lean_box(0),
                    v___x_1164_,
                );
                return v___x_1165_;
            }
            3 => {
                v___x_1172_ = crate::leanh::lean_box(0);
                v___x_1173_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1173_, 0, v___x_1172_);
                crate::leanh::lean_ctor_set(v___x_1173_, 1, v_a_1168_);
                if v_isShared_1171_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1170_, 0, v___x_1173_);
                    v___x_1175_ = v___x_1170_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1173_);
                    v___x_1175_ = v_reuseFailAlloc_1177_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1176_ = crate::leanh::lean_apply_2(
                    v_toPure_1157_,
                    crate::leanh::lean_box(0),
                    v___x_1175_,
                );
                return v___x_1176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_instForInProdOfMonad___redArg___lam__2(
    mut v___y_1179_: *mut crate::leanh::LeanObject,
    mut v_toBind_1180_: *mut crate::leanh::LeanObject,
    mut v___f_1181_: *mut crate::leanh::LeanObject,
    mut v_x_1182_: *mut crate::leanh::LeanObject,
    mut v_y_1183_: *mut crate::leanh::LeanObject,
    mut v___y_1184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1185_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1185_, 0, v_x_1182_);
    crate::leanh::lean_ctor_set(v___x_1185_, 1, v_y_1183_);
    v___x_1186_ = crate::leanh::lean_apply_2(v___y_1179_, v___x_1185_, v___y_1184_);
    v___x_1187_ = crate::leanh::lean_apply_4(
        v_toBind_1180_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1186_,
        v___f_1181_,
    );
    return v___x_1187_;
}
pub unsafe fn l_Lean_SMap_instForInProdOfMonad___redArg___lam__3(
    mut v_inst_1188_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1189_: *mut crate::leanh::LeanObject,
    mut v___y_1190_: *mut crate::leanh::LeanObject,
    mut v___y_1191_: *mut crate::leanh::LeanObject,
    mut v___y_1192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140__overap_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_1188_, 7);
    v___f_1193_ = crate::leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1193_, 0, v_inst_1188_);
    v___f_1194_ = crate::leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1194_, 0, v_inst_1188_);
    v___f_1195_ = crate::leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1195_, 0, v_inst_1188_);
    v___f_1196_ = crate::leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1196_, 0, v_inst_1188_);
    v___x_1197_ = crate::leanh::lean_alloc_closure(l_ExceptT_map as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___x_1197_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1197_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1197_, 2, v_inst_1188_);
    v___x_1198_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1198_, 0, v___x_1197_);
    crate::leanh::lean_ctor_set(v___x_1198_, 1, v___f_1193_);
    v___x_1199_ = crate::leanh::lean_alloc_closure(l_ExceptT_pure as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_1199_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1199_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1199_, 2, v_inst_1188_);
    v___x_1200_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1200_, 0, v___x_1198_);
    crate::leanh::lean_ctor_set(v___x_1200_, 1, v___x_1199_);
    crate::leanh::lean_ctor_set(v___x_1200_, 2, v___f_1194_);
    crate::leanh::lean_ctor_set(v___x_1200_, 3, v___f_1195_);
    crate::leanh::lean_ctor_set(v___x_1200_, 4, v___f_1196_);
    v___x_1201_ = crate::leanh::lean_alloc_closure(l_ExceptT_bind as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___x_1201_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1201_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1201_, 2, v_inst_1188_);
    v___x_1202_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1202_, 0, v___x_1200_);
    crate::leanh::lean_ctor_set(v___x_1202_, 1, v___x_1201_);
    crate::leanh::lean_inc_ref_n(v___x_1202_, 6);
    v___f_1203_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1203_, 0, v___x_1202_);
    v___f_1204_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1204_, 0, v___x_1202_);
    v___f_1205_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1205_, 0, v___x_1202_);
    v___f_1206_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1206_, 0, v___x_1202_);
    v___x_1207_ = crate::leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1207_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1207_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1207_, 2, v___x_1202_);
    v___x_1208_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1208_, 0, v___x_1207_);
    crate::leanh::lean_ctor_set(v___x_1208_, 1, v___f_1203_);
    v___x_1209_ = crate::leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_1209_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1209_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1209_, 2, v___x_1202_);
    v___x_1210_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1210_, 0, v___x_1208_);
    crate::leanh::lean_ctor_set(v___x_1210_, 1, v___x_1209_);
    crate::leanh::lean_ctor_set(v___x_1210_, 2, v___f_1204_);
    crate::leanh::lean_ctor_set(v___x_1210_, 3, v___f_1205_);
    crate::leanh::lean_ctor_set(v___x_1210_, 4, v___f_1206_);
    v___x_1211_ = crate::leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1211_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1211_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1211_, 2, v___x_1202_);
    v___x_1212_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1212_, 0, v___x_1210_);
    crate::leanh::lean_ctor_set(v___x_1212_, 1, v___x_1211_);
    v_toApplicative_1213_ = crate::leanh::lean_ctor_get(v_inst_1188_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1213_);
    v_toBind_1214_ = crate::leanh::lean_ctor_get(v_inst_1188_, 1);
    crate::leanh::lean_inc_n(v_toBind_1214_, 2);
    crate::leanh::lean_dec_ref(v_inst_1188_);
    v_toPure_1215_ = crate::leanh::lean_ctor_get(v_toApplicative_1213_, 1);
    crate::leanh::lean_inc_n(v_toPure_1215_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_1213_);
    v___f_1216_ = crate::leanh::lean_alloc_closure(
        l_Lean_SMap_instForInProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1216_, 0, v_toPure_1215_);
    v___f_1217_ = crate::leanh::lean_alloc_closure(
        l_Lean_SMap_instForInProdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1217_, 0, v_toPure_1215_);
    v___f_1218_ = crate::leanh::lean_alloc_closure(
        l_Lean_SMap_instForInProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1218_, 0, v___y_1192_);
    crate::leanh::lean_closure_set(v___f_1218_, 1, v_toBind_1214_);
    crate::leanh::lean_closure_set(v___f_1218_, 2, v___f_1217_);
    v___x_140__overap_1219_ = l_Lean_SMap_forM___redArg(v___x_1212_, v___y_1190_, v___f_1218_);
    v___x_1220_ = crate::leanh::lean_apply_1(v___x_140__overap_1219_, v___y_1191_);
    v___x_1221_ = crate::leanh::lean_apply_4(
        v_toBind_1214_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1220_,
        v___f_1216_,
    );
    return v___x_1221_;
}
pub unsafe fn l_Lean_SMap_instForInProdOfMonad___redArg(
    mut v_inst_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1223_ = crate::leanh::lean_alloc_closure(
        l_Lean_SMap_instForInProdOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1223_, 0, v_inst_1222_);
    return v___f_1223_;
}
pub unsafe fn l_Lean_SMap_instForInProdOfMonad(
    mut v_00_u03b1_1224_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1225_: *mut crate::leanh::LeanObject,
    mut v_inst_1226_: *mut crate::leanh::LeanObject,
    mut v_inst_1227_: *mut crate::leanh::LeanObject,
    mut v_m_1228_: *mut crate::leanh::LeanObject,
    mut v_inst_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1230_ = crate::leanh::lean_alloc_closure(
        l_Lean_SMap_instForInProdOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1230_, 0, v_inst_1229_);
    return v___f_1230_;
}
pub unsafe fn l_Lean_SMap_instForInProdOfMonad___boxed(
    mut v_00_u03b1_1231_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1232_: *mut crate::leanh::LeanObject,
    mut v_inst_1233_: *mut crate::leanh::LeanObject,
    mut v_inst_1234_: *mut crate::leanh::LeanObject,
    mut v_m_1235_: *mut crate::leanh::LeanObject,
    mut v_inst_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1237_ = l_Lean_SMap_instForInProdOfMonad(
        v_00_u03b1_1231_,
        v_00_u03b2_1232_,
        v_inst_1233_,
        v_inst_1234_,
        v_m_1235_,
        v_inst_1236_,
    );
    crate::leanh::lean_dec_ref(v_inst_1234_);
    crate::leanh::lean_dec_ref(v_inst_1233_);
    return v_res_1237_;
}
pub unsafe fn l_Lean_SMap_iter___redArg(
    mut v_s_1238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_u2081_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1244_: u8 = 0;
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1254_: u8 = 0;
    let mut v_unused_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_u2081_1239_ = crate::leanh::lean_ctor_get(v_s_1238_, 0);
                crate::leanh::lean_inc_ref(v_map_u2081_1239_);
                v_map_u2082_1240_ = crate::leanh::lean_ctor_get(v_s_1238_, 1);
                crate::leanh::lean_inc_ref(v_map_u2082_1240_);
                crate::leanh::lean_dec_ref(v_s_1238_);
                v_buckets_1241_ = crate::leanh::lean_ctor_get(v_map_u2081_1239_, 1);
                v_isSharedCheck_1254_ = (!crate::leanh::lean_is_exclusive(v_map_u2081_1239_)) as u8;
                if v_isSharedCheck_1254_ == 0 {
                    v_unused_1255_ = crate::leanh::lean_ctor_get(v_map_u2081_1239_, 0);
                    crate::leanh::lean_dec(v_unused_1255_);
                    v___x_1243_ = v_map_u2081_1239_;
                    v_isShared_1244_ = v_isSharedCheck_1254_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1241_);
                    crate::leanh::lean_dec(v_map_u2081_1239_);
                    v___x_1243_ = crate::leanh::lean_box(0);
                    v_isShared_1244_ = v_isSharedCheck_1254_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1245_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_1244_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1243_, 1, v___x_1245_);
                    crate::leanh::lean_ctor_set(v___x_1243_, 0, v_buckets_1241_);
                    v___x_1247_ = v___x_1243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1253_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_buckets_1241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___x_1245_);
                    v___x_1247_ = v_reuseFailAlloc_1253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1248_ = crate::leanh::lean_box(0);
                v___x_1249_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1249_, 0, v___x_1247_);
                crate::leanh::lean_ctor_set(v___x_1249_, 1, v___x_1248_);
                v___x_1250_ = crate::leanh::lean_box(0);
                v___x_1251_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(
                    v_map_u2082_1240_,
                    v___x_1250_,
                );
                v___x_1252_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1252_, 0, v___x_1249_);
                crate::leanh::lean_ctor_set(v___x_1252_, 1, v___x_1251_);
                return v___x_1252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_iter(
    mut v_00_u03b1_1256_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1257_: *mut crate::leanh::LeanObject,
    mut v_inst_1258_: *mut crate::leanh::LeanObject,
    mut v_inst_1259_: *mut crate::leanh::LeanObject,
    mut v_s_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = l_Lean_SMap_iter___redArg(v_s_1260_);
    return v___x_1261_;
}
pub unsafe fn l_Lean_SMap_iter___boxed(
    mut v_00_u03b1_1262_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1263_: *mut crate::leanh::LeanObject,
    mut v_inst_1264_: *mut crate::leanh::LeanObject,
    mut v_inst_1265_: *mut crate::leanh::LeanObject,
    mut v_s_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_Lean_SMap_iter(
        v_00_u03b1_1262_,
        v_00_u03b2_1263_,
        v_inst_1264_,
        v_inst_1265_,
        v_s_1266_,
    );
    crate::leanh::lean_dec_ref(v_inst_1265_);
    crate::leanh::lean_dec_ref(v_inst_1264_);
    return v_res_1267_;
}
pub unsafe fn l_Lean_SMap_switch___redArg(
    mut v_m_1268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_1269_: u8 = 0;
    let mut v_map_u2081_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1274_: u8 = 0;
    let mut v___x_1275_: u8 = 0;
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_1269_ = crate::leanh::lean_ctor_get_uint8(
                    v_m_1268_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_1269_ == 0 {
                    return v_m_1268_;
                } else {
                    v_map_u2081_1270_ = crate::leanh::lean_ctor_get(v_m_1268_, 0);
                    v_map_u2082_1271_ = crate::leanh::lean_ctor_get(v_m_1268_, 1);
                    v_isSharedCheck_1279_ = (!crate::leanh::lean_is_exclusive(v_m_1268_)) as u8;
                    if v_isSharedCheck_1279_ == 0 {
                        v___x_1273_ = v_m_1268_;
                        v_isShared_1274_ = v_isSharedCheck_1279_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_u2082_1271_);
                        crate::leanh::lean_inc(v_map_u2081_1270_);
                        crate::leanh::lean_dec(v_m_1268_);
                        v___x_1273_ = crate::leanh::lean_box(0);
                        v_isShared_1274_ = v_isSharedCheck_1279_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1275_ = 0;
                if v_isShared_1274_ == 0 {
                    v___x_1277_ = v___x_1273_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1278_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_map_u2081_1270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_map_u2082_1271_);
                    v___x_1277_ = v_reuseFailAlloc_1278_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1277_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1275_,
                );
                return v___x_1277_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_switch(
    mut v_00_u03b1_1280_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1281_: *mut crate::leanh::LeanObject,
    mut v_inst_1282_: *mut crate::leanh::LeanObject,
    mut v_inst_1283_: *mut crate::leanh::LeanObject,
    mut v_m_1284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ = l_Lean_SMap_switch___redArg(v_m_1284_);
    return v___x_1285_;
}
pub unsafe fn l_Lean_SMap_switch___boxed(
    mut v_00_u03b1_1286_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1287_: *mut crate::leanh::LeanObject,
    mut v_inst_1288_: *mut crate::leanh::LeanObject,
    mut v_inst_1289_: *mut crate::leanh::LeanObject,
    mut v_m_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1291_ = l_Lean_SMap_switch(
        v_00_u03b1_1286_,
        v_00_u03b2_1287_,
        v_inst_1288_,
        v_inst_1289_,
        v_m_1290_,
    );
    crate::leanh::lean_dec_ref(v_inst_1289_);
    crate::leanh::lean_dec_ref(v_inst_1288_);
    return v_res_1291_;
}
pub unsafe fn l_Lean_SMap_foldStage2___redArg(
    mut v_f_1292_: *mut crate::leanh::LeanObject,
    mut v_s_1293_: *mut crate::leanh::LeanObject,
    mut v_m_1294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_u2082_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_u2082_1295_ = crate::leanh::lean_ctor_get(v_m_1294_, 1);
    crate::leanh::lean_inc_ref(v_map_u2082_1295_);
    crate::leanh::lean_dec_ref(v_m_1294_);
    v___x_1296_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_1295_, v_f_1292_, v_s_1293_);
    return v___x_1296_;
}
pub unsafe fn l_Lean_SMap_foldStage2(
    mut v_00_u03b1_1297_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1298_: *mut crate::leanh::LeanObject,
    mut v_inst_1299_: *mut crate::leanh::LeanObject,
    mut v_inst_1300_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1301_: *mut crate::leanh::LeanObject,
    mut v_f_1302_: *mut crate::leanh::LeanObject,
    mut v_s_1303_: *mut crate::leanh::LeanObject,
    mut v_m_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_u2082_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_u2082_1305_ = crate::leanh::lean_ctor_get(v_m_1304_, 1);
    crate::leanh::lean_inc_ref(v_map_u2082_1305_);
    crate::leanh::lean_dec_ref(v_m_1304_);
    v___x_1306_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_1305_, v_f_1302_, v_s_1303_);
    return v___x_1306_;
}
pub unsafe fn l_Lean_SMap_foldStage2___boxed(
    mut v_00_u03b1_1307_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1308_: *mut crate::leanh::LeanObject,
    mut v_inst_1309_: *mut crate::leanh::LeanObject,
    mut v_inst_1310_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1311_: *mut crate::leanh::LeanObject,
    mut v_f_1312_: *mut crate::leanh::LeanObject,
    mut v_s_1313_: *mut crate::leanh::LeanObject,
    mut v_m_1314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1315_ = l_Lean_SMap_foldStage2(
        v_00_u03b1_1307_,
        v_00_u03b2_1308_,
        v_inst_1309_,
        v_inst_1310_,
        v_00_u03c3_1311_,
        v_f_1312_,
        v_s_1313_,
        v_m_1314_,
    );
    crate::leanh::lean_dec_ref(v_inst_1310_);
    crate::leanh::lean_dec_ref(v_inst_1309_);
    return v_res_1315_;
}
pub unsafe fn l_Lean_SMap_foldM___redArg___lam__0(
    mut v_inst_1316_: *mut crate::leanh::LeanObject,
    mut v_f_1317_: *mut crate::leanh::LeanObject,
    mut v_map_u2082_1318_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1320_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v_inst_1316_,
        v_f_1317_,
        v_map_u2082_1318_,
        v_____do__lift_1319_,
    );
    return v___x_1320_;
}
pub unsafe fn l_Lean_SMap_foldM___redArg___lam__1(
    mut v_inst_1321_: *mut crate::leanh::LeanObject,
    mut v_f_1322_: *mut crate::leanh::LeanObject,
    mut v_acc_1323_: *mut crate::leanh::LeanObject,
    mut v_l_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1325_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1321_,
        v_f_1322_,
        v_acc_1323_,
        v_l_1324_,
    );
    return v___x_1325_;
}
pub unsafe fn l_Lean_SMap_foldM___redArg(
    mut v_inst_1326_: *mut crate::leanh::LeanObject,
    mut v_f_1327_: *mut crate::leanh::LeanObject,
    mut v_init_1328_: *mut crate::leanh::LeanObject,
    mut v_map_1329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_u2081_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: u8 = 0;
    v_map_u2081_1330_ = crate::leanh::lean_ctor_get(v_map_1329_, 0);
    crate::leanh::lean_inc_ref(v_map_u2081_1330_);
    v_toApplicative_1331_ = crate::leanh::lean_ctor_get(v_inst_1326_, 0);
    v_toBind_1332_ = crate::leanh::lean_ctor_get(v_inst_1326_, 1);
    crate::leanh::lean_inc(v_toBind_1332_);
    v_map_u2082_1333_ = crate::leanh::lean_ctor_get(v_map_1329_, 1);
    crate::leanh::lean_inc_ref(v_map_u2082_1333_);
    crate::leanh::lean_dec_ref(v_map_1329_);
    v_buckets_1334_ = crate::leanh::lean_ctor_get(v_map_u2081_1330_, 1);
    crate::leanh::lean_inc_ref(v_buckets_1334_);
    crate::leanh::lean_dec_ref(v_map_u2081_1330_);
    crate::leanh::lean_inc(v_f_1327_);
    crate::leanh::lean_inc_ref(v_inst_1326_);
    v___f_1335_ = crate::leanh::lean_alloc_closure(
        l_Lean_SMap_foldM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1335_, 0, v_inst_1326_);
    crate::leanh::lean_closure_set(v___f_1335_, 1, v_f_1327_);
    crate::leanh::lean_closure_set(v___f_1335_, 2, v_map_u2082_1333_);
    v___x_1336_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1337_ = lean_array_get_size(v_buckets_1334_);
    v___x_1338_ = lean_nat_dec_lt(v___x_1336_, v___x_1337_);
    if v___x_1338_ == 0 {
        let mut v_toPure_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_toApplicative_1331_);
        crate::leanh::lean_dec_ref(v_buckets_1334_);
        crate::leanh::lean_dec(v_f_1327_);
        crate::leanh::lean_dec_ref(v_inst_1326_);
        v_toPure_1339_ = crate::leanh::lean_ctor_get(v_toApplicative_1331_, 1);
        crate::leanh::lean_inc(v_toPure_1339_);
        crate::leanh::lean_dec_ref(v_toApplicative_1331_);
        v___x_1340_ =
            crate::leanh::lean_apply_2(v_toPure_1339_, crate::leanh::lean_box(0), v_init_1328_);
        v___x_1341_ = crate::leanh::lean_apply_4(
            v_toBind_1332_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1340_,
            v___f_1335_,
        );
        return v___x_1341_;
    } else {
        let mut v___f_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1343_: u8 = 0;
        crate::leanh::lean_inc_ref(v_inst_1326_);
        v___f_1342_ = crate::leanh::lean_alloc_closure(
            l_Lean_SMap_foldM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_1342_, 0, v_inst_1326_);
        crate::leanh::lean_closure_set(v___f_1342_, 1, v_f_1327_);
        v___x_1343_ = lean_nat_dec_le(v___x_1337_, v___x_1337_);
        if v___x_1343_ == 0 {
            if v___x_1338_ == 0 {
                let mut v_toPure_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc_ref(v_toApplicative_1331_);
                crate::leanh::lean_dec_ref(v___f_1342_);
                crate::leanh::lean_dec_ref(v_buckets_1334_);
                crate::leanh::lean_dec_ref(v_inst_1326_);
                v_toPure_1344_ = crate::leanh::lean_ctor_get(v_toApplicative_1331_, 1);
                crate::leanh::lean_inc(v_toPure_1344_);
                crate::leanh::lean_dec_ref(v_toApplicative_1331_);
                v___x_1345_ = crate::leanh::lean_apply_2(
                    v_toPure_1344_,
                    crate::leanh::lean_box(0),
                    v_init_1328_,
                );
                v___x_1346_ = crate::leanh::lean_apply_4(
                    v_toBind_1332_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1345_,
                    v___f_1335_,
                );
                return v___x_1346_;
            } else {
                let mut v___x_1347_: usize = 0;
                let mut v___x_1348_: usize = 0;
                let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1347_ = 0usize;
                v___x_1348_ = lean_usize_of_nat(v___x_1337_);
                v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_1326_,
                    v___f_1342_,
                    v_buckets_1334_,
                    v___x_1347_,
                    v___x_1348_,
                    v_init_1328_,
                );
                v___x_1350_ = crate::leanh::lean_apply_4(
                    v_toBind_1332_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1349_,
                    v___f_1335_,
                );
                return v___x_1350_;
            }
        } else {
            let mut v___x_1351_: usize = 0;
            let mut v___x_1352_: usize = 0;
            let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1351_ = 0usize;
            v___x_1352_ = lean_usize_of_nat(v___x_1337_);
            v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_1326_,
                v___f_1342_,
                v_buckets_1334_,
                v___x_1351_,
                v___x_1352_,
                v_init_1328_,
            );
            v___x_1354_ = crate::leanh::lean_apply_4(
                v_toBind_1332_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1353_,
                v___f_1335_,
            );
            return v___x_1354_;
        }
    }
}
pub unsafe fn l_Lean_SMap_foldM(
    mut v_00_u03b1_1355_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1356_: *mut crate::leanh::LeanObject,
    mut v_inst_1357_: *mut crate::leanh::LeanObject,
    mut v_inst_1358_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1359_: *mut crate::leanh::LeanObject,
    mut v_m_1360_: *mut crate::leanh::LeanObject,
    mut v_inst_1361_: *mut crate::leanh::LeanObject,
    mut v_f_1362_: *mut crate::leanh::LeanObject,
    mut v_init_1363_: *mut crate::leanh::LeanObject,
    mut v_map_1364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1365_ = l_Lean_SMap_foldM___redArg(v_inst_1361_, v_f_1362_, v_init_1363_, v_map_1364_);
    return v___x_1365_;
}
pub unsafe fn l_Lean_SMap_foldM___boxed(
    mut v_00_u03b1_1366_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1367_: *mut crate::leanh::LeanObject,
    mut v_inst_1368_: *mut crate::leanh::LeanObject,
    mut v_inst_1369_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1370_: *mut crate::leanh::LeanObject,
    mut v_m_1371_: *mut crate::leanh::LeanObject,
    mut v_inst_1372_: *mut crate::leanh::LeanObject,
    mut v_f_1373_: *mut crate::leanh::LeanObject,
    mut v_init_1374_: *mut crate::leanh::LeanObject,
    mut v_map_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1376_ = l_Lean_SMap_foldM(
        v_00_u03b1_1366_,
        v_00_u03b2_1367_,
        v_inst_1368_,
        v_inst_1369_,
        v_00_u03c3_1370_,
        v_m_1371_,
        v_inst_1372_,
        v_f_1373_,
        v_init_1374_,
        v_map_1375_,
    );
    crate::leanh::lean_dec_ref(v_inst_1369_);
    crate::leanh::lean_dec_ref(v_inst_1368_);
    return v_res_1376_;
}
pub unsafe fn l_Lean_SMap_fold___redArg___lam__0(
    mut v_f_1377_: *mut crate::leanh::LeanObject,
    mut v_x1_1378_: *mut crate::leanh::LeanObject,
    mut v_x2_1379_: *mut crate::leanh::LeanObject,
    mut v_x3_1380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1381_ = crate::leanh::lean_apply_3(v_f_1377_, v_x1_1378_, v_x2_1379_, v_x3_1380_);
    return v___x_1381_;
}
pub unsafe fn l_Lean_SMap_fold___redArg___lam__1(
    mut v___x_1382_: *mut crate::leanh::LeanObject,
    mut v___f_1383_: *mut crate::leanh::LeanObject,
    mut v_acc_1384_: *mut crate::leanh::LeanObject,
    mut v_l_1385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1386_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_1382_,
        v___f_1383_,
        v_acc_1384_,
        v_l_1385_,
    );
    return v___x_1386_;
}
pub unsafe fn l_Lean_SMap_fold___redArg(
    mut v_f_1406_: *mut crate::leanh::LeanObject,
    mut v_init_1407_: *mut crate::leanh::LeanObject,
    mut v_m_1408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_u2081_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u8 = 0;
    v_map_u2081_1409_ = crate::leanh::lean_ctor_get(v_m_1408_, 0);
    crate::leanh::lean_inc_ref(v_map_u2081_1409_);
    v_map_u2082_1410_ = crate::leanh::lean_ctor_get(v_m_1408_, 1);
    crate::leanh::lean_inc_ref(v_map_u2082_1410_);
    crate::leanh::lean_dec_ref(v_m_1408_);
    v___x_1411_ = l_Lean_SMap_fold___redArg___closed__9;
    v_buckets_1412_ = crate::leanh::lean_ctor_get(v_map_u2081_1409_, 1);
    crate::leanh::lean_inc_ref(v_buckets_1412_);
    crate::leanh::lean_dec_ref(v_map_u2081_1409_);
    v___x_1413_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1414_ = lean_array_get_size(v_buckets_1412_);
    v___x_1415_ = lean_nat_dec_lt(v___x_1413_, v___x_1414_);
    if v___x_1415_ == 0 {
        let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_1412_);
        v___x_1416_ =
            l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_1410_, v_f_1406_, v_init_1407_);
        return v___x_1416_;
    } else {
        let mut v___f_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1419_: u8 = 0;
        crate::leanh::lean_inc(v_f_1406_);
        v___f_1417_ = crate::leanh::lean_alloc_closure(
            l_Lean_SMap_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1417_, 0, v_f_1406_);
        v___f_1418_ = crate::leanh::lean_alloc_closure(
            l_Lean_SMap_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_1418_, 0, v___x_1411_);
        crate::leanh::lean_closure_set(v___f_1418_, 1, v___f_1417_);
        v___x_1419_ = lean_nat_dec_le(v___x_1414_, v___x_1414_);
        if v___x_1419_ == 0 {
            if v___x_1415_ == 0 {
                let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_1418_);
                crate::leanh::lean_dec_ref(v_buckets_1412_);
                v___x_1420_ = l_Lean_PersistentHashMap_foldl___redArg(
                    v_map_u2082_1410_,
                    v_f_1406_,
                    v_init_1407_,
                );
                return v___x_1420_;
            } else {
                let mut v___x_1421_: usize = 0;
                let mut v___x_1422_: usize = 0;
                let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1421_ = 0usize;
                v___x_1422_ = lean_usize_of_nat(v___x_1414_);
                v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1411_,
                    v___f_1418_,
                    v_buckets_1412_,
                    v___x_1421_,
                    v___x_1422_,
                    v_init_1407_,
                );
                v___x_1424_ = l_Lean_PersistentHashMap_foldl___redArg(
                    v_map_u2082_1410_,
                    v_f_1406_,
                    v___x_1423_,
                );
                return v___x_1424_;
            }
        } else {
            let mut v___x_1425_: usize = 0;
            let mut v___x_1426_: usize = 0;
            let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1425_ = 0usize;
            v___x_1426_ = lean_usize_of_nat(v___x_1414_);
            v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1411_,
                v___f_1418_,
                v_buckets_1412_,
                v___x_1425_,
                v___x_1426_,
                v_init_1407_,
            );
            v___x_1428_ =
                l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_1410_, v_f_1406_, v___x_1427_);
            return v___x_1428_;
        }
    }
}
pub unsafe fn l_Lean_SMap_fold(
    mut v_00_u03b1_1429_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1430_: *mut crate::leanh::LeanObject,
    mut v_inst_1431_: *mut crate::leanh::LeanObject,
    mut v_inst_1432_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1433_: *mut crate::leanh::LeanObject,
    mut v_f_1434_: *mut crate::leanh::LeanObject,
    mut v_init_1435_: *mut crate::leanh::LeanObject,
    mut v_m_1436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1437_ = l_Lean_SMap_fold___redArg(v_f_1434_, v_init_1435_, v_m_1436_);
    return v___x_1437_;
}
pub unsafe fn l_Lean_SMap_fold___boxed(
    mut v_00_u03b1_1438_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1439_: *mut crate::leanh::LeanObject,
    mut v_inst_1440_: *mut crate::leanh::LeanObject,
    mut v_inst_1441_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1442_: *mut crate::leanh::LeanObject,
    mut v_f_1443_: *mut crate::leanh::LeanObject,
    mut v_init_1444_: *mut crate::leanh::LeanObject,
    mut v_m_1445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1446_ = l_Lean_SMap_fold(
        v_00_u03b1_1438_,
        v_00_u03b2_1439_,
        v_inst_1440_,
        v_inst_1441_,
        v_00_u03c3_1442_,
        v_f_1443_,
        v_init_1444_,
        v_m_1445_,
    );
    crate::leanh::lean_dec_ref(v_inst_1441_);
    crate::leanh::lean_dec_ref(v_inst_1440_);
    return v_res_1446_;
}
pub unsafe fn l_Lean_SMap_numBuckets___redArg(
    mut v_m_1447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_u2081_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_u2081_1448_ = crate::leanh::lean_ctor_get(v_m_1447_, 0);
    v___x_1449_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_map_u2081_1448_);
    return v___x_1449_;
}
pub unsafe fn l_Lean_SMap_numBuckets___redArg___boxed(
    mut v_m_1450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1451_ = l_Lean_SMap_numBuckets___redArg(v_m_1450_);
    crate::leanh::lean_dec_ref(v_m_1450_);
    return v_res_1451_;
}
pub unsafe fn l_Lean_SMap_numBuckets(
    mut v_00_u03b1_1452_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1453_: *mut crate::leanh::LeanObject,
    mut v_inst_1454_: *mut crate::leanh::LeanObject,
    mut v_inst_1455_: *mut crate::leanh::LeanObject,
    mut v_m_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = l_Lean_SMap_numBuckets___redArg(v_m_1456_);
    return v___x_1457_;
}
pub unsafe fn l_Lean_SMap_numBuckets___boxed(
    mut v_00_u03b1_1458_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1459_: *mut crate::leanh::LeanObject,
    mut v_inst_1460_: *mut crate::leanh::LeanObject,
    mut v_inst_1461_: *mut crate::leanh::LeanObject,
    mut v_m_1462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1463_ = l_Lean_SMap_numBuckets(
        v_00_u03b1_1458_,
        v_00_u03b2_1459_,
        v_inst_1460_,
        v_inst_1461_,
        v_m_1462_,
    );
    crate::leanh::lean_dec_ref(v_m_1462_);
    crate::leanh::lean_dec_ref(v_inst_1461_);
    crate::leanh::lean_dec_ref(v_inst_1460_);
    return v_res_1463_;
}
pub unsafe fn l_Lean_SMap_toList___redArg___lam__0(
    mut v_es_1464_: *mut crate::leanh::LeanObject,
    mut v_a_1465_: *mut crate::leanh::LeanObject,
    mut v_b_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1467_, 0, v_a_1465_);
    crate::leanh::lean_ctor_set(v___x_1467_, 1, v_b_1466_);
    v___x_1468_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1468_, 0, v___x_1467_);
    crate::leanh::lean_ctor_set(v___x_1468_, 1, v_es_1464_);
    return v___x_1468_;
}
pub unsafe fn l_Lean_SMap_toList___redArg(
    mut v_m_1470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1471_ = l_Lean_SMap_toList___redArg___closed__0;
    v___x_1472_ = crate::leanh::lean_box(0);
    v___x_1473_ = l_Lean_SMap_fold___redArg(v___f_1471_, v___x_1472_, v_m_1470_);
    return v___x_1473_;
}
pub unsafe fn l_Lean_SMap_toList(
    mut v_00_u03b1_1474_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1475_: *mut crate::leanh::LeanObject,
    mut v_inst_1476_: *mut crate::leanh::LeanObject,
    mut v_inst_1477_: *mut crate::leanh::LeanObject,
    mut v_m_1478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = l_Lean_SMap_toList___redArg(v_m_1478_);
    return v___x_1479_;
}
pub unsafe fn l_Lean_SMap_toList___boxed(
    mut v_00_u03b1_1480_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1481_: *mut crate::leanh::LeanObject,
    mut v_inst_1482_: *mut crate::leanh::LeanObject,
    mut v_inst_1483_: *mut crate::leanh::LeanObject,
    mut v_m_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1485_ = l_Lean_SMap_toList(
        v_00_u03b1_1480_,
        v_00_u03b2_1481_,
        v_inst_1482_,
        v_inst_1483_,
        v_m_1484_,
    );
    crate::leanh::lean_dec_ref(v_inst_1483_);
    crate::leanh::lean_dec_ref(v_inst_1482_);
    return v_res_1485_;
}
pub unsafe fn l_List_toSMap___redArg___lam__0(
    mut v_inst_1486_: *mut crate::leanh::LeanObject,
    mut v_inst_1487_: *mut crate::leanh::LeanObject,
    mut v_s_1488_: *mut crate::leanh::LeanObject,
    mut v_x_1489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1490_ = crate::leanh::lean_ctor_get(v_x_1489_, 0);
    crate::leanh::lean_inc(v_fst_1490_);
    v_snd_1491_ = crate::leanh::lean_ctor_get(v_x_1489_, 1);
    crate::leanh::lean_inc(v_snd_1491_);
    crate::leanh::lean_dec_ref(v_x_1489_);
    v___x_1492_ = l_Lean_SMap_insert___redArg(
        v_inst_1486_,
        v_inst_1487_,
        v_s_1488_,
        v_fst_1490_,
        v_snd_1491_,
    );
    return v___x_1492_;
}
pub unsafe fn l_List_toSMap___redArg(
    mut v_inst_1493_: *mut crate::leanh::LeanObject,
    mut v_inst_1494_: *mut crate::leanh::LeanObject,
    mut v_es_1495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1496_ = crate::leanh::lean_alloc_closure(
        l_List_toSMap___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1496_, 0, v_inst_1493_);
    crate::leanh::lean_closure_set(v___f_1496_, 1, v_inst_1494_);
    v___x_1497_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__4),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__4_once),
        _init_l_Lean_SMap_instInhabited___closed__4,
    );
    v___x_1498_ = l_List_foldl___redArg(v___f_1496_, v___x_1497_, v_es_1495_);
    return v___x_1498_;
}
pub unsafe fn l_List_toSMap(
    mut v_00_u03b1_1499_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1500_: *mut crate::leanh::LeanObject,
    mut v_inst_1501_: *mut crate::leanh::LeanObject,
    mut v_inst_1502_: *mut crate::leanh::LeanObject,
    mut v_es_1503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1504_ = l_List_toSMap___redArg(v_inst_1501_, v_inst_1502_, v_es_1503_);
    return v___x_1504_;
}
pub unsafe fn l_Lean_instReprSMap___redArg___lam__0(
    mut v___x_1508_: *mut crate::leanh::LeanObject,
    mut v_v_1509_: *mut crate::leanh::LeanObject,
    mut v_prec_1510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ = l_Lean_SMap_toList___redArg(v_v_1509_);
    v___x_1512_ = l_List_repr___redArg(v___x_1508_, v___x_1511_);
    v___x_1513_ = l_Lean_instReprSMap___redArg___lam__0___closed__1;
    v___x_1514_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1514_, 0, v___x_1512_);
    crate::leanh::lean_ctor_set(v___x_1514_, 1, v___x_1513_);
    v___x_1515_ = l_Repr_addAppParen(v___x_1514_, v_prec_1510_);
    return v___x_1515_;
}
pub unsafe fn l_Lean_instReprSMap___redArg___lam__0___boxed(
    mut v___x_1516_: *mut crate::leanh::LeanObject,
    mut v_v_1517_: *mut crate::leanh::LeanObject,
    mut v_prec_1518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1519_ = l_Lean_instReprSMap___redArg___lam__0(v___x_1516_, v_v_1517_, v_prec_1518_);
    crate::leanh::lean_dec(v_prec_1518_);
    return v_res_1519_;
}
pub unsafe fn l_Lean_instReprSMap___redArg(
    mut v_inst_1520_: *mut crate::leanh::LeanObject,
    mut v_inst_1521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1522_ = crate::leanh::lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1522_, 0, v_inst_1521_);
    v___x_1523_ =
        crate::leanh::lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1523_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1523_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1523_, 2, v_inst_1520_);
    crate::leanh::lean_closure_set(v___x_1523_, 3, v___f_1522_);
    v___f_1524_ = crate::leanh::lean_alloc_closure(
        l_Lean_instReprSMap___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1524_, 0, v___x_1523_);
    return v___f_1524_;
}
pub unsafe fn l_Lean_instReprSMap(
    mut v_00_u03b1_1525_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1526_: *mut crate::leanh::LeanObject,
    mut v_x_1527_: *mut crate::leanh::LeanObject,
    mut v_x_1528_: *mut crate::leanh::LeanObject,
    mut v_inst_1529_: *mut crate::leanh::LeanObject,
    mut v_inst_1530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Lean_instReprSMap___redArg(v_inst_1529_, v_inst_1530_);
    return v___x_1531_;
}
pub unsafe fn l_Lean_instReprSMap___boxed(
    mut v_00_u03b1_1532_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1533_: *mut crate::leanh::LeanObject,
    mut v_x_1534_: *mut crate::leanh::LeanObject,
    mut v_x_1535_: *mut crate::leanh::LeanObject,
    mut v_inst_1536_: *mut crate::leanh::LeanObject,
    mut v_inst_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1538_ = l_Lean_instReprSMap(
        v_00_u03b1_1532_,
        v_00_u03b2_1533_,
        v_x_1534_,
        v_x_1535_,
        v_inst_1536_,
        v_inst_1537_,
    );
    crate::leanh::lean_dec_ref(v_x_1535_);
    crate::leanh::lean_dec_ref(v_x_1534_);
    return v_res_1538_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_SMap(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentHashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_SMap(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_SMap(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_PersistentHashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_SMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_SMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_SMap(builtin);
}
