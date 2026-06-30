// Lean compiler output
// Module: Lean.Data.SMap
// Imports: Std.Data.HashMap.Basic Lean.Data.PersistentHashMap Std.Data.HashMap.Iterator Lean.Data.Iterators.Producers.PersistentHashMap Init.Data.Iterators.Combinators.Append
use crate::ffi::{
    lean_array_get_size, lean_mk_array, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_of_nat,
};
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
static mut l_Lean_SMap_instInhabited___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SMap_instInhabited___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_SMap_instInhabited___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SMap_instInhabited___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_SMap_instInhabited___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SMap_instInhabited___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_SMap_instInhabited___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SMap_instInhabited___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_SMap_instInhabited___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SMap_instInhabited___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_SMap_find_x21___redArg___closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_SMap_find_x21___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_find_x21___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SMap_find_x21___redArg___closed__1_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 83, 77, 97, 112, 46, 102, 105, 110, 100, 33, 0,
        ],
    };
static mut l_Lean_SMap_find_x21___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_find_x21___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SMap_find_x21___redArg___closed__2_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_SMap_find_x21___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_find_x21___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_SMap_find_x21___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SMap_find_x21___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_SMap_fold___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Lean_SMap_fold___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
static mut l_Lean_SMap_fold___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
static mut l_Lean_SMap_fold___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
static mut l_Lean_SMap_fold___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
static mut l_Lean_SMap_fold___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
static mut l_Lean_SMap_fold___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
static mut l_Lean_SMap_fold___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_SMap_fold___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__8_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_SMap_fold___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SMap_fold___redArg___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_SMap_fold___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_fold___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SMap_toList___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_SMap_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SMap_toList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SMap_toList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprSMap___redArg___lam__0___closed__0_value: leanh::LeanStringObject<
    8,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_instReprSMap___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprSMap___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprSMap___redArg___lam__0___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprSMap___redArg___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprSMap___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprSMap___redArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_SMap_instInhabited___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_770_ = leanh::lean_box(0);
    v___x_771_ = leanh::lean_unsigned_to_nat(16);
    v___x_772_ = lean_mk_array(v___x_771_, v___x_770_);
    return v___x_772_;
}
pub unsafe fn _init_l_Lean_SMap_instInhabited___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_773_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__0_once),
        _init_l_Lean_SMap_instInhabited___closed__0,
    );
    v___x_774_ = leanh::lean_unsigned_to_nat(0);
    v___x_775_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_775_, 0, v___x_774_);
    leanh::lean_ctor_set(v___x_775_, 1, v___x_773_);
    return v___x_775_;
}
pub unsafe fn _init_l_Lean_SMap_instInhabited___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_776_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_776_;
}
pub unsafe fn _init_l_Lean_SMap_instInhabited___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_777_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__2),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__2_once),
        _init_l_Lean_SMap_instInhabited___closed__2,
    );
    v___x_778_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_778_, 0, v___x_777_);
    return v___x_778_;
}
pub unsafe fn _init_l_Lean_SMap_instInhabited___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: u8 = 0;
    let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_779_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__3),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__3_once),
        _init_l_Lean_SMap_instInhabited___closed__3,
    );
    v___x_780_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__1),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__1_once),
        _init_l_Lean_SMap_instInhabited___closed__1,
    );
    v___x_781_ = 1;
    v___x_782_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_782_, 0, v___x_780_);
    leanh::lean_ctor_set(v___x_782_, 1, v___x_779_);
    leanh::lean_ctor_set_uint8(
        v___x_782_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_781_,
    );
    return v___x_782_;
}
pub unsafe fn l_Lean_SMap_instInhabited(
    mut v_00_u03b1_783_: *mut leanh::LeanObject,
    mut v_00_u03b2_784_: *mut leanh::LeanObject,
    mut v_inst_785_: *mut leanh::LeanObject,
    mut v_inst_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_787_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__4),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__4_once),
        _init_l_Lean_SMap_instInhabited___closed__4,
    );
    return v___x_787_;
}
pub unsafe fn l_Lean_SMap_instInhabited___boxed(
    mut v_00_u03b1_788_: *mut leanh::LeanObject,
    mut v_00_u03b2_789_: *mut leanh::LeanObject,
    mut v_inst_790_: *mut leanh::LeanObject,
    mut v_inst_791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_792_ =
        l_Lean_SMap_instInhabited(v_00_u03b1_788_, v_00_u03b2_789_, v_inst_790_, v_inst_791_);
    leanh::lean_dec_ref(v_inst_791_);
    leanh::lean_dec_ref(v_inst_790_);
    return v_res_792_;
}
pub unsafe fn l_Lean_SMap_empty(
    mut v_00_u03b1_793_: *mut leanh::LeanObject,
    mut v_00_u03b2_794_: *mut leanh::LeanObject,
    mut v_inst_795_: *mut leanh::LeanObject,
    mut v_inst_796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_797_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__4),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__4_once),
        _init_l_Lean_SMap_instInhabited___closed__4,
    );
    return v___x_797_;
}
pub unsafe fn l_Lean_SMap_empty___boxed(
    mut v_00_u03b1_798_: *mut leanh::LeanObject,
    mut v_00_u03b2_799_: *mut leanh::LeanObject,
    mut v_inst_800_: *mut leanh::LeanObject,
    mut v_inst_801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_802_ = l_Lean_SMap_empty(v_00_u03b1_798_, v_00_u03b2_799_, v_inst_800_, v_inst_801_);
    leanh::lean_dec_ref(v_inst_801_);
    leanh::lean_dec_ref(v_inst_800_);
    return v_res_802_;
}
pub unsafe fn l_Lean_SMap_fromHashMap___redArg(
    mut v_m_803_: *mut leanh::LeanObject,
    mut v_stage_u2081_804_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_805_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__3),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__3_once),
        _init_l_Lean_SMap_instInhabited___closed__3,
    );
    v___x_806_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_806_, 0, v_m_803_);
    leanh::lean_ctor_set(v___x_806_, 1, v___x_805_);
    leanh::lean_ctor_set_uint8(
        v___x_806_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_stage_u2081_804_,
    );
    return v___x_806_;
}
pub unsafe fn l_Lean_SMap_fromHashMap___redArg___boxed(
    mut v_m_807_: *mut leanh::LeanObject,
    mut v_stage_u2081_808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_boxed_809_: u8 = 0;
    let mut v_res_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_stage_u2081_boxed_809_ = (leanh::lean_unbox(v_stage_u2081_808_) as u8);
    v_res_810_ = l_Lean_SMap_fromHashMap___redArg(v_m_807_, v_stage_u2081_boxed_809_);
    return v_res_810_;
}
pub unsafe fn l_Lean_SMap_fromHashMap(
    mut v_00_u03b1_811_: *mut leanh::LeanObject,
    mut v_00_u03b2_812_: *mut leanh::LeanObject,
    mut v_inst_813_: *mut leanh::LeanObject,
    mut v_inst_814_: *mut leanh::LeanObject,
    mut v_m_815_: *mut leanh::LeanObject,
    mut v_stage_u2081_816_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_817_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__3),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__3_once),
        _init_l_Lean_SMap_instInhabited___closed__3,
    );
    v___x_818_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_818_, 0, v_m_815_);
    leanh::lean_ctor_set(v___x_818_, 1, v___x_817_);
    leanh::lean_ctor_set_uint8(
        v___x_818_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_stage_u2081_816_,
    );
    return v___x_818_;
}
pub unsafe fn l_Lean_SMap_fromHashMap___boxed(
    mut v_00_u03b1_819_: *mut leanh::LeanObject,
    mut v_00_u03b2_820_: *mut leanh::LeanObject,
    mut v_inst_821_: *mut leanh::LeanObject,
    mut v_inst_822_: *mut leanh::LeanObject,
    mut v_m_823_: *mut leanh::LeanObject,
    mut v_stage_u2081_824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_boxed_825_: u8 = 0;
    let mut v_res_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_stage_u2081_boxed_825_ = (leanh::lean_unbox(v_stage_u2081_824_) as u8);
    v_res_826_ = l_Lean_SMap_fromHashMap(
        v_00_u03b1_819_,
        v_00_u03b2_820_,
        v_inst_821_,
        v_inst_822_,
        v_m_823_,
        v_stage_u2081_boxed_825_,
    );
    leanh::lean_dec_ref(v_inst_822_);
    leanh::lean_dec_ref(v_inst_821_);
    return v_res_826_;
}
pub unsafe fn l_Lean_SMap_insert___redArg(
    mut v_inst_827_: *mut leanh::LeanObject,
    mut v_inst_828_: *mut leanh::LeanObject,
    mut v_x_829_: *mut leanh::LeanObject,
    mut v_x_830_: *mut leanh::LeanObject,
    mut v_x_831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_832_: u8 = 0;
    let mut v_map_u2081_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_837_: u8 = 0;
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_842_: u8 = 0;
    let mut v_map_u2081_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_847_: u8 = 0;
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_852_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_832_ = leanh::lean_ctor_get_uint8(
                    v_x_829_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_832_ == 0 {
                    v_map_u2081_833_ = leanh::lean_ctor_get(v_x_829_, 0);
                    v_map_u2082_834_ = leanh::lean_ctor_get(v_x_829_, 1);
                    v_isSharedCheck_842_ = (!leanh::lean_is_exclusive(v_x_829_)) as u8;
                    if v_isSharedCheck_842_ == 0 {
                        v___x_836_ = v_x_829_;
                        v_isShared_837_ = v_isSharedCheck_842_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_834_);
                        leanh::lean_inc(v_map_u2081_833_);
                        leanh::lean_dec(v_x_829_);
                        v___x_836_ = leanh::lean_box(0);
                        v_isShared_837_ = v_isSharedCheck_842_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_843_ = leanh::lean_ctor_get(v_x_829_, 0);
                    v_map_u2082_844_ = leanh::lean_ctor_get(v_x_829_, 1);
                    v_isSharedCheck_852_ = (!leanh::lean_is_exclusive(v_x_829_)) as u8;
                    if v_isSharedCheck_852_ == 0 {
                        v___x_846_ = v_x_829_;
                        v_isShared_847_ = v_isSharedCheck_852_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_844_);
                        leanh::lean_inc(v_map_u2081_843_);
                        leanh::lean_dec(v_x_829_);
                        v___x_846_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_836_, 1, v___x_838_);
                    v___x_840_ = v___x_836_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_841_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_841_, 0, v_map_u2081_833_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_838_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_841_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                    leanh::lean_ctor_set(v___x_846_, 0, v___x_848_);
                    v___x_850_ = v___x_846_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_851_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_851_, 1, v_map_u2082_844_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_851_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_00_u03b1_853_: *mut leanh::LeanObject,
    mut v_00_u03b2_854_: *mut leanh::LeanObject,
    mut v_inst_855_: *mut leanh::LeanObject,
    mut v_inst_856_: *mut leanh::LeanObject,
    mut v_x_857_: *mut leanh::LeanObject,
    mut v_x_858_: *mut leanh::LeanObject,
    mut v_x_859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ =
        l_Lean_SMap_insert___redArg(v_inst_855_, v_inst_856_, v_x_857_, v_x_858_, v_x_859_);
    return v___x_860_;
}
pub unsafe fn l_Lean_SMap_insert_x27___redArg(
    mut v_inst_861_: *mut leanh::LeanObject,
    mut v_inst_862_: *mut leanh::LeanObject,
    mut v_x_863_: *mut leanh::LeanObject,
    mut v_x_864_: *mut leanh::LeanObject,
    mut v_x_865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_866_: u8 = 0;
    let mut v_map_u2081_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_871_: u8 = 0;
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_876_: u8 = 0;
    let mut v_map_u2081_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_881_: u8 = 0;
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_866_ = leanh::lean_ctor_get_uint8(
                    v_x_863_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_866_ == 0 {
                    v_map_u2081_867_ = leanh::lean_ctor_get(v_x_863_, 0);
                    v_map_u2082_868_ = leanh::lean_ctor_get(v_x_863_, 1);
                    v_isSharedCheck_876_ = (!leanh::lean_is_exclusive(v_x_863_)) as u8;
                    if v_isSharedCheck_876_ == 0 {
                        v___x_870_ = v_x_863_;
                        v_isShared_871_ = v_isSharedCheck_876_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_868_);
                        leanh::lean_inc(v_map_u2081_867_);
                        leanh::lean_dec(v_x_863_);
                        v___x_870_ = leanh::lean_box(0);
                        v_isShared_871_ = v_isSharedCheck_876_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_877_ = leanh::lean_ctor_get(v_x_863_, 0);
                    v_map_u2082_878_ = leanh::lean_ctor_get(v_x_863_, 1);
                    v_isSharedCheck_886_ = (!leanh::lean_is_exclusive(v_x_863_)) as u8;
                    if v_isSharedCheck_886_ == 0 {
                        v___x_880_ = v_x_863_;
                        v_isShared_881_ = v_isSharedCheck_886_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_878_);
                        leanh::lean_inc(v_map_u2081_877_);
                        leanh::lean_dec(v_x_863_);
                        v___x_880_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_870_, 1, v___x_872_);
                    v___x_874_ = v___x_870_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_875_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_875_, 0, v_map_u2081_867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_872_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_875_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                    leanh::lean_ctor_set(v___x_880_, 0, v___x_882_);
                    v___x_884_ = v___x_880_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_885_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_885_, 1, v_map_u2082_878_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_885_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_00_u03b1_887_: *mut leanh::LeanObject,
    mut v_00_u03b2_888_: *mut leanh::LeanObject,
    mut v_inst_889_: *mut leanh::LeanObject,
    mut v_inst_890_: *mut leanh::LeanObject,
    mut v_x_891_: *mut leanh::LeanObject,
    mut v_x_892_: *mut leanh::LeanObject,
    mut v_x_893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_894_ =
        l_Lean_SMap_insert_x27___redArg(v_inst_889_, v_inst_890_, v_x_891_, v_x_892_, v_x_893_);
    return v___x_894_;
}
pub unsafe fn l_Lean_SMap_find_x3f___redArg(
    mut v_inst_895_: *mut leanh::LeanObject,
    mut v_inst_896_: *mut leanh::LeanObject,
    mut v_x_897_: *mut leanh::LeanObject,
    mut v_x_898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_899_: u8 = 0;
    v_stage_u2081_899_ = leanh::lean_ctor_get_uint8(
        v_x_897_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_899_ == 0 {
        let mut v_map_u2081_900_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_901_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_900_ = leanh::lean_ctor_get(v_x_897_, 0);
        v_map_u2082_901_ = leanh::lean_ctor_get(v_x_897_, 1);
        leanh::lean_inc(v_x_898_);
        leanh::lean_inc_ref(v_inst_896_);
        leanh::lean_inc_ref(v_inst_895_);
        v___x_902_ = l_Lean_PersistentHashMap_find_x3f___redArg(
            v_inst_895_,
            v_inst_896_,
            v_map_u2082_901_,
            v_x_898_,
        );
        if leanh::lean_obj_tag(v___x_902_) == 0 {
            let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                v_inst_895_,
                v_inst_896_,
                v_map_u2081_900_,
                v_x_898_,
            );
            return v___x_903_;
        } else {
            leanh::lean_dec(v_x_898_);
            leanh::lean_dec_ref(v_inst_896_);
            leanh::lean_dec_ref(v_inst_895_);
            return v___x_902_;
        }
    } else {
        let mut v_map_u2081_904_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_904_ = leanh::lean_ctor_get(v_x_897_, 0);
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
    mut v_inst_906_: *mut leanh::LeanObject,
    mut v_inst_907_: *mut leanh::LeanObject,
    mut v_x_908_: *mut leanh::LeanObject,
    mut v_x_909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_910_ = l_Lean_SMap_find_x3f___redArg(v_inst_906_, v_inst_907_, v_x_908_, v_x_909_);
    leanh::lean_dec_ref(v_x_908_);
    return v_res_910_;
}
pub unsafe fn l_Lean_SMap_find_x3f(
    mut v_00_u03b1_911_: *mut leanh::LeanObject,
    mut v_00_u03b2_912_: *mut leanh::LeanObject,
    mut v_inst_913_: *mut leanh::LeanObject,
    mut v_inst_914_: *mut leanh::LeanObject,
    mut v_x_915_: *mut leanh::LeanObject,
    mut v_x_916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_917_ = l_Lean_SMap_find_x3f___redArg(v_inst_913_, v_inst_914_, v_x_915_, v_x_916_);
    return v___x_917_;
}
pub unsafe fn l_Lean_SMap_find_x3f___boxed(
    mut v_00_u03b1_918_: *mut leanh::LeanObject,
    mut v_00_u03b2_919_: *mut leanh::LeanObject,
    mut v_inst_920_: *mut leanh::LeanObject,
    mut v_inst_921_: *mut leanh::LeanObject,
    mut v_x_922_: *mut leanh::LeanObject,
    mut v_x_923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_924_ = l_Lean_SMap_find_x3f(
        v_00_u03b1_918_,
        v_00_u03b2_919_,
        v_inst_920_,
        v_inst_921_,
        v_x_922_,
        v_x_923_,
    );
    leanh::lean_dec_ref(v_x_922_);
    return v_res_924_;
}
pub unsafe fn l_Lean_SMap_findD___redArg(
    mut v_inst_925_: *mut leanh::LeanObject,
    mut v_inst_926_: *mut leanh::LeanObject,
    mut v_m_927_: *mut leanh::LeanObject,
    mut v_a_928_: *mut leanh::LeanObject,
    mut v_b_u2080_929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_930_ = l_Lean_SMap_find_x3f___redArg(v_inst_925_, v_inst_926_, v_m_927_, v_a_928_);
    if leanh::lean_obj_tag(v___x_930_) == 0 {
        leanh::lean_inc(v_b_u2080_929_);
        return v_b_u2080_929_;
    } else {
        let mut v_val_931_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_931_ = leanh::lean_ctor_get(v___x_930_, 0);
        leanh::lean_inc(v_val_931_);
        leanh::lean_dec_ref_known(v___x_930_, 1);
        return v_val_931_;
    }
}
pub unsafe fn l_Lean_SMap_findD___redArg___boxed(
    mut v_inst_932_: *mut leanh::LeanObject,
    mut v_inst_933_: *mut leanh::LeanObject,
    mut v_m_934_: *mut leanh::LeanObject,
    mut v_a_935_: *mut leanh::LeanObject,
    mut v_b_u2080_936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_937_ =
        l_Lean_SMap_findD___redArg(v_inst_932_, v_inst_933_, v_m_934_, v_a_935_, v_b_u2080_936_);
    leanh::lean_dec(v_b_u2080_936_);
    leanh::lean_dec_ref(v_m_934_);
    return v_res_937_;
}
pub unsafe fn l_Lean_SMap_findD(
    mut v_00_u03b1_938_: *mut leanh::LeanObject,
    mut v_00_u03b2_939_: *mut leanh::LeanObject,
    mut v_inst_940_: *mut leanh::LeanObject,
    mut v_inst_941_: *mut leanh::LeanObject,
    mut v_m_942_: *mut leanh::LeanObject,
    mut v_a_943_: *mut leanh::LeanObject,
    mut v_b_u2080_944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_945_ = l_Lean_SMap_find_x3f___redArg(v_inst_940_, v_inst_941_, v_m_942_, v_a_943_);
    if leanh::lean_obj_tag(v___x_945_) == 0 {
        leanh::lean_inc(v_b_u2080_944_);
        return v_b_u2080_944_;
    } else {
        let mut v_val_946_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_946_ = leanh::lean_ctor_get(v___x_945_, 0);
        leanh::lean_inc(v_val_946_);
        leanh::lean_dec_ref_known(v___x_945_, 1);
        return v_val_946_;
    }
}
pub unsafe fn l_Lean_SMap_findD___boxed(
    mut v_00_u03b1_947_: *mut leanh::LeanObject,
    mut v_00_u03b2_948_: *mut leanh::LeanObject,
    mut v_inst_949_: *mut leanh::LeanObject,
    mut v_inst_950_: *mut leanh::LeanObject,
    mut v_m_951_: *mut leanh::LeanObject,
    mut v_a_952_: *mut leanh::LeanObject,
    mut v_b_u2080_953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_954_ = l_Lean_SMap_findD(
        v_00_u03b1_947_,
        v_00_u03b2_948_,
        v_inst_949_,
        v_inst_950_,
        v_m_951_,
        v_a_952_,
        v_b_u2080_953_,
    );
    leanh::lean_dec(v_b_u2080_953_);
    leanh::lean_dec_ref(v_m_951_);
    return v_res_954_;
}
pub unsafe fn _init_l_Lean_SMap_find_x21___redArg___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_958_ = l_Lean_SMap_find_x21___redArg___closed__2;
    v___x_959_ = leanh::lean_unsigned_to_nat(14);
    v___x_960_ = leanh::lean_unsigned_to_nat(70);
    v___x_961_ = l_Lean_SMap_find_x21___redArg___closed__1;
    v___x_962_ = l_Lean_SMap_find_x21___redArg___closed__0;
    v___x_963_ =
        l_mkPanicMessageWithDecl(v___x_962_, v___x_961_, v___x_960_, v___x_959_, v___x_958_);
    return v___x_963_;
}
pub unsafe fn l_Lean_SMap_find_x21___redArg(
    mut v_inst_964_: *mut leanh::LeanObject,
    mut v_inst_965_: *mut leanh::LeanObject,
    mut v_inst_966_: *mut leanh::LeanObject,
    mut v_m_967_: *mut leanh::LeanObject,
    mut v_a_968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_969_ = l_Lean_SMap_find_x3f___redArg(v_inst_964_, v_inst_965_, v_m_967_, v_a_968_);
    if leanh::lean_obj_tag(v___x_969_) == 0 {
        let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_970_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_SMap_find_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Lean_SMap_find_x21___redArg___closed__3_once),
            _init_l_Lean_SMap_find_x21___redArg___closed__3,
        );
        v___x_971_ = l_panic___redArg(v_inst_966_, v___x_970_);
        return v___x_971_;
    } else {
        let mut v_val_972_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_972_ = leanh::lean_ctor_get(v___x_969_, 0);
        leanh::lean_inc(v_val_972_);
        leanh::lean_dec_ref_known(v___x_969_, 1);
        return v_val_972_;
    }
}
pub unsafe fn l_Lean_SMap_find_x21___redArg___boxed(
    mut v_inst_973_: *mut leanh::LeanObject,
    mut v_inst_974_: *mut leanh::LeanObject,
    mut v_inst_975_: *mut leanh::LeanObject,
    mut v_m_976_: *mut leanh::LeanObject,
    mut v_a_977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_978_ =
        l_Lean_SMap_find_x21___redArg(v_inst_973_, v_inst_974_, v_inst_975_, v_m_976_, v_a_977_);
    leanh::lean_dec_ref(v_m_976_);
    leanh::lean_dec(v_inst_975_);
    return v_res_978_;
}
pub unsafe fn l_Lean_SMap_find_x21(
    mut v_00_u03b1_979_: *mut leanh::LeanObject,
    mut v_00_u03b2_980_: *mut leanh::LeanObject,
    mut v_inst_981_: *mut leanh::LeanObject,
    mut v_inst_982_: *mut leanh::LeanObject,
    mut v_inst_983_: *mut leanh::LeanObject,
    mut v_m_984_: *mut leanh::LeanObject,
    mut v_a_985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_986_ = l_Lean_SMap_find_x3f___redArg(v_inst_981_, v_inst_982_, v_m_984_, v_a_985_);
    if leanh::lean_obj_tag(v___x_986_) == 0 {
        let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_987_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_SMap_find_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Lean_SMap_find_x21___redArg___closed__3_once),
            _init_l_Lean_SMap_find_x21___redArg___closed__3,
        );
        v___x_988_ = l_panic___redArg(v_inst_983_, v___x_987_);
        return v___x_988_;
    } else {
        let mut v_val_989_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_989_ = leanh::lean_ctor_get(v___x_986_, 0);
        leanh::lean_inc(v_val_989_);
        leanh::lean_dec_ref_known(v___x_986_, 1);
        return v_val_989_;
    }
}
pub unsafe fn l_Lean_SMap_find_x21___boxed(
    mut v_00_u03b1_990_: *mut leanh::LeanObject,
    mut v_00_u03b2_991_: *mut leanh::LeanObject,
    mut v_inst_992_: *mut leanh::LeanObject,
    mut v_inst_993_: *mut leanh::LeanObject,
    mut v_inst_994_: *mut leanh::LeanObject,
    mut v_m_995_: *mut leanh::LeanObject,
    mut v_a_996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_997_ = l_Lean_SMap_find_x21(
        v_00_u03b1_990_,
        v_00_u03b2_991_,
        v_inst_992_,
        v_inst_993_,
        v_inst_994_,
        v_m_995_,
        v_a_996_,
    );
    leanh::lean_dec_ref(v_m_995_);
    leanh::lean_dec(v_inst_994_);
    return v_res_997_;
}
pub unsafe fn l_Lean_SMap_contains___redArg(
    mut v_inst_998_: *mut leanh::LeanObject,
    mut v_inst_999_: *mut leanh::LeanObject,
    mut v_x_1000_: *mut leanh::LeanObject,
    mut v_x_1001_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_stage_u2081_1002_: u8 = 0;
    v_stage_u2081_1002_ = leanh::lean_ctor_get_uint8(
        v_x_1000_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_1002_ == 0 {
        let mut v_map_u2081_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1005_: u8 = 0;
        v_map_u2081_1003_ = leanh::lean_ctor_get(v_x_1000_, 0);
        leanh::lean_inc_ref(v_map_u2081_1003_);
        v_map_u2082_1004_ = leanh::lean_ctor_get(v_x_1000_, 1);
        leanh::lean_inc_ref(v_map_u2082_1004_);
        leanh::lean_dec_ref(v_x_1000_);
        leanh::lean_inc(v_x_1001_);
        leanh::lean_inc_ref(v_inst_999_);
        leanh::lean_inc_ref(v_inst_998_);
        v___x_1005_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v_inst_998_,
            v_inst_999_,
            v_map_u2081_1003_,
            v_x_1001_,
        );
        leanh::lean_dec_ref(v_map_u2081_1003_);
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
            leanh::lean_dec_ref(v_map_u2082_1004_);
            leanh::lean_dec(v_x_1001_);
            leanh::lean_dec_ref(v_inst_999_);
            leanh::lean_dec_ref(v_inst_998_);
            return v___x_1005_;
        }
    } else {
        let mut v_map_u2081_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1008_: u8 = 0;
        v_map_u2081_1007_ = leanh::lean_ctor_get(v_x_1000_, 0);
        leanh::lean_inc_ref(v_map_u2081_1007_);
        leanh::lean_dec_ref(v_x_1000_);
        v___x_1008_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v_inst_998_,
            v_inst_999_,
            v_map_u2081_1007_,
            v_x_1001_,
        );
        leanh::lean_dec_ref(v_map_u2081_1007_);
        return v___x_1008_;
    }
}
pub unsafe fn l_Lean_SMap_contains___redArg___boxed(
    mut v_inst_1009_: *mut leanh::LeanObject,
    mut v_inst_1010_: *mut leanh::LeanObject,
    mut v_x_1011_: *mut leanh::LeanObject,
    mut v_x_1012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1013_: u8 = 0;
    let mut v_r_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Lean_SMap_contains___redArg(v_inst_1009_, v_inst_1010_, v_x_1011_, v_x_1012_);
    v_r_1014_ = leanh::lean_box((v_res_1013_) as usize);
    return v_r_1014_;
}
pub unsafe fn l_Lean_SMap_contains(
    mut v_00_u03b1_1015_: *mut leanh::LeanObject,
    mut v_00_u03b2_1016_: *mut leanh::LeanObject,
    mut v_inst_1017_: *mut leanh::LeanObject,
    mut v_inst_1018_: *mut leanh::LeanObject,
    mut v_x_1019_: *mut leanh::LeanObject,
    mut v_x_1020_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1021_: u8 = 0;
    v___x_1021_ = l_Lean_SMap_contains___redArg(v_inst_1017_, v_inst_1018_, v_x_1019_, v_x_1020_);
    return v___x_1021_;
}
pub unsafe fn l_Lean_SMap_contains___boxed(
    mut v_00_u03b1_1022_: *mut leanh::LeanObject,
    mut v_00_u03b2_1023_: *mut leanh::LeanObject,
    mut v_inst_1024_: *mut leanh::LeanObject,
    mut v_inst_1025_: *mut leanh::LeanObject,
    mut v_x_1026_: *mut leanh::LeanObject,
    mut v_x_1027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1028_: u8 = 0;
    let mut v_r_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1028_ = l_Lean_SMap_contains(
        v_00_u03b1_1022_,
        v_00_u03b2_1023_,
        v_inst_1024_,
        v_inst_1025_,
        v_x_1026_,
        v_x_1027_,
    );
    v_r_1029_ = leanh::lean_box((v_res_1028_) as usize);
    return v_r_1029_;
}
pub unsafe fn l_Lean_SMap_find_x3f_x27___redArg(
    mut v_inst_1030_: *mut leanh::LeanObject,
    mut v_inst_1031_: *mut leanh::LeanObject,
    mut v_x_1032_: *mut leanh::LeanObject,
    mut v_x_1033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_1034_: u8 = 0;
    v_stage_u2081_1034_ = leanh::lean_ctor_get_uint8(
        v_x_1032_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_1034_ == 0 {
        let mut v_map_u2081_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_1035_ = leanh::lean_ctor_get(v_x_1032_, 0);
        v_map_u2082_1036_ = leanh::lean_ctor_get(v_x_1032_, 1);
        leanh::lean_inc(v_x_1033_);
        leanh::lean_inc_ref(v_inst_1031_);
        leanh::lean_inc_ref(v_inst_1030_);
        v___x_1037_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
            v_inst_1030_,
            v_inst_1031_,
            v_map_u2081_1035_,
            v_x_1033_,
        );
        if leanh::lean_obj_tag(v___x_1037_) == 0 {
            let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1038_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                v_inst_1030_,
                v_inst_1031_,
                v_map_u2082_1036_,
                v_x_1033_,
            );
            return v___x_1038_;
        } else {
            leanh::lean_dec(v_x_1033_);
            leanh::lean_dec_ref(v_inst_1031_);
            leanh::lean_dec_ref(v_inst_1030_);
            return v___x_1037_;
        }
    } else {
        let mut v_map_u2081_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_1039_ = leanh::lean_ctor_get(v_x_1032_, 0);
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
    mut v_inst_1041_: *mut leanh::LeanObject,
    mut v_inst_1042_: *mut leanh::LeanObject,
    mut v_x_1043_: *mut leanh::LeanObject,
    mut v_x_1044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1045_ =
        l_Lean_SMap_find_x3f_x27___redArg(v_inst_1041_, v_inst_1042_, v_x_1043_, v_x_1044_);
    leanh::lean_dec_ref(v_x_1043_);
    return v_res_1045_;
}
pub unsafe fn l_Lean_SMap_find_x3f_x27(
    mut v_00_u03b1_1046_: *mut leanh::LeanObject,
    mut v_00_u03b2_1047_: *mut leanh::LeanObject,
    mut v_inst_1048_: *mut leanh::LeanObject,
    mut v_inst_1049_: *mut leanh::LeanObject,
    mut v_x_1050_: *mut leanh::LeanObject,
    mut v_x_1051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1052_ =
        l_Lean_SMap_find_x3f_x27___redArg(v_inst_1048_, v_inst_1049_, v_x_1050_, v_x_1051_);
    return v___x_1052_;
}
pub unsafe fn l_Lean_SMap_find_x3f_x27___boxed(
    mut v_00_u03b1_1053_: *mut leanh::LeanObject,
    mut v_00_u03b2_1054_: *mut leanh::LeanObject,
    mut v_inst_1055_: *mut leanh::LeanObject,
    mut v_inst_1056_: *mut leanh::LeanObject,
    mut v_x_1057_: *mut leanh::LeanObject,
    mut v_x_1058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1059_ = l_Lean_SMap_find_x3f_x27(
        v_00_u03b1_1053_,
        v_00_u03b2_1054_,
        v_inst_1055_,
        v_inst_1056_,
        v_x_1057_,
        v_x_1058_,
    );
    leanh::lean_dec_ref(v_x_1057_);
    return v_res_1059_;
}
pub unsafe fn l_Lean_SMap_forM___redArg___lam__0(
    mut v_inst_1060_: *mut leanh::LeanObject,
    mut v_map_u2082_1061_: *mut leanh::LeanObject,
    mut v_f_1062_: *mut leanh::LeanObject,
    mut v_____r_1063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ =
        l_Lean_PersistentHashMap_forM___redArg(v_inst_1060_, v_map_u2082_1061_, v_f_1062_);
    return v___x_1064_;
}
pub unsafe fn l_Lean_SMap_forM___redArg___lam__1(
    mut v_f_1065_: *mut leanh::LeanObject,
    mut v_x_1066_: *mut leanh::LeanObject,
    mut v___y_1067_: *mut leanh::LeanObject,
    mut v___y_1068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1069_ = leanh::lean_apply_2(v_f_1065_, v___y_1067_, v___y_1068_);
    return v___x_1069_;
}
pub unsafe fn l_Lean_SMap_forM___redArg___lam__2(
    mut v_inst_1070_: *mut leanh::LeanObject,
    mut v___f_1071_: *mut leanh::LeanObject,
    mut v_x_1072_: *mut leanh::LeanObject,
    mut v___y_1073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ = leanh::lean_box(0);
    v___x_1075_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1070_,
        v___f_1071_,
        v___x_1074_,
        v___y_1073_,
    );
    return v___x_1075_;
}
pub unsafe fn l_Lean_SMap_forM___redArg(
    mut v_inst_1076_: *mut leanh::LeanObject,
    mut v_s_1077_: *mut leanh::LeanObject,
    mut v_f_1078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_u2081_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: u8 = 0;
    v_map_u2081_1079_ = leanh::lean_ctor_get(v_s_1077_, 0);
    leanh::lean_inc_ref(v_map_u2081_1079_);
    v_toApplicative_1080_ = leanh::lean_ctor_get(v_inst_1076_, 0);
    v_toBind_1081_ = leanh::lean_ctor_get(v_inst_1076_, 1);
    leanh::lean_inc(v_toBind_1081_);
    v_map_u2082_1082_ = leanh::lean_ctor_get(v_s_1077_, 1);
    leanh::lean_inc_ref(v_map_u2082_1082_);
    leanh::lean_dec_ref(v_s_1077_);
    v_buckets_1083_ = leanh::lean_ctor_get(v_map_u2081_1079_, 1);
    leanh::lean_inc_ref(v_buckets_1083_);
    leanh::lean_dec_ref(v_map_u2081_1079_);
    leanh::lean_inc(v_f_1078_);
    leanh::lean_inc_ref(v_inst_1076_);
    v___f_1084_ = leanh::lean_alloc_closure(
        l_Lean_SMap_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1084_, 0, v_inst_1076_);
    leanh::lean_closure_set(v___f_1084_, 1, v_map_u2082_1082_);
    leanh::lean_closure_set(v___f_1084_, 2, v_f_1078_);
    v___x_1085_ = leanh::lean_unsigned_to_nat(0);
    v___x_1086_ = lean_array_get_size(v_buckets_1083_);
    v___x_1087_ = leanh::lean_box(0);
    v___x_1088_ = lean_nat_dec_lt(v___x_1085_, v___x_1086_);
    if v___x_1088_ == 0 {
        let mut v_toPure_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_toApplicative_1080_);
        leanh::lean_dec_ref(v_buckets_1083_);
        leanh::lean_dec(v_f_1078_);
        leanh::lean_dec_ref(v_inst_1076_);
        v_toPure_1089_ = leanh::lean_ctor_get(v_toApplicative_1080_, 1);
        leanh::lean_inc(v_toPure_1089_);
        leanh::lean_dec_ref(v_toApplicative_1080_);
        v___x_1090_ =
            leanh::lean_apply_2(v_toPure_1089_, leanh::lean_box(0), v___x_1087_);
        v___x_1091_ = leanh::lean_apply_4(
            v_toBind_1081_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1090_,
            v___f_1084_,
        );
        return v___x_1091_;
    } else {
        let mut v___f_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1094_: u8 = 0;
        v___f_1092_ = leanh::lean_alloc_closure(
            l_Lean_SMap_forM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_1092_, 0, v_f_1078_);
        leanh::lean_inc_ref(v_inst_1076_);
        v___f_1093_ = leanh::lean_alloc_closure(
            l_Lean_SMap_forM___redArg___lam__2 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_1093_, 0, v_inst_1076_);
        leanh::lean_closure_set(v___f_1093_, 1, v___f_1092_);
        v___x_1094_ = lean_nat_dec_le(v___x_1086_, v___x_1086_);
        if v___x_1094_ == 0 {
            if v___x_1088_ == 0 {
                let mut v_toPure_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc_ref(v_toApplicative_1080_);
                leanh::lean_dec_ref(v___f_1093_);
                leanh::lean_dec_ref(v_buckets_1083_);
                leanh::lean_dec_ref(v_inst_1076_);
                v_toPure_1095_ = leanh::lean_ctor_get(v_toApplicative_1080_, 1);
                leanh::lean_inc(v_toPure_1095_);
                leanh::lean_dec_ref(v_toApplicative_1080_);
                v___x_1096_ = leanh::lean_apply_2(
                    v_toPure_1095_,
                    leanh::lean_box(0),
                    v___x_1087_,
                );
                v___x_1097_ = leanh::lean_apply_4(
                    v_toBind_1081_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1096_,
                    v___f_1084_,
                );
                return v___x_1097_;
            } else {
                let mut v___x_1098_: usize = 0;
                let mut v___x_1099_: usize = 0;
                let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1098_ = 0usize;
                v___x_1099_ = lean_usize_of_nat(v___x_1086_);
                v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_1076_,
                    v___f_1093_,
                    v_buckets_1083_,
                    v___x_1098_,
                    v___x_1099_,
                    v___x_1087_,
                );
                v___x_1101_ = leanh::lean_apply_4(
                    v_toBind_1081_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1100_,
                    v___f_1084_,
                );
                return v___x_1101_;
            }
        } else {
            let mut v___x_1102_: usize = 0;
            let mut v___x_1103_: usize = 0;
            let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1102_ = 0usize;
            v___x_1103_ = lean_usize_of_nat(v___x_1086_);
            v___x_1104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1076_,
                v___f_1093_,
                v_buckets_1083_,
                v___x_1102_,
                v___x_1103_,
                v___x_1087_,
            );
            v___x_1105_ = leanh::lean_apply_4(
                v_toBind_1081_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1104_,
                v___f_1084_,
            );
            return v___x_1105_;
        }
    }
}
pub unsafe fn l_Lean_SMap_forM(
    mut v_00_u03b1_1106_: *mut leanh::LeanObject,
    mut v_00_u03b2_1107_: *mut leanh::LeanObject,
    mut v_inst_1108_: *mut leanh::LeanObject,
    mut v_inst_1109_: *mut leanh::LeanObject,
    mut v_m_1110_: *mut leanh::LeanObject,
    mut v_inst_1111_: *mut leanh::LeanObject,
    mut v_s_1112_: *mut leanh::LeanObject,
    mut v_f_1113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1114_ = l_Lean_SMap_forM___redArg(v_inst_1111_, v_s_1112_, v_f_1113_);
    return v___x_1114_;
}
pub unsafe fn l_Lean_SMap_forM___boxed(
    mut v_00_u03b1_1115_: *mut leanh::LeanObject,
    mut v_00_u03b2_1116_: *mut leanh::LeanObject,
    mut v_inst_1117_: *mut leanh::LeanObject,
    mut v_inst_1118_: *mut leanh::LeanObject,
    mut v_m_1119_: *mut leanh::LeanObject,
    mut v_inst_1120_: *mut leanh::LeanObject,
    mut v_s_1121_: *mut leanh::LeanObject,
    mut v_f_1122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_1118_);
    leanh::lean_dec_ref(v_inst_1117_);
    return v_res_1123_;
}
pub unsafe fn l_Lean_SMap_instForMProdOfMonad___redArg___lam__0(
    mut v_f_1124_: *mut leanh::LeanObject,
    mut v_x_1125_: *mut leanh::LeanObject,
    mut v_y_1126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1127_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1127_, 0, v_x_1125_);
    leanh::lean_ctor_set(v___x_1127_, 1, v_y_1126_);
    v___x_1128_ = leanh::lean_apply_1(v_f_1124_, v___x_1127_);
    return v___x_1128_;
}
pub unsafe fn l_Lean_SMap_instForMProdOfMonad___redArg___lam__1(
    mut v_inst_1129_: *mut leanh::LeanObject,
    mut v_s_1130_: *mut leanh::LeanObject,
    mut v_f_1131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1132_ = leanh::lean_alloc_closure(
        l_Lean_SMap_instForMProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1132_, 0, v_f_1131_);
    v___x_1133_ = l_Lean_SMap_forM___redArg(v_inst_1129_, v_s_1130_, v___f_1132_);
    return v___x_1133_;
}
pub unsafe fn l_Lean_SMap_instForMProdOfMonad___redArg(
    mut v_inst_1134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1135_ = leanh::lean_alloc_closure(
        l_Lean_SMap_instForMProdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1135_, 0, v_inst_1134_);
    return v___f_1135_;
}
pub unsafe fn l_Lean_SMap_instForMProdOfMonad(
    mut v_00_u03b1_1136_: *mut leanh::LeanObject,
    mut v_00_u03b2_1137_: *mut leanh::LeanObject,
    mut v_inst_1138_: *mut leanh::LeanObject,
    mut v_inst_1139_: *mut leanh::LeanObject,
    mut v_m_1140_: *mut leanh::LeanObject,
    mut v_inst_1141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1142_ = leanh::lean_alloc_closure(
        l_Lean_SMap_instForMProdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1142_, 0, v_inst_1141_);
    return v___f_1142_;
}
pub unsafe fn l_Lean_SMap_instForMProdOfMonad___boxed(
    mut v_00_u03b1_1143_: *mut leanh::LeanObject,
    mut v_00_u03b2_1144_: *mut leanh::LeanObject,
    mut v_inst_1145_: *mut leanh::LeanObject,
    mut v_inst_1146_: *mut leanh::LeanObject,
    mut v_m_1147_: *mut leanh::LeanObject,
    mut v_inst_1148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1149_ = l_Lean_SMap_instForMProdOfMonad(
        v_00_u03b1_1143_,
        v_00_u03b2_1144_,
        v_inst_1145_,
        v_inst_1146_,
        v_m_1147_,
        v_inst_1148_,
    );
    leanh::lean_dec_ref(v_inst_1146_);
    leanh::lean_dec_ref(v_inst_1145_);
    return v_res_1149_;
}
pub unsafe fn l_Lean_SMap_instForInProdOfMonad___redArg___lam__0(
    mut v_toPure_1150_: *mut leanh::LeanObject,
    mut v_____do__lift_1151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1151_) == 0 {
        let mut v_a_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1152_ = leanh::lean_ctor_get(v_____do__lift_1151_, 0);
        leanh::lean_inc(v_a_1152_);
        leanh::lean_dec_ref_known(v_____do__lift_1151_, 1);
        v___x_1153_ =
            leanh::lean_apply_2(v_toPure_1150_, leanh::lean_box(0), v_a_1152_);
        return v___x_1153_;
    } else {
        let mut v_a_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1154_ = leanh::lean_ctor_get(v_____do__lift_1151_, 0);
        leanh::lean_inc(v_a_1154_);
        leanh::lean_dec_ref_known(v_____do__lift_1151_, 1);
        v_snd_1155_ = leanh::lean_ctor_get(v_a_1154_, 1);
        leanh::lean_inc(v_snd_1155_);
        leanh::lean_dec(v_a_1154_);
        v___x_1156_ =
            leanh::lean_apply_2(v_toPure_1150_, leanh::lean_box(0), v_snd_1155_);
        return v___x_1156_;
    }
}
pub unsafe fn l_Lean_SMap_instForInProdOfMonad___redArg___lam__1(
    mut v_toPure_1157_: *mut leanh::LeanObject,
    mut v_____do__lift_1158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1162_: u8 = 0;
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1167_: u8 = 0;
    let mut v_a_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1171_: u8 = 0;
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_1158_) == 0 {
                    v_a_1159_ = leanh::lean_ctor_get(v_____do__lift_1158_, 0);
                    v_isSharedCheck_1167_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_1158_)) as u8;
                    if v_isSharedCheck_1167_ == 0 {
                        v___x_1161_ = v_____do__lift_1158_;
                        v_isShared_1162_ = v_isSharedCheck_1167_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1159_);
                        leanh::lean_dec(v_____do__lift_1158_);
                        v___x_1161_ = leanh::lean_box(0);
                        v_isShared_1162_ = v_isSharedCheck_1167_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1168_ = leanh::lean_ctor_get(v_____do__lift_1158_, 0);
                    v_isSharedCheck_1178_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_1158_)) as u8;
                    if v_isSharedCheck_1178_ == 0 {
                        v___x_1170_ = v_____do__lift_1158_;
                        v_isShared_1171_ = v_isSharedCheck_1178_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1168_);
                        leanh::lean_dec(v_____do__lift_1158_);
                        v___x_1170_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1166_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1159_);
                    v___x_1164_ = v_reuseFailAlloc_1166_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1165_ = leanh::lean_apply_2(
                    v_toPure_1157_,
                    leanh::lean_box(0),
                    v___x_1164_,
                );
                return v___x_1165_;
            }
            3 => {
                v___x_1172_ = leanh::lean_box(0);
                v___x_1173_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1173_, 0, v___x_1172_);
                leanh::lean_ctor_set(v___x_1173_, 1, v_a_1168_);
                if v_isShared_1171_ == 0 {
                    leanh::lean_ctor_set(v___x_1170_, 0, v___x_1173_);
                    v___x_1175_ = v___x_1170_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1177_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1173_);
                    v___x_1175_ = v_reuseFailAlloc_1177_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1176_ = leanh::lean_apply_2(
                    v_toPure_1157_,
                    leanh::lean_box(0),
                    v___x_1175_,
                );
                return v___x_1176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_instForInProdOfMonad___redArg___lam__2(
    mut v___y_1179_: *mut leanh::LeanObject,
    mut v_toBind_1180_: *mut leanh::LeanObject,
    mut v___f_1181_: *mut leanh::LeanObject,
    mut v_x_1182_: *mut leanh::LeanObject,
    mut v_y_1183_: *mut leanh::LeanObject,
    mut v___y_1184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1185_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1185_, 0, v_x_1182_);
    leanh::lean_ctor_set(v___x_1185_, 1, v_y_1183_);
    v___x_1186_ = leanh::lean_apply_2(v___y_1179_, v___x_1185_, v___y_1184_);
    v___x_1187_ = leanh::lean_apply_4(
        v_toBind_1180_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1186_,
        v___f_1181_,
    );
    return v___x_1187_;
}
pub unsafe fn l_Lean_SMap_instForInProdOfMonad___redArg___lam__3(
    mut v_inst_1188_: *mut leanh::LeanObject,
    mut v_00_u03b2_1189_: *mut leanh::LeanObject,
    mut v___y_1190_: *mut leanh::LeanObject,
    mut v___y_1191_: *mut leanh::LeanObject,
    mut v___y_1192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140__overap_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_1188_, 7);
    v___f_1193_ = leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1193_, 0, v_inst_1188_);
    v___f_1194_ = leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1194_, 0, v_inst_1188_);
    v___f_1195_ = leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1195_, 0, v_inst_1188_);
    v___f_1196_ = leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1196_, 0, v_inst_1188_);
    v___x_1197_ = leanh::lean_alloc_closure(l_ExceptT_map as *mut core::ffi::c_void, 7, 3);
    leanh::lean_closure_set(v___x_1197_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1197_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1197_, 2, v_inst_1188_);
    v___x_1198_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1198_, 0, v___x_1197_);
    leanh::lean_ctor_set(v___x_1198_, 1, v___f_1193_);
    v___x_1199_ = leanh::lean_alloc_closure(l_ExceptT_pure as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_1199_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1199_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1199_, 2, v_inst_1188_);
    v___x_1200_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1200_, 0, v___x_1198_);
    leanh::lean_ctor_set(v___x_1200_, 1, v___x_1199_);
    leanh::lean_ctor_set(v___x_1200_, 2, v___f_1194_);
    leanh::lean_ctor_set(v___x_1200_, 3, v___f_1195_);
    leanh::lean_ctor_set(v___x_1200_, 4, v___f_1196_);
    v___x_1201_ = leanh::lean_alloc_closure(l_ExceptT_bind as *mut core::ffi::c_void, 7, 3);
    leanh::lean_closure_set(v___x_1201_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1201_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1201_, 2, v_inst_1188_);
    v___x_1202_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1202_, 0, v___x_1200_);
    leanh::lean_ctor_set(v___x_1202_, 1, v___x_1201_);
    leanh::lean_inc_ref_n(v___x_1202_, 6);
    v___f_1203_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1203_, 0, v___x_1202_);
    v___f_1204_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1204_, 0, v___x_1202_);
    v___f_1205_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1205_, 0, v___x_1202_);
    v___f_1206_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1206_, 0, v___x_1202_);
    v___x_1207_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_1207_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1207_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1207_, 2, v___x_1202_);
    v___x_1208_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1208_, 0, v___x_1207_);
    leanh::lean_ctor_set(v___x_1208_, 1, v___f_1203_);
    v___x_1209_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_1209_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1209_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1209_, 2, v___x_1202_);
    v___x_1210_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1210_, 0, v___x_1208_);
    leanh::lean_ctor_set(v___x_1210_, 1, v___x_1209_);
    leanh::lean_ctor_set(v___x_1210_, 2, v___f_1204_);
    leanh::lean_ctor_set(v___x_1210_, 3, v___f_1205_);
    leanh::lean_ctor_set(v___x_1210_, 4, v___f_1206_);
    v___x_1211_ = leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_1211_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1211_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1211_, 2, v___x_1202_);
    v___x_1212_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1212_, 0, v___x_1210_);
    leanh::lean_ctor_set(v___x_1212_, 1, v___x_1211_);
    v_toApplicative_1213_ = leanh::lean_ctor_get(v_inst_1188_, 0);
    leanh::lean_inc_ref(v_toApplicative_1213_);
    v_toBind_1214_ = leanh::lean_ctor_get(v_inst_1188_, 1);
    leanh::lean_inc_n(v_toBind_1214_, 2);
    leanh::lean_dec_ref(v_inst_1188_);
    v_toPure_1215_ = leanh::lean_ctor_get(v_toApplicative_1213_, 1);
    leanh::lean_inc_n(v_toPure_1215_, 2);
    leanh::lean_dec_ref(v_toApplicative_1213_);
    v___f_1216_ = leanh::lean_alloc_closure(
        l_Lean_SMap_instForInProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1216_, 0, v_toPure_1215_);
    v___f_1217_ = leanh::lean_alloc_closure(
        l_Lean_SMap_instForInProdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1217_, 0, v_toPure_1215_);
    v___f_1218_ = leanh::lean_alloc_closure(
        l_Lean_SMap_instForInProdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_1218_, 0, v___y_1192_);
    leanh::lean_closure_set(v___f_1218_, 1, v_toBind_1214_);
    leanh::lean_closure_set(v___f_1218_, 2, v___f_1217_);
    v___x_140__overap_1219_ = l_Lean_SMap_forM___redArg(v___x_1212_, v___y_1190_, v___f_1218_);
    v___x_1220_ = leanh::lean_apply_1(v___x_140__overap_1219_, v___y_1191_);
    v___x_1221_ = leanh::lean_apply_4(
        v_toBind_1214_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1220_,
        v___f_1216_,
    );
    return v___x_1221_;
}
pub unsafe fn l_Lean_SMap_instForInProdOfMonad___redArg(
    mut v_inst_1222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1223_ = leanh::lean_alloc_closure(
        l_Lean_SMap_instForInProdOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1223_, 0, v_inst_1222_);
    return v___f_1223_;
}
pub unsafe fn l_Lean_SMap_instForInProdOfMonad(
    mut v_00_u03b1_1224_: *mut leanh::LeanObject,
    mut v_00_u03b2_1225_: *mut leanh::LeanObject,
    mut v_inst_1226_: *mut leanh::LeanObject,
    mut v_inst_1227_: *mut leanh::LeanObject,
    mut v_m_1228_: *mut leanh::LeanObject,
    mut v_inst_1229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1230_ = leanh::lean_alloc_closure(
        l_Lean_SMap_instForInProdOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1230_, 0, v_inst_1229_);
    return v___f_1230_;
}
pub unsafe fn l_Lean_SMap_instForInProdOfMonad___boxed(
    mut v_00_u03b1_1231_: *mut leanh::LeanObject,
    mut v_00_u03b2_1232_: *mut leanh::LeanObject,
    mut v_inst_1233_: *mut leanh::LeanObject,
    mut v_inst_1234_: *mut leanh::LeanObject,
    mut v_m_1235_: *mut leanh::LeanObject,
    mut v_inst_1236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1237_ = l_Lean_SMap_instForInProdOfMonad(
        v_00_u03b1_1231_,
        v_00_u03b2_1232_,
        v_inst_1233_,
        v_inst_1234_,
        v_m_1235_,
        v_inst_1236_,
    );
    leanh::lean_dec_ref(v_inst_1234_);
    leanh::lean_dec_ref(v_inst_1233_);
    return v_res_1237_;
}
pub unsafe fn l_Lean_SMap_iter___redArg(
    mut v_s_1238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_u2081_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1244_: u8 = 0;
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1254_: u8 = 0;
    let mut v_unused_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_u2081_1239_ = leanh::lean_ctor_get(v_s_1238_, 0);
                leanh::lean_inc_ref(v_map_u2081_1239_);
                v_map_u2082_1240_ = leanh::lean_ctor_get(v_s_1238_, 1);
                leanh::lean_inc_ref(v_map_u2082_1240_);
                leanh::lean_dec_ref(v_s_1238_);
                v_buckets_1241_ = leanh::lean_ctor_get(v_map_u2081_1239_, 1);
                v_isSharedCheck_1254_ = (!leanh::lean_is_exclusive(v_map_u2081_1239_)) as u8;
                if v_isSharedCheck_1254_ == 0 {
                    v_unused_1255_ = leanh::lean_ctor_get(v_map_u2081_1239_, 0);
                    leanh::lean_dec(v_unused_1255_);
                    v___x_1243_ = v_map_u2081_1239_;
                    v_isShared_1244_ = v_isSharedCheck_1254_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1241_);
                    leanh::lean_dec(v_map_u2081_1239_);
                    v___x_1243_ = leanh::lean_box(0);
                    v_isShared_1244_ = v_isSharedCheck_1254_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1245_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_1244_ == 0 {
                    leanh::lean_ctor_set(v___x_1243_, 1, v___x_1245_);
                    leanh::lean_ctor_set(v___x_1243_, 0, v_buckets_1241_);
                    v___x_1247_ = v___x_1243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1253_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_buckets_1241_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___x_1245_);
                    v___x_1247_ = v_reuseFailAlloc_1253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1248_ = leanh::lean_box(0);
                v___x_1249_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1249_, 0, v___x_1247_);
                leanh::lean_ctor_set(v___x_1249_, 1, v___x_1248_);
                v___x_1250_ = leanh::lean_box(0);
                v___x_1251_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(
                    v_map_u2082_1240_,
                    v___x_1250_,
                );
                v___x_1252_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1252_, 0, v___x_1249_);
                leanh::lean_ctor_set(v___x_1252_, 1, v___x_1251_);
                return v___x_1252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_iter(
    mut v_00_u03b1_1256_: *mut leanh::LeanObject,
    mut v_00_u03b2_1257_: *mut leanh::LeanObject,
    mut v_inst_1258_: *mut leanh::LeanObject,
    mut v_inst_1259_: *mut leanh::LeanObject,
    mut v_s_1260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = l_Lean_SMap_iter___redArg(v_s_1260_);
    return v___x_1261_;
}
pub unsafe fn l_Lean_SMap_iter___boxed(
    mut v_00_u03b1_1262_: *mut leanh::LeanObject,
    mut v_00_u03b2_1263_: *mut leanh::LeanObject,
    mut v_inst_1264_: *mut leanh::LeanObject,
    mut v_inst_1265_: *mut leanh::LeanObject,
    mut v_s_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_Lean_SMap_iter(
        v_00_u03b1_1262_,
        v_00_u03b2_1263_,
        v_inst_1264_,
        v_inst_1265_,
        v_s_1266_,
    );
    leanh::lean_dec_ref(v_inst_1265_);
    leanh::lean_dec_ref(v_inst_1264_);
    return v_res_1267_;
}
pub unsafe fn l_Lean_SMap_switch___redArg(
    mut v_m_1268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_1269_: u8 = 0;
    let mut v_map_u2081_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1274_: u8 = 0;
    let mut v___x_1275_: u8 = 0;
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_1269_ = leanh::lean_ctor_get_uint8(
                    v_m_1268_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_1269_ == 0 {
                    return v_m_1268_;
                } else {
                    v_map_u2081_1270_ = leanh::lean_ctor_get(v_m_1268_, 0);
                    v_map_u2082_1271_ = leanh::lean_ctor_get(v_m_1268_, 1);
                    v_isSharedCheck_1279_ = (!leanh::lean_is_exclusive(v_m_1268_)) as u8;
                    if v_isSharedCheck_1279_ == 0 {
                        v___x_1273_ = v_m_1268_;
                        v_isShared_1274_ = v_isSharedCheck_1279_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_1271_);
                        leanh::lean_inc(v_map_u2081_1270_);
                        leanh::lean_dec(v_m_1268_);
                        v___x_1273_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1278_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_map_u2081_1270_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_map_u2082_1271_);
                    v___x_1277_ = v_reuseFailAlloc_1278_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1277_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_1275_,
                );
                return v___x_1277_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_switch(
    mut v_00_u03b1_1280_: *mut leanh::LeanObject,
    mut v_00_u03b2_1281_: *mut leanh::LeanObject,
    mut v_inst_1282_: *mut leanh::LeanObject,
    mut v_inst_1283_: *mut leanh::LeanObject,
    mut v_m_1284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ = l_Lean_SMap_switch___redArg(v_m_1284_);
    return v___x_1285_;
}
pub unsafe fn l_Lean_SMap_switch___boxed(
    mut v_00_u03b1_1286_: *mut leanh::LeanObject,
    mut v_00_u03b2_1287_: *mut leanh::LeanObject,
    mut v_inst_1288_: *mut leanh::LeanObject,
    mut v_inst_1289_: *mut leanh::LeanObject,
    mut v_m_1290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1291_ = l_Lean_SMap_switch(
        v_00_u03b1_1286_,
        v_00_u03b2_1287_,
        v_inst_1288_,
        v_inst_1289_,
        v_m_1290_,
    );
    leanh::lean_dec_ref(v_inst_1289_);
    leanh::lean_dec_ref(v_inst_1288_);
    return v_res_1291_;
}
pub unsafe fn l_Lean_SMap_foldStage2___redArg(
    mut v_f_1292_: *mut leanh::LeanObject,
    mut v_s_1293_: *mut leanh::LeanObject,
    mut v_m_1294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_u2082_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_u2082_1295_ = leanh::lean_ctor_get(v_m_1294_, 1);
    leanh::lean_inc_ref(v_map_u2082_1295_);
    leanh::lean_dec_ref(v_m_1294_);
    v___x_1296_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_1295_, v_f_1292_, v_s_1293_);
    return v___x_1296_;
}
pub unsafe fn l_Lean_SMap_foldStage2(
    mut v_00_u03b1_1297_: *mut leanh::LeanObject,
    mut v_00_u03b2_1298_: *mut leanh::LeanObject,
    mut v_inst_1299_: *mut leanh::LeanObject,
    mut v_inst_1300_: *mut leanh::LeanObject,
    mut v_00_u03c3_1301_: *mut leanh::LeanObject,
    mut v_f_1302_: *mut leanh::LeanObject,
    mut v_s_1303_: *mut leanh::LeanObject,
    mut v_m_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_u2082_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_u2082_1305_ = leanh::lean_ctor_get(v_m_1304_, 1);
    leanh::lean_inc_ref(v_map_u2082_1305_);
    leanh::lean_dec_ref(v_m_1304_);
    v___x_1306_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_1305_, v_f_1302_, v_s_1303_);
    return v___x_1306_;
}
pub unsafe fn l_Lean_SMap_foldStage2___boxed(
    mut v_00_u03b1_1307_: *mut leanh::LeanObject,
    mut v_00_u03b2_1308_: *mut leanh::LeanObject,
    mut v_inst_1309_: *mut leanh::LeanObject,
    mut v_inst_1310_: *mut leanh::LeanObject,
    mut v_00_u03c3_1311_: *mut leanh::LeanObject,
    mut v_f_1312_: *mut leanh::LeanObject,
    mut v_s_1313_: *mut leanh::LeanObject,
    mut v_m_1314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_1310_);
    leanh::lean_dec_ref(v_inst_1309_);
    return v_res_1315_;
}
pub unsafe fn l_Lean_SMap_foldM___redArg___lam__0(
    mut v_inst_1316_: *mut leanh::LeanObject,
    mut v_f_1317_: *mut leanh::LeanObject,
    mut v_map_u2082_1318_: *mut leanh::LeanObject,
    mut v_____do__lift_1319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1320_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v_inst_1316_,
        v_f_1317_,
        v_map_u2082_1318_,
        v_____do__lift_1319_,
    );
    return v___x_1320_;
}
pub unsafe fn l_Lean_SMap_foldM___redArg___lam__1(
    mut v_inst_1321_: *mut leanh::LeanObject,
    mut v_f_1322_: *mut leanh::LeanObject,
    mut v_acc_1323_: *mut leanh::LeanObject,
    mut v_l_1324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1325_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1321_,
        v_f_1322_,
        v_acc_1323_,
        v_l_1324_,
    );
    return v___x_1325_;
}
pub unsafe fn l_Lean_SMap_foldM___redArg(
    mut v_inst_1326_: *mut leanh::LeanObject,
    mut v_f_1327_: *mut leanh::LeanObject,
    mut v_init_1328_: *mut leanh::LeanObject,
    mut v_map_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_u2081_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: u8 = 0;
    v_map_u2081_1330_ = leanh::lean_ctor_get(v_map_1329_, 0);
    leanh::lean_inc_ref(v_map_u2081_1330_);
    v_toApplicative_1331_ = leanh::lean_ctor_get(v_inst_1326_, 0);
    v_toBind_1332_ = leanh::lean_ctor_get(v_inst_1326_, 1);
    leanh::lean_inc(v_toBind_1332_);
    v_map_u2082_1333_ = leanh::lean_ctor_get(v_map_1329_, 1);
    leanh::lean_inc_ref(v_map_u2082_1333_);
    leanh::lean_dec_ref(v_map_1329_);
    v_buckets_1334_ = leanh::lean_ctor_get(v_map_u2081_1330_, 1);
    leanh::lean_inc_ref(v_buckets_1334_);
    leanh::lean_dec_ref(v_map_u2081_1330_);
    leanh::lean_inc(v_f_1327_);
    leanh::lean_inc_ref(v_inst_1326_);
    v___f_1335_ = leanh::lean_alloc_closure(
        l_Lean_SMap_foldM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1335_, 0, v_inst_1326_);
    leanh::lean_closure_set(v___f_1335_, 1, v_f_1327_);
    leanh::lean_closure_set(v___f_1335_, 2, v_map_u2082_1333_);
    v___x_1336_ = leanh::lean_unsigned_to_nat(0);
    v___x_1337_ = lean_array_get_size(v_buckets_1334_);
    v___x_1338_ = lean_nat_dec_lt(v___x_1336_, v___x_1337_);
    if v___x_1338_ == 0 {
        let mut v_toPure_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_toApplicative_1331_);
        leanh::lean_dec_ref(v_buckets_1334_);
        leanh::lean_dec(v_f_1327_);
        leanh::lean_dec_ref(v_inst_1326_);
        v_toPure_1339_ = leanh::lean_ctor_get(v_toApplicative_1331_, 1);
        leanh::lean_inc(v_toPure_1339_);
        leanh::lean_dec_ref(v_toApplicative_1331_);
        v___x_1340_ =
            leanh::lean_apply_2(v_toPure_1339_, leanh::lean_box(0), v_init_1328_);
        v___x_1341_ = leanh::lean_apply_4(
            v_toBind_1332_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1340_,
            v___f_1335_,
        );
        return v___x_1341_;
    } else {
        let mut v___f_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1343_: u8 = 0;
        leanh::lean_inc_ref(v_inst_1326_);
        v___f_1342_ = leanh::lean_alloc_closure(
            l_Lean_SMap_foldM___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_1342_, 0, v_inst_1326_);
        leanh::lean_closure_set(v___f_1342_, 1, v_f_1327_);
        v___x_1343_ = lean_nat_dec_le(v___x_1337_, v___x_1337_);
        if v___x_1343_ == 0 {
            if v___x_1338_ == 0 {
                let mut v_toPure_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc_ref(v_toApplicative_1331_);
                leanh::lean_dec_ref(v___f_1342_);
                leanh::lean_dec_ref(v_buckets_1334_);
                leanh::lean_dec_ref(v_inst_1326_);
                v_toPure_1344_ = leanh::lean_ctor_get(v_toApplicative_1331_, 1);
                leanh::lean_inc(v_toPure_1344_);
                leanh::lean_dec_ref(v_toApplicative_1331_);
                v___x_1345_ = leanh::lean_apply_2(
                    v_toPure_1344_,
                    leanh::lean_box(0),
                    v_init_1328_,
                );
                v___x_1346_ = leanh::lean_apply_4(
                    v_toBind_1332_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1345_,
                    v___f_1335_,
                );
                return v___x_1346_;
            } else {
                let mut v___x_1347_: usize = 0;
                let mut v___x_1348_: usize = 0;
                let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1347_ = 0usize;
                v___x_1348_ = lean_usize_of_nat(v___x_1337_);
                v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_1326_,
                    v___f_1342_,
                    v_buckets_1334_,
                    v___x_1347_,
                    v___x_1348_,
                    v_init_1328_,
                );
                v___x_1350_ = leanh::lean_apply_4(
                    v_toBind_1332_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1349_,
                    v___f_1335_,
                );
                return v___x_1350_;
            }
        } else {
            let mut v___x_1351_: usize = 0;
            let mut v___x_1352_: usize = 0;
            let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1351_ = 0usize;
            v___x_1352_ = lean_usize_of_nat(v___x_1337_);
            v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1326_,
                v___f_1342_,
                v_buckets_1334_,
                v___x_1351_,
                v___x_1352_,
                v_init_1328_,
            );
            v___x_1354_ = leanh::lean_apply_4(
                v_toBind_1332_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1353_,
                v___f_1335_,
            );
            return v___x_1354_;
        }
    }
}
pub unsafe fn l_Lean_SMap_foldM(
    mut v_00_u03b1_1355_: *mut leanh::LeanObject,
    mut v_00_u03b2_1356_: *mut leanh::LeanObject,
    mut v_inst_1357_: *mut leanh::LeanObject,
    mut v_inst_1358_: *mut leanh::LeanObject,
    mut v_00_u03c3_1359_: *mut leanh::LeanObject,
    mut v_m_1360_: *mut leanh::LeanObject,
    mut v_inst_1361_: *mut leanh::LeanObject,
    mut v_f_1362_: *mut leanh::LeanObject,
    mut v_init_1363_: *mut leanh::LeanObject,
    mut v_map_1364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1365_ = l_Lean_SMap_foldM___redArg(v_inst_1361_, v_f_1362_, v_init_1363_, v_map_1364_);
    return v___x_1365_;
}
pub unsafe fn l_Lean_SMap_foldM___boxed(
    mut v_00_u03b1_1366_: *mut leanh::LeanObject,
    mut v_00_u03b2_1367_: *mut leanh::LeanObject,
    mut v_inst_1368_: *mut leanh::LeanObject,
    mut v_inst_1369_: *mut leanh::LeanObject,
    mut v_00_u03c3_1370_: *mut leanh::LeanObject,
    mut v_m_1371_: *mut leanh::LeanObject,
    mut v_inst_1372_: *mut leanh::LeanObject,
    mut v_f_1373_: *mut leanh::LeanObject,
    mut v_init_1374_: *mut leanh::LeanObject,
    mut v_map_1375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_1369_);
    leanh::lean_dec_ref(v_inst_1368_);
    return v_res_1376_;
}
pub unsafe fn l_Lean_SMap_fold___redArg___lam__0(
    mut v_f_1377_: *mut leanh::LeanObject,
    mut v_x1_1378_: *mut leanh::LeanObject,
    mut v_x2_1379_: *mut leanh::LeanObject,
    mut v_x3_1380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1381_ = leanh::lean_apply_3(v_f_1377_, v_x1_1378_, v_x2_1379_, v_x3_1380_);
    return v___x_1381_;
}
pub unsafe fn l_Lean_SMap_fold___redArg___lam__1(
    mut v___x_1382_: *mut leanh::LeanObject,
    mut v___f_1383_: *mut leanh::LeanObject,
    mut v_acc_1384_: *mut leanh::LeanObject,
    mut v_l_1385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1386_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_1382_,
        v___f_1383_,
        v_acc_1384_,
        v_l_1385_,
    );
    return v___x_1386_;
}
pub unsafe fn l_Lean_SMap_fold___redArg(
    mut v_f_1406_: *mut leanh::LeanObject,
    mut v_init_1407_: *mut leanh::LeanObject,
    mut v_m_1408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_u2081_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u8 = 0;
    v_map_u2081_1409_ = leanh::lean_ctor_get(v_m_1408_, 0);
    leanh::lean_inc_ref(v_map_u2081_1409_);
    v_map_u2082_1410_ = leanh::lean_ctor_get(v_m_1408_, 1);
    leanh::lean_inc_ref(v_map_u2082_1410_);
    leanh::lean_dec_ref(v_m_1408_);
    v___x_1411_ = l_Lean_SMap_fold___redArg___closed__9;
    v_buckets_1412_ = leanh::lean_ctor_get(v_map_u2081_1409_, 1);
    leanh::lean_inc_ref(v_buckets_1412_);
    leanh::lean_dec_ref(v_map_u2081_1409_);
    v___x_1413_ = leanh::lean_unsigned_to_nat(0);
    v___x_1414_ = lean_array_get_size(v_buckets_1412_);
    v___x_1415_ = lean_nat_dec_lt(v___x_1413_, v___x_1414_);
    if v___x_1415_ == 0 {
        let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_buckets_1412_);
        v___x_1416_ =
            l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_1410_, v_f_1406_, v_init_1407_);
        return v___x_1416_;
    } else {
        let mut v___f_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1419_: u8 = 0;
        leanh::lean_inc(v_f_1406_);
        v___f_1417_ = leanh::lean_alloc_closure(
            l_Lean_SMap_fold___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_1417_, 0, v_f_1406_);
        v___f_1418_ = leanh::lean_alloc_closure(
            l_Lean_SMap_fold___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_1418_, 0, v___x_1411_);
        leanh::lean_closure_set(v___f_1418_, 1, v___f_1417_);
        v___x_1419_ = lean_nat_dec_le(v___x_1414_, v___x_1414_);
        if v___x_1419_ == 0 {
            if v___x_1415_ == 0 {
                let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_1418_);
                leanh::lean_dec_ref(v_buckets_1412_);
                v___x_1420_ = l_Lean_PersistentHashMap_foldl___redArg(
                    v_map_u2082_1410_,
                    v_f_1406_,
                    v_init_1407_,
                );
                return v___x_1420_;
            } else {
                let mut v___x_1421_: usize = 0;
                let mut v___x_1422_: usize = 0;
                let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1421_ = 0usize;
                v___x_1422_ = lean_usize_of_nat(v___x_1414_);
                v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1425_ = 0usize;
            v___x_1426_ = lean_usize_of_nat(v___x_1414_);
            v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03b1_1429_: *mut leanh::LeanObject,
    mut v_00_u03b2_1430_: *mut leanh::LeanObject,
    mut v_inst_1431_: *mut leanh::LeanObject,
    mut v_inst_1432_: *mut leanh::LeanObject,
    mut v_00_u03c3_1433_: *mut leanh::LeanObject,
    mut v_f_1434_: *mut leanh::LeanObject,
    mut v_init_1435_: *mut leanh::LeanObject,
    mut v_m_1436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1437_ = l_Lean_SMap_fold___redArg(v_f_1434_, v_init_1435_, v_m_1436_);
    return v___x_1437_;
}
pub unsafe fn l_Lean_SMap_fold___boxed(
    mut v_00_u03b1_1438_: *mut leanh::LeanObject,
    mut v_00_u03b2_1439_: *mut leanh::LeanObject,
    mut v_inst_1440_: *mut leanh::LeanObject,
    mut v_inst_1441_: *mut leanh::LeanObject,
    mut v_00_u03c3_1442_: *mut leanh::LeanObject,
    mut v_f_1443_: *mut leanh::LeanObject,
    mut v_init_1444_: *mut leanh::LeanObject,
    mut v_m_1445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_1441_);
    leanh::lean_dec_ref(v_inst_1440_);
    return v_res_1446_;
}
pub unsafe fn l_Lean_SMap_numBuckets___redArg(
    mut v_m_1447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_u2081_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_u2081_1448_ = leanh::lean_ctor_get(v_m_1447_, 0);
    v___x_1449_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_map_u2081_1448_);
    return v___x_1449_;
}
pub unsafe fn l_Lean_SMap_numBuckets___redArg___boxed(
    mut v_m_1450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1451_ = l_Lean_SMap_numBuckets___redArg(v_m_1450_);
    leanh::lean_dec_ref(v_m_1450_);
    return v_res_1451_;
}
pub unsafe fn l_Lean_SMap_numBuckets(
    mut v_00_u03b1_1452_: *mut leanh::LeanObject,
    mut v_00_u03b2_1453_: *mut leanh::LeanObject,
    mut v_inst_1454_: *mut leanh::LeanObject,
    mut v_inst_1455_: *mut leanh::LeanObject,
    mut v_m_1456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = l_Lean_SMap_numBuckets___redArg(v_m_1456_);
    return v___x_1457_;
}
pub unsafe fn l_Lean_SMap_numBuckets___boxed(
    mut v_00_u03b1_1458_: *mut leanh::LeanObject,
    mut v_00_u03b2_1459_: *mut leanh::LeanObject,
    mut v_inst_1460_: *mut leanh::LeanObject,
    mut v_inst_1461_: *mut leanh::LeanObject,
    mut v_m_1462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1463_ = l_Lean_SMap_numBuckets(
        v_00_u03b1_1458_,
        v_00_u03b2_1459_,
        v_inst_1460_,
        v_inst_1461_,
        v_m_1462_,
    );
    leanh::lean_dec_ref(v_m_1462_);
    leanh::lean_dec_ref(v_inst_1461_);
    leanh::lean_dec_ref(v_inst_1460_);
    return v_res_1463_;
}
pub unsafe fn l_Lean_SMap_toList___redArg___lam__0(
    mut v_es_1464_: *mut leanh::LeanObject,
    mut v_a_1465_: *mut leanh::LeanObject,
    mut v_b_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1467_, 0, v_a_1465_);
    leanh::lean_ctor_set(v___x_1467_, 1, v_b_1466_);
    v___x_1468_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1468_, 0, v___x_1467_);
    leanh::lean_ctor_set(v___x_1468_, 1, v_es_1464_);
    return v___x_1468_;
}
pub unsafe fn l_Lean_SMap_toList___redArg(
    mut v_m_1470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1471_ = l_Lean_SMap_toList___redArg___closed__0;
    v___x_1472_ = leanh::lean_box(0);
    v___x_1473_ = l_Lean_SMap_fold___redArg(v___f_1471_, v___x_1472_, v_m_1470_);
    return v___x_1473_;
}
pub unsafe fn l_Lean_SMap_toList(
    mut v_00_u03b1_1474_: *mut leanh::LeanObject,
    mut v_00_u03b2_1475_: *mut leanh::LeanObject,
    mut v_inst_1476_: *mut leanh::LeanObject,
    mut v_inst_1477_: *mut leanh::LeanObject,
    mut v_m_1478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = l_Lean_SMap_toList___redArg(v_m_1478_);
    return v___x_1479_;
}
pub unsafe fn l_Lean_SMap_toList___boxed(
    mut v_00_u03b1_1480_: *mut leanh::LeanObject,
    mut v_00_u03b2_1481_: *mut leanh::LeanObject,
    mut v_inst_1482_: *mut leanh::LeanObject,
    mut v_inst_1483_: *mut leanh::LeanObject,
    mut v_m_1484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1485_ = l_Lean_SMap_toList(
        v_00_u03b1_1480_,
        v_00_u03b2_1481_,
        v_inst_1482_,
        v_inst_1483_,
        v_m_1484_,
    );
    leanh::lean_dec_ref(v_inst_1483_);
    leanh::lean_dec_ref(v_inst_1482_);
    return v_res_1485_;
}
pub unsafe fn l_List_toSMap___redArg___lam__0(
    mut v_inst_1486_: *mut leanh::LeanObject,
    mut v_inst_1487_: *mut leanh::LeanObject,
    mut v_s_1488_: *mut leanh::LeanObject,
    mut v_x_1489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1490_ = leanh::lean_ctor_get(v_x_1489_, 0);
    leanh::lean_inc(v_fst_1490_);
    v_snd_1491_ = leanh::lean_ctor_get(v_x_1489_, 1);
    leanh::lean_inc(v_snd_1491_);
    leanh::lean_dec_ref(v_x_1489_);
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
    mut v_inst_1493_: *mut leanh::LeanObject,
    mut v_inst_1494_: *mut leanh::LeanObject,
    mut v_es_1495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1496_ = leanh::lean_alloc_closure(
        l_List_toSMap___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1496_, 0, v_inst_1493_);
    leanh::lean_closure_set(v___f_1496_, 1, v_inst_1494_);
    v___x_1497_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__4),
        core::ptr::addr_of_mut!(l_Lean_SMap_instInhabited___closed__4_once),
        _init_l_Lean_SMap_instInhabited___closed__4,
    );
    v___x_1498_ = l_List_foldl___redArg(v___f_1496_, v___x_1497_, v_es_1495_);
    return v___x_1498_;
}
pub unsafe fn l_List_toSMap(
    mut v_00_u03b1_1499_: *mut leanh::LeanObject,
    mut v_00_u03b2_1500_: *mut leanh::LeanObject,
    mut v_inst_1501_: *mut leanh::LeanObject,
    mut v_inst_1502_: *mut leanh::LeanObject,
    mut v_es_1503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1504_ = l_List_toSMap___redArg(v_inst_1501_, v_inst_1502_, v_es_1503_);
    return v___x_1504_;
}
pub unsafe fn l_Lean_instReprSMap___redArg___lam__0(
    mut v___x_1508_: *mut leanh::LeanObject,
    mut v_v_1509_: *mut leanh::LeanObject,
    mut v_prec_1510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ = l_Lean_SMap_toList___redArg(v_v_1509_);
    v___x_1512_ = l_List_repr___redArg(v___x_1508_, v___x_1511_);
    v___x_1513_ = l_Lean_instReprSMap___redArg___lam__0___closed__1;
    v___x_1514_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1514_, 0, v___x_1512_);
    leanh::lean_ctor_set(v___x_1514_, 1, v___x_1513_);
    v___x_1515_ = l_Repr_addAppParen(v___x_1514_, v_prec_1510_);
    return v___x_1515_;
}
pub unsafe fn l_Lean_instReprSMap___redArg___lam__0___boxed(
    mut v___x_1516_: *mut leanh::LeanObject,
    mut v_v_1517_: *mut leanh::LeanObject,
    mut v_prec_1518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1519_ = l_Lean_instReprSMap___redArg___lam__0(v___x_1516_, v_v_1517_, v_prec_1518_);
    leanh::lean_dec(v_prec_1518_);
    return v_res_1519_;
}
pub unsafe fn l_Lean_instReprSMap___redArg(
    mut v_inst_1520_: *mut leanh::LeanObject,
    mut v_inst_1521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1522_ = leanh::lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1522_, 0, v_inst_1521_);
    v___x_1523_ =
        leanh::lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_1523_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1523_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1523_, 2, v_inst_1520_);
    leanh::lean_closure_set(v___x_1523_, 3, v___f_1522_);
    v___f_1524_ = leanh::lean_alloc_closure(
        l_Lean_instReprSMap___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1524_, 0, v___x_1523_);
    return v___f_1524_;
}
pub unsafe fn l_Lean_instReprSMap(
    mut v_00_u03b1_1525_: *mut leanh::LeanObject,
    mut v_00_u03b2_1526_: *mut leanh::LeanObject,
    mut v_x_1527_: *mut leanh::LeanObject,
    mut v_x_1528_: *mut leanh::LeanObject,
    mut v_inst_1529_: *mut leanh::LeanObject,
    mut v_inst_1530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Lean_instReprSMap___redArg(v_inst_1529_, v_inst_1530_);
    return v___x_1531_;
}
pub unsafe fn l_Lean_instReprSMap___boxed(
    mut v_00_u03b1_1532_: *mut leanh::LeanObject,
    mut v_00_u03b2_1533_: *mut leanh::LeanObject,
    mut v_x_1534_: *mut leanh::LeanObject,
    mut v_x_1535_: *mut leanh::LeanObject,
    mut v_inst_1536_: *mut leanh::LeanObject,
    mut v_inst_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1538_ = l_Lean_instReprSMap(
        v_00_u03b1_1532_,
        v_00_u03b2_1533_,
        v_x_1534_,
        v_x_1535_,
        v_inst_1536_,
        v_inst_1537_,
    );
    leanh::lean_dec_ref(v_x_1535_);
    leanh::lean_dec_ref(v_x_1534_);
    return v_res_1538_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_SMap(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentHashMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Append(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_SMap(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_SMap(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_PersistentHashMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_Append(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_SMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_SMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_SMap(builtin);
}