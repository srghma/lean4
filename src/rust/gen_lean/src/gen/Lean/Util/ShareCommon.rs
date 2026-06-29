// Lean compiler output
// Module: Lean.Util.ShareCommon
// Imports: Init.ShareCommon Std.Data.HashSet.Basic Lean.Data.PersistentHashSet
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::ShareCommon::{
    initialize_Init_ShareCommon, l_ShareCommon_StateFactory_mkImpl, l_ShareCommon_mkStateImpl,
    runtime_initialize_Init_ShareCommon,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::PersistentHashSet::{
    initialize_Lean_Data_PersistentHashSet, runtime_initialize_Lean_Data_PersistentHashSet,
};
use crate::r#gen::Std::Data::HashSet::Basic::{
    initialize_Std_Data_HashSet_Basic, runtime_initialize_Std_Data_HashSet_Basic,
};
use crate::ffi::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
};
use crate::ffi::lean_state_sharecommon;
pub static l_Lean_ShareCommon_objectFactory___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ShareCommon_objectFactory___elam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ShareCommon_objectFactory___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ShareCommon_objectFactory___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ShareCommon_objectFactory___elam__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ShareCommon_objectFactory___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ShareCommon_objectFactory___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ShareCommon_objectFactory___elam__2 as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ShareCommon_objectFactory___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ShareCommon_objectFactory___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ShareCommon_objectFactory___elam__3___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ShareCommon_objectFactory___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ShareCommon_objectFactory___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ShareCommon_objectFactory___elam__4___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ShareCommon_objectFactory___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ShareCommon_objectFactory___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ShareCommon_objectFactory___elam__5 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ShareCommon_objectFactory___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ShareCommon_objectFactory___closed__6_value: crate::leanh::LeanCtorObject<6> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6
                + 0) as u16,
            other: 6,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_ShareCommon_objectFactory___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ShareCommon_objectFactory___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ShareCommon_objectFactory___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_ShareCommon_objectFactory: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ShareCommon_persistentObjectFactory___closed__0_value:
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
    m_fun: l_Lean_ShareCommon_persistentObjectFactory___elam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ShareCommon_persistentObjectFactory___closed__1_value:
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
    m_fun: l_Lean_ShareCommon_persistentObjectFactory___elam__1___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ShareCommon_persistentObjectFactory___closed__2_value:
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
    m_fun: l_Lean_ShareCommon_persistentObjectFactory___elam__2 as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ShareCommon_persistentObjectFactory___closed__3_value:
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
    m_fun: l_Lean_ShareCommon_persistentObjectFactory___elam__3___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ShareCommon_persistentObjectFactory___closed__4_value:
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
    m_fun: l_Lean_ShareCommon_persistentObjectFactory___elam__4___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ShareCommon_persistentObjectFactory___closed__5_value:
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
    m_fun: l_Lean_ShareCommon_persistentObjectFactory___elam__5 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ShareCommon_persistentObjectFactory___closed__6_value:
    crate::leanh::LeanCtorObject<6> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6
            + 0) as u16,
        other: 6,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_ShareCommon_persistentObjectFactory: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0_value:
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
    m_fun: l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__0___redArg(
    mut v_x_1235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1237_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1238_ = lean_nat_mul(v_x_1235_, v___x_1237_);
    v___x_1239_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1240_ = lean_nat_div(v___x_1238_, v___x_1239_);
    crate::leanh::lean_dec(v___x_1238_);
    v___x_1241_ = l_Nat_nextPowerOfTwo(v___x_1240_);
    crate::leanh::lean_dec(v___x_1240_);
    v___x_1242_ = crate::leanh::lean_box(0);
    v___x_1243_ = lean_mk_array(v___x_1241_, v___x_1242_);
    v___x_1244_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1244_, 0, v___x_1236_);
    crate::leanh::lean_ctor_set(v___x_1244_, 1, v___x_1243_);
    return v___x_1244_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__0___redArg___boxed(
    mut v_x_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1246_ = l_Lean_ShareCommon_objectFactory___elam__0___redArg(v_x_1245_);
    crate::leanh::lean_dec(v_x_1245_);
    return v_res_1246_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__0(
    mut v_00_u03b1_1247_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1248_: *mut crate::leanh::LeanObject,
    mut v_inst_1249_: *mut crate::leanh::LeanObject,
    mut v_inst_1250_: *mut crate::leanh::LeanObject,
    mut v_x_1251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = l_Lean_ShareCommon_objectFactory___elam__0___redArg(v_x_1251_);
    return v___x_1252_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__0___boxed(
    mut v_00_u03b1_1253_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1254_: *mut crate::leanh::LeanObject,
    mut v_inst_1255_: *mut crate::leanh::LeanObject,
    mut v_inst_1256_: *mut crate::leanh::LeanObject,
    mut v_x_1257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Lean_ShareCommon_objectFactory___elam__0(
        v_00_u03b1_1253_,
        v_00_u03b2_1254_,
        v_inst_1255_,
        v_inst_1256_,
        v_x_1257_,
    );
    crate::leanh::lean_dec(v_x_1257_);
    crate::leanh::lean_dec_ref(v_inst_1256_);
    crate::leanh::lean_dec_ref(v_inst_1255_);
    return v_res_1258_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__3___redArg(
    mut v_x_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1260_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1261_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1262_ = lean_nat_mul(v_x_1259_, v___x_1261_);
    v___x_1263_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1264_ = lean_nat_div(v___x_1262_, v___x_1263_);
    crate::leanh::lean_dec(v___x_1262_);
    v___x_1265_ = l_Nat_nextPowerOfTwo(v___x_1264_);
    crate::leanh::lean_dec(v___x_1264_);
    v___x_1266_ = crate::leanh::lean_box(0);
    v___x_1267_ = lean_mk_array(v___x_1265_, v___x_1266_);
    v___x_1268_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1268_, 0, v___x_1260_);
    crate::leanh::lean_ctor_set(v___x_1268_, 1, v___x_1267_);
    return v___x_1268_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__3___redArg___boxed(
    mut v_x_1269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1270_ = l_Lean_ShareCommon_objectFactory___elam__3___redArg(v_x_1269_);
    crate::leanh::lean_dec(v_x_1269_);
    return v_res_1270_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__3(
    mut v_00_u03b1_1271_: *mut crate::leanh::LeanObject,
    mut v_inst_1272_: *mut crate::leanh::LeanObject,
    mut v_inst_1273_: *mut crate::leanh::LeanObject,
    mut v_x_1274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_Lean_ShareCommon_objectFactory___elam__3___redArg(v_x_1274_);
    return v___x_1275_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__3___boxed(
    mut v_00_u03b1_1276_: *mut crate::leanh::LeanObject,
    mut v_inst_1277_: *mut crate::leanh::LeanObject,
    mut v_inst_1278_: *mut crate::leanh::LeanObject,
    mut v_x_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1280_ = l_Lean_ShareCommon_objectFactory___elam__3(
        v_00_u03b1_1276_,
        v_inst_1277_,
        v_inst_1278_,
        v_x_1279_,
    );
    crate::leanh::lean_dec(v_x_1279_);
    crate::leanh::lean_dec_ref(v_inst_1278_);
    crate::leanh::lean_dec_ref(v_inst_1277_);
    return v_res_1280_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(
    mut v_inst_1281_: *mut crate::leanh::LeanObject,
    mut v_a_1282_: *mut crate::leanh::LeanObject,
    mut v_x_1283_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1284_: u8 = 0;
    let mut v_key_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: u8 = 0;
    let mut v___x_1290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1283_) == 0 {
                    crate::leanh::lean_dec(v_a_1282_);
                    crate::leanh::lean_dec_ref(v_inst_1281_);
                    v___x_1284_ = 0;
                    return v___x_1284_;
                } else {
                    v_key_1285_ = crate::leanh::lean_ctor_get(v_x_1283_, 0);
                    crate::leanh::lean_inc(v_key_1285_);
                    v_tail_1286_ = crate::leanh::lean_ctor_get(v_x_1283_, 2);
                    crate::leanh::lean_inc(v_tail_1286_);
                    crate::leanh::lean_dec_ref_known(v_x_1283_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1281_);
                    crate::leanh::lean_inc(v_a_1282_);
                    v___x_1287_ = crate::leanh::lean_apply_2(v_inst_1281_, v_key_1285_, v_a_1282_);
                    v___x_1288_ = (crate::leanh::lean_unbox(v___x_1287_) as u8);
                    if v___x_1288_ == 0 {
                        v_x_1283_ = v_tail_1286_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1286_);
                        crate::leanh::lean_dec(v_a_1282_);
                        crate::leanh::lean_dec_ref(v_inst_1281_);
                        v___x_1290_ = (crate::leanh::lean_unbox(v___x_1287_) as u8);
                        return v___x_1290_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg___boxed(
    mut v_inst_1291_: *mut crate::leanh::LeanObject,
    mut v_a_1292_: *mut crate::leanh::LeanObject,
    mut v_x_1293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1294_: u8 = 0;
    let mut v_r_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1294_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_1291_, v_a_1292_, v_x_1293_);
    v_r_1295_ = crate::leanh::lean_box((v_res_1294_) as usize);
    return v_r_1295_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13___redArg(
    mut v_inst_1296_: *mut crate::leanh::LeanObject,
    mut v_x_1297_: *mut crate::leanh::LeanObject,
    mut v_x_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1304_: u8 = 0;
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: u64 = 0;
    let mut v___x_1308_: u64 = 0;
    let mut v___x_1309_: u64 = 0;
    let mut v___x_1310_: u64 = 0;
    let mut v_fold_1311_: u64 = 0;
    let mut v___x_1312_: u64 = 0;
    let mut v___x_1313_: u64 = 0;
    let mut v___x_1314_: u64 = 0;
    let mut v___x_1315_: usize = 0;
    let mut v___x_1316_: usize = 0;
    let mut v___x_1317_: usize = 0;
    let mut v___x_1318_: usize = 0;
    let mut v___x_1319_: usize = 0;
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1298_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_1296_);
                    return v_x_1297_;
                } else {
                    v_key_1299_ = crate::leanh::lean_ctor_get(v_x_1298_, 0);
                    v_value_1300_ = crate::leanh::lean_ctor_get(v_x_1298_, 1);
                    v_tail_1301_ = crate::leanh::lean_ctor_get(v_x_1298_, 2);
                    v_isSharedCheck_1326_ = (!crate::leanh::lean_is_exclusive(v_x_1298_)) as u8;
                    if v_isSharedCheck_1326_ == 0 {
                        v___x_1303_ = v_x_1298_;
                        v_isShared_1304_ = v_isSharedCheck_1326_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1301_);
                        crate::leanh::lean_inc(v_value_1300_);
                        crate::leanh::lean_inc(v_key_1299_);
                        crate::leanh::lean_dec(v_x_1298_);
                        v___x_1303_ = crate::leanh::lean_box(0);
                        v_isShared_1304_ = v_isSharedCheck_1326_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1305_ = lean_array_get_size(v_x_1297_);
                crate::leanh::lean_inc_ref(v_inst_1296_);
                crate::leanh::lean_inc(v_key_1299_);
                v___x_1306_ = crate::leanh::lean_apply_1(v_inst_1296_, v_key_1299_);
                v___x_1307_ = 32u64;
                v___x_1308_ = crate::leanh::lean_unbox_uint64(v___x_1306_);
                v___x_1309_ = lean_uint64_shift_right(v___x_1308_, v___x_1307_);
                v___x_1310_ = crate::leanh::lean_unbox_uint64(v___x_1306_);
                crate::leanh::lean_dec_ref(v___x_1306_);
                v_fold_1311_ = lean_uint64_xor(v___x_1310_, v___x_1309_);
                v___x_1312_ = 16u64;
                v___x_1313_ = lean_uint64_shift_right(v_fold_1311_, v___x_1312_);
                v___x_1314_ = lean_uint64_xor(v_fold_1311_, v___x_1313_);
                v___x_1315_ = lean_uint64_to_usize(v___x_1314_);
                v___x_1316_ = lean_usize_of_nat(v___x_1305_);
                v___x_1317_ = 1usize;
                v___x_1318_ = lean_usize_sub(v___x_1316_, v___x_1317_);
                v___x_1319_ = lean_usize_land(v___x_1315_, v___x_1318_);
                v___x_1320_ = lean_array_uget_borrowed(v_x_1297_, v___x_1319_);
                crate::leanh::lean_inc(v___x_1320_);
                if v_isShared_1304_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1303_, 2, v___x_1320_);
                    v___x_1322_ = v___x_1303_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1325_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_key_1299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_value_1300_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1325_, 2, v___x_1320_);
                    v___x_1322_ = v_reuseFailAlloc_1325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1323_ = lean_array_uset(v_x_1297_, v___x_1319_, v___x_1322_);
                v_x_1297_ = v___x_1323_;
                v_x_1298_ = v_tail_1301_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10___redArg(
    mut v_inst_1327_: *mut crate::leanh::LeanObject,
    mut v_i_1328_: *mut crate::leanh::LeanObject,
    mut v_source_1329_: *mut crate::leanh::LeanObject,
    mut v_target_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    let mut v_es_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1331_ = lean_array_get_size(v_source_1329_);
                v___x_1332_ = lean_nat_dec_lt(v_i_1328_, v___x_1331_);
                if v___x_1332_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1329_);
                    crate::leanh::lean_dec(v_i_1328_);
                    crate::leanh::lean_dec_ref(v_inst_1327_);
                    return v_target_1330_;
                } else {
                    v_es_1333_ = lean_array_fget(v_source_1329_, v_i_1328_);
                    v___x_1334_ = crate::leanh::lean_box(0);
                    v_source_1335_ = lean_array_fset(v_source_1329_, v_i_1328_, v___x_1334_);
                    crate::leanh::lean_inc_ref(v_inst_1327_);
                    v_target_1336_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13___redArg(v_inst_1327_, v_target_1330_, v_es_1333_);
                    v___x_1337_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1338_ = lean_nat_add(v_i_1328_, v___x_1337_);
                    crate::leanh::lean_dec(v_i_1328_);
                    v_i_1328_ = v___x_1338_;
                    v_source_1329_ = v_source_1335_;
                    v_target_1330_ = v_target_1336_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(
    mut v_inst_1340_: *mut crate::leanh::LeanObject,
    mut v_data_1341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1342_ = lean_array_get_size(v_data_1341_);
    v___x_1343_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1344_ = lean_nat_mul(v___x_1342_, v___x_1343_);
    v___x_1345_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1346_ = crate::leanh::lean_box(0);
    v___x_1347_ = lean_mk_array(v_nbuckets_1344_, v___x_1346_);
    v___x_1348_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10___redArg(v_inst_1340_, v___x_1345_, v_data_1341_, v___x_1347_);
    return v___x_1348_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(
    mut v_inst_1349_: *mut crate::leanh::LeanObject,
    mut v_inst_1350_: *mut crate::leanh::LeanObject,
    mut v_m_1351_: *mut crate::leanh::LeanObject,
    mut v_a_1352_: *mut crate::leanh::LeanObject,
    mut v_b_1353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: u64 = 0;
    let mut v___x_1359_: u64 = 0;
    let mut v___x_1360_: u64 = 0;
    let mut v___x_1361_: u64 = 0;
    let mut v_fold_1362_: u64 = 0;
    let mut v___x_1363_: u64 = 0;
    let mut v___x_1364_: u64 = 0;
    let mut v___x_1365_: u64 = 0;
    let mut v___x_1366_: usize = 0;
    let mut v___x_1367_: usize = 0;
    let mut v___x_1368_: usize = 0;
    let mut v___x_1369_: usize = 0;
    let mut v___x_1370_: usize = 0;
    let mut v_bkt_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: u8 = 0;
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1375_: u8 = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: u8 = 0;
    let mut v_val_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1393_: u8 = 0;
    let mut v_unused_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1354_ = crate::leanh::lean_ctor_get(v_m_1351_, 0);
                v_buckets_1355_ = crate::leanh::lean_ctor_get(v_m_1351_, 1);
                v___x_1356_ = lean_array_get_size(v_buckets_1355_);
                crate::leanh::lean_inc_ref(v_inst_1350_);
                crate::leanh::lean_inc_n(v_a_1352_, 2);
                v___x_1357_ = crate::leanh::lean_apply_1(v_inst_1350_, v_a_1352_);
                v___x_1358_ = 32u64;
                v___x_1359_ = crate::leanh::lean_unbox_uint64(v___x_1357_);
                v___x_1360_ = lean_uint64_shift_right(v___x_1359_, v___x_1358_);
                v___x_1361_ = crate::leanh::lean_unbox_uint64(v___x_1357_);
                crate::leanh::lean_dec_ref(v___x_1357_);
                v_fold_1362_ = lean_uint64_xor(v___x_1361_, v___x_1360_);
                v___x_1363_ = 16u64;
                v___x_1364_ = lean_uint64_shift_right(v_fold_1362_, v___x_1363_);
                v___x_1365_ = lean_uint64_xor(v_fold_1362_, v___x_1364_);
                v___x_1366_ = lean_uint64_to_usize(v___x_1365_);
                v___x_1367_ = lean_usize_of_nat(v___x_1356_);
                v___x_1368_ = 1usize;
                v___x_1369_ = lean_usize_sub(v___x_1367_, v___x_1368_);
                v___x_1370_ = lean_usize_land(v___x_1366_, v___x_1369_);
                v_bkt_1371_ = lean_array_uget_borrowed(v_buckets_1355_, v___x_1370_);
                crate::leanh::lean_inc(v_bkt_1371_);
                v___x_1372_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_1349_, v_a_1352_, v_bkt_1371_);
                if v___x_1372_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_1355_);
                    crate::leanh::lean_inc(v_size_1354_);
                    v_isSharedCheck_1393_ = (!crate::leanh::lean_is_exclusive(v_m_1351_)) as u8;
                    if v_isSharedCheck_1393_ == 0 {
                        v_unused_1394_ = crate::leanh::lean_ctor_get(v_m_1351_, 1);
                        crate::leanh::lean_dec(v_unused_1394_);
                        v_unused_1395_ = crate::leanh::lean_ctor_get(v_m_1351_, 0);
                        crate::leanh::lean_dec(v_unused_1395_);
                        v___x_1374_ = v_m_1351_;
                        v_isShared_1375_ = v_isSharedCheck_1393_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1351_);
                        v___x_1374_ = crate::leanh::lean_box(0);
                        v_isShared_1375_ = v_isSharedCheck_1393_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1353_);
                    crate::leanh::lean_dec(v_a_1352_);
                    crate::leanh::lean_dec_ref(v_inst_1350_);
                    return v_m_1351_;
                }
            }
            1 => {
                v___x_1376_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_1377_ = lean_nat_add(v_size_1354_, v___x_1376_);
                crate::leanh::lean_dec(v_size_1354_);
                crate::leanh::lean_inc(v_bkt_1371_);
                v___x_1378_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1378_, 0, v_a_1352_);
                crate::leanh::lean_ctor_set(v___x_1378_, 1, v_b_1353_);
                crate::leanh::lean_ctor_set(v___x_1378_, 2, v_bkt_1371_);
                v_buckets_x27_1379_ = lean_array_uset(v_buckets_1355_, v___x_1370_, v___x_1378_);
                v___x_1380_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1381_ = lean_nat_mul(v_size_x27_1377_, v___x_1380_);
                v___x_1382_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1383_ = lean_nat_div(v___x_1381_, v___x_1382_);
                crate::leanh::lean_dec(v___x_1381_);
                v___x_1384_ = lean_array_get_size(v_buckets_x27_1379_);
                v___x_1385_ = lean_nat_dec_le(v___x_1383_, v___x_1384_);
                crate::leanh::lean_dec(v___x_1383_);
                if v___x_1385_ == 0 {
                    v_val_1386_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_1350_, v_buckets_x27_1379_);
                    if v_isShared_1375_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1374_, 1, v_val_1386_);
                        crate::leanh::lean_ctor_set(v___x_1374_, 0, v_size_x27_1377_);
                        v___x_1388_ = v___x_1374_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1389_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_size_x27_1377_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_val_1386_);
                        v___x_1388_ = v_reuseFailAlloc_1389_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_1350_);
                    if v_isShared_1375_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1374_, 1, v_buckets_x27_1379_);
                        crate::leanh::lean_ctor_set(v___x_1374_, 0, v_size_x27_1377_);
                        v___x_1391_ = v___x_1374_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1392_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_size_x27_1377_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_buckets_x27_1379_);
                        v___x_1391_ = v_reuseFailAlloc_1392_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1388_;
            }
            3 => {
                return v___x_1391_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__5___redArg(
    mut v_inst_1396_: *mut crate::leanh::LeanObject,
    mut v_inst_1397_: *mut crate::leanh::LeanObject,
    mut v_x_1398_: *mut crate::leanh::LeanObject,
    mut v___y_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ = crate::leanh::lean_box(0);
    v___x_1401_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(v_inst_1396_, v_inst_1397_, v_x_1398_, v___y_1399_, v___x_1400_);
    return v___x_1401_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__5(
    mut v_00_u03b1_1402_: *mut crate::leanh::LeanObject,
    mut v_inst_1403_: *mut crate::leanh::LeanObject,
    mut v_inst_1404_: *mut crate::leanh::LeanObject,
    mut v_x_1405_: *mut crate::leanh::LeanObject,
    mut v___y_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ = l_Lean_ShareCommon_objectFactory___elam__5___redArg(
        v_inst_1403_,
        v_inst_1404_,
        v_x_1405_,
        v___y_1406_,
    );
    return v___x_1407_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(
    mut v_inst_1408_: *mut crate::leanh::LeanObject,
    mut v_a_1409_: *mut crate::leanh::LeanObject,
    mut v_b_1410_: *mut crate::leanh::LeanObject,
    mut v_x_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1417_: u8 = 0;
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: u8 = 0;
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1411_) == 0 {
                    crate::leanh::lean_dec(v_b_1410_);
                    crate::leanh::lean_dec(v_a_1409_);
                    crate::leanh::lean_dec_ref(v_inst_1408_);
                    return v_x_1411_;
                } else {
                    v_key_1412_ = crate::leanh::lean_ctor_get(v_x_1411_, 0);
                    v_value_1413_ = crate::leanh::lean_ctor_get(v_x_1411_, 1);
                    v_tail_1414_ = crate::leanh::lean_ctor_get(v_x_1411_, 2);
                    v_isSharedCheck_1427_ = (!crate::leanh::lean_is_exclusive(v_x_1411_)) as u8;
                    if v_isSharedCheck_1427_ == 0 {
                        v___x_1416_ = v_x_1411_;
                        v_isShared_1417_ = v_isSharedCheck_1427_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1414_);
                        crate::leanh::lean_inc(v_value_1413_);
                        crate::leanh::lean_inc(v_key_1412_);
                        crate::leanh::lean_dec(v_x_1411_);
                        v___x_1416_ = crate::leanh::lean_box(0);
                        v_isShared_1417_ = v_isSharedCheck_1427_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_1408_);
                crate::leanh::lean_inc(v_a_1409_);
                crate::leanh::lean_inc(v_key_1412_);
                v___x_1418_ = crate::leanh::lean_apply_2(v_inst_1408_, v_key_1412_, v_a_1409_);
                v___x_1419_ = (crate::leanh::lean_unbox(v___x_1418_) as u8);
                if v___x_1419_ == 0 {
                    v___x_1420_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_1408_, v_a_1409_, v_b_1410_, v_tail_1414_);
                    if v_isShared_1417_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1416_, 2, v___x_1420_);
                        v___x_1422_ = v___x_1416_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1423_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_key_1412_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_value_1413_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 2, v___x_1420_);
                        v___x_1422_ = v_reuseFailAlloc_1423_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1413_);
                    crate::leanh::lean_dec(v_key_1412_);
                    crate::leanh::lean_dec_ref(v_inst_1408_);
                    if v_isShared_1417_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1416_, 1, v_b_1410_);
                        crate::leanh::lean_ctor_set(v___x_1416_, 0, v_a_1409_);
                        v___x_1425_ = v___x_1416_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1426_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1409_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_b_1410_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_tail_1414_);
                        v___x_1425_ = v_reuseFailAlloc_1426_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1422_;
            }
            3 => {
                return v___x_1425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(
    mut v_inst_1428_: *mut crate::leanh::LeanObject,
    mut v_inst_1429_: *mut crate::leanh::LeanObject,
    mut v_m_1430_: *mut crate::leanh::LeanObject,
    mut v_a_1431_: *mut crate::leanh::LeanObject,
    mut v_b_1432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1437_: u8 = 0;
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: u64 = 0;
    let mut v___x_1441_: u64 = 0;
    let mut v___x_1442_: u64 = 0;
    let mut v___x_1443_: u64 = 0;
    let mut v_fold_1444_: u64 = 0;
    let mut v___x_1445_: u64 = 0;
    let mut v___x_1446_: u64 = 0;
    let mut v___x_1447_: u64 = 0;
    let mut v___x_1448_: usize = 0;
    let mut v___x_1449_: usize = 0;
    let mut v___x_1450_: usize = 0;
    let mut v___x_1451_: usize = 0;
    let mut v___x_1452_: usize = 0;
    let mut v_bkt_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: u8 = 0;
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u8 = 0;
    let mut v_val_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1433_ = crate::leanh::lean_ctor_get(v_m_1430_, 0);
                v_buckets_1434_ = crate::leanh::lean_ctor_get(v_m_1430_, 1);
                v_isSharedCheck_1479_ = (!crate::leanh::lean_is_exclusive(v_m_1430_)) as u8;
                if v_isSharedCheck_1479_ == 0 {
                    v___x_1436_ = v_m_1430_;
                    v_isShared_1437_ = v_isSharedCheck_1479_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1434_);
                    crate::leanh::lean_inc(v_size_1433_);
                    crate::leanh::lean_dec(v_m_1430_);
                    v___x_1436_ = crate::leanh::lean_box(0);
                    v_isShared_1437_ = v_isSharedCheck_1479_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1438_ = lean_array_get_size(v_buckets_1434_);
                crate::leanh::lean_inc_ref(v_inst_1429_);
                crate::leanh::lean_inc_n(v_a_1431_, 2);
                v___x_1439_ = crate::leanh::lean_apply_1(v_inst_1429_, v_a_1431_);
                v___x_1440_ = 32u64;
                v___x_1441_ = crate::leanh::lean_unbox_uint64(v___x_1439_);
                v___x_1442_ = lean_uint64_shift_right(v___x_1441_, v___x_1440_);
                v___x_1443_ = crate::leanh::lean_unbox_uint64(v___x_1439_);
                crate::leanh::lean_dec_ref(v___x_1439_);
                v_fold_1444_ = lean_uint64_xor(v___x_1443_, v___x_1442_);
                v___x_1445_ = 16u64;
                v___x_1446_ = lean_uint64_shift_right(v_fold_1444_, v___x_1445_);
                v___x_1447_ = lean_uint64_xor(v_fold_1444_, v___x_1446_);
                v___x_1448_ = lean_uint64_to_usize(v___x_1447_);
                v___x_1449_ = lean_usize_of_nat(v___x_1438_);
                v___x_1450_ = 1usize;
                v___x_1451_ = lean_usize_sub(v___x_1449_, v___x_1450_);
                v___x_1452_ = lean_usize_land(v___x_1448_, v___x_1451_);
                v_bkt_1453_ = lean_array_uget_borrowed(v_buckets_1434_, v___x_1452_);
                crate::leanh::lean_inc(v_bkt_1453_);
                crate::leanh::lean_inc_ref(v_inst_1428_);
                v___x_1454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_1428_, v_a_1431_, v_bkt_1453_);
                if v___x_1454_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_1428_);
                    v___x_1455_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1456_ = lean_nat_add(v_size_1433_, v___x_1455_);
                    crate::leanh::lean_dec(v_size_1433_);
                    crate::leanh::lean_inc(v_bkt_1453_);
                    v___x_1457_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1457_, 0, v_a_1431_);
                    crate::leanh::lean_ctor_set(v___x_1457_, 1, v_b_1432_);
                    crate::leanh::lean_ctor_set(v___x_1457_, 2, v_bkt_1453_);
                    v_buckets_x27_1458_ =
                        lean_array_uset(v_buckets_1434_, v___x_1452_, v___x_1457_);
                    v___x_1459_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1460_ = lean_nat_mul(v_size_x27_1456_, v___x_1459_);
                    v___x_1461_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1462_ = lean_nat_div(v___x_1460_, v___x_1461_);
                    crate::leanh::lean_dec(v___x_1460_);
                    v___x_1463_ = lean_array_get_size(v_buckets_x27_1458_);
                    v___x_1464_ = lean_nat_dec_le(v___x_1462_, v___x_1463_);
                    crate::leanh::lean_dec(v___x_1462_);
                    if v___x_1464_ == 0 {
                        v_val_1465_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_1429_, v_buckets_x27_1458_);
                        if v_isShared_1437_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1436_, 1, v_val_1465_);
                            crate::leanh::lean_ctor_set(v___x_1436_, 0, v_size_x27_1456_);
                            v___x_1467_ = v___x_1436_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1468_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1468_,
                                0,
                                v_size_x27_1456_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_val_1465_);
                            v___x_1467_ = v_reuseFailAlloc_1468_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_inst_1429_);
                        if v_isShared_1437_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1436_, 1, v_buckets_x27_1458_);
                            crate::leanh::lean_ctor_set(v___x_1436_, 0, v_size_x27_1456_);
                            v___x_1470_ = v___x_1436_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1471_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1471_,
                                0,
                                v_size_x27_1456_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1471_,
                                1,
                                v_buckets_x27_1458_,
                            );
                            v___x_1470_ = v_reuseFailAlloc_1471_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1453_);
                    crate::leanh::lean_dec_ref(v_inst_1429_);
                    v___x_1472_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1473_ =
                        lean_array_uset(v_buckets_1434_, v___x_1452_, v___x_1472_);
                    v___x_1474_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_1428_, v_a_1431_, v_b_1432_, v_bkt_1453_);
                    v___x_1475_ = lean_array_uset(v_buckets_x27_1473_, v___x_1452_, v___x_1474_);
                    if v_isShared_1437_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1436_, 1, v___x_1475_);
                        v___x_1477_ = v___x_1436_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1478_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_size_1433_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 1, v___x_1475_);
                        v___x_1477_ = v_reuseFailAlloc_1478_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1467_;
            }
            3 => {
                return v___x_1470_;
            }
            4 => {
                return v___x_1477_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__2(
    mut v_00_u03b1_1480_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1481_: *mut crate::leanh::LeanObject,
    mut v_inst_1482_: *mut crate::leanh::LeanObject,
    mut v_inst_1483_: *mut crate::leanh::LeanObject,
    mut v_x_1484_: *mut crate::leanh::LeanObject,
    mut v___y_1485_: *mut crate::leanh::LeanObject,
    mut v___y_1486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1487_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_1482_, v_inst_1483_, v_x_1484_, v___y_1485_, v___y_1486_);
    return v___x_1487_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(
    mut v_inst_1488_: *mut crate::leanh::LeanObject,
    mut v_a_1489_: *mut crate::leanh::LeanObject,
    mut v_x_1490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: u8 = 0;
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1490_) == 0 {
                    crate::leanh::lean_dec(v_a_1489_);
                    crate::leanh::lean_dec_ref(v_inst_1488_);
                    v___x_1491_ = crate::leanh::lean_box(0);
                    return v___x_1491_;
                } else {
                    v_key_1492_ = crate::leanh::lean_ctor_get(v_x_1490_, 0);
                    crate::leanh::lean_inc_n(v_key_1492_, 2);
                    v_tail_1493_ = crate::leanh::lean_ctor_get(v_x_1490_, 2);
                    crate::leanh::lean_inc(v_tail_1493_);
                    crate::leanh::lean_dec_ref_known(v_x_1490_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1488_);
                    crate::leanh::lean_inc(v_a_1489_);
                    v___x_1494_ = crate::leanh::lean_apply_2(v_inst_1488_, v_key_1492_, v_a_1489_);
                    v___x_1495_ = (crate::leanh::lean_unbox(v___x_1494_) as u8);
                    if v___x_1495_ == 0 {
                        crate::leanh::lean_dec(v_key_1492_);
                        v_x_1490_ = v_tail_1493_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1493_);
                        crate::leanh::lean_dec(v_a_1489_);
                        crate::leanh::lean_dec_ref(v_inst_1488_);
                        v___x_1497_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1497_, 0, v_key_1492_);
                        return v___x_1497_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(
    mut v_inst_1498_: *mut crate::leanh::LeanObject,
    mut v_inst_1499_: *mut crate::leanh::LeanObject,
    mut v_m_1500_: *mut crate::leanh::LeanObject,
    mut v_a_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: u64 = 0;
    let mut v___x_1506_: u64 = 0;
    let mut v___x_1507_: u64 = 0;
    let mut v___x_1508_: u64 = 0;
    let mut v_fold_1509_: u64 = 0;
    let mut v___x_1510_: u64 = 0;
    let mut v___x_1511_: u64 = 0;
    let mut v___x_1512_: u64 = 0;
    let mut v___x_1513_: usize = 0;
    let mut v___x_1514_: usize = 0;
    let mut v___x_1515_: usize = 0;
    let mut v___x_1516_: usize = 0;
    let mut v___x_1517_: usize = 0;
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1502_ = crate::leanh::lean_ctor_get(v_m_1500_, 1);
    v___x_1503_ = lean_array_get_size(v_buckets_1502_);
    crate::leanh::lean_inc(v_a_1501_);
    v___x_1504_ = crate::leanh::lean_apply_1(v_inst_1499_, v_a_1501_);
    v___x_1505_ = 32u64;
    v___x_1506_ = crate::leanh::lean_unbox_uint64(v___x_1504_);
    v___x_1507_ = lean_uint64_shift_right(v___x_1506_, v___x_1505_);
    v___x_1508_ = crate::leanh::lean_unbox_uint64(v___x_1504_);
    crate::leanh::lean_dec_ref(v___x_1504_);
    v_fold_1509_ = lean_uint64_xor(v___x_1508_, v___x_1507_);
    v___x_1510_ = 16u64;
    v___x_1511_ = lean_uint64_shift_right(v_fold_1509_, v___x_1510_);
    v___x_1512_ = lean_uint64_xor(v_fold_1509_, v___x_1511_);
    v___x_1513_ = lean_uint64_to_usize(v___x_1512_);
    v___x_1514_ = lean_usize_of_nat(v___x_1503_);
    v___x_1515_ = 1usize;
    v___x_1516_ = lean_usize_sub(v___x_1514_, v___x_1515_);
    v___x_1517_ = lean_usize_land(v___x_1513_, v___x_1516_);
    v___x_1518_ = lean_array_uget_borrowed(v_buckets_1502_, v___x_1517_);
    crate::leanh::lean_inc(v___x_1518_);
    v___x_1519_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(v_inst_1498_, v_a_1501_, v___x_1518_);
    return v___x_1519_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg___boxed(
    mut v_inst_1520_: *mut crate::leanh::LeanObject,
    mut v_inst_1521_: *mut crate::leanh::LeanObject,
    mut v_m_1522_: *mut crate::leanh::LeanObject,
    mut v_a_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_1520_, v_inst_1521_, v_m_1522_, v_a_1523_);
    crate::leanh::lean_dec_ref(v_m_1522_);
    return v_res_1524_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__4(
    mut v_00_u03b1_1525_: *mut crate::leanh::LeanObject,
    mut v_inst_1526_: *mut crate::leanh::LeanObject,
    mut v_inst_1527_: *mut crate::leanh::LeanObject,
    mut v_x_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1530_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_1526_, v_inst_1527_, v_x_1528_, v___y_1529_);
    return v___x_1530_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__4___boxed(
    mut v_00_u03b1_1531_: *mut crate::leanh::LeanObject,
    mut v_inst_1532_: *mut crate::leanh::LeanObject,
    mut v_inst_1533_: *mut crate::leanh::LeanObject,
    mut v_x_1534_: *mut crate::leanh::LeanObject,
    mut v___y_1535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1536_ = l_Lean_ShareCommon_objectFactory___elam__4(
        v_00_u03b1_1531_,
        v_inst_1532_,
        v_inst_1533_,
        v_x_1534_,
        v___y_1535_,
    );
    crate::leanh::lean_dec_ref(v_x_1534_);
    return v_res_1536_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(
    mut v_inst_1537_: *mut crate::leanh::LeanObject,
    mut v_a_1538_: *mut crate::leanh::LeanObject,
    mut v_x_1539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: u8 = 0;
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1539_) == 0 {
                    crate::leanh::lean_dec(v_a_1538_);
                    crate::leanh::lean_dec_ref(v_inst_1537_);
                    v___x_1540_ = crate::leanh::lean_box(0);
                    return v___x_1540_;
                } else {
                    v_key_1541_ = crate::leanh::lean_ctor_get(v_x_1539_, 0);
                    crate::leanh::lean_inc(v_key_1541_);
                    v_value_1542_ = crate::leanh::lean_ctor_get(v_x_1539_, 1);
                    crate::leanh::lean_inc(v_value_1542_);
                    v_tail_1543_ = crate::leanh::lean_ctor_get(v_x_1539_, 2);
                    crate::leanh::lean_inc(v_tail_1543_);
                    crate::leanh::lean_dec_ref_known(v_x_1539_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1537_);
                    crate::leanh::lean_inc(v_a_1538_);
                    v___x_1544_ = crate::leanh::lean_apply_2(v_inst_1537_, v_key_1541_, v_a_1538_);
                    v___x_1545_ = (crate::leanh::lean_unbox(v___x_1544_) as u8);
                    if v___x_1545_ == 0 {
                        crate::leanh::lean_dec(v_value_1542_);
                        v_x_1539_ = v_tail_1543_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1543_);
                        crate::leanh::lean_dec(v_a_1538_);
                        crate::leanh::lean_dec_ref(v_inst_1537_);
                        v___x_1547_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1547_, 0, v_value_1542_);
                        return v___x_1547_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(
    mut v_inst_1548_: *mut crate::leanh::LeanObject,
    mut v_inst_1549_: *mut crate::leanh::LeanObject,
    mut v_m_1550_: *mut crate::leanh::LeanObject,
    mut v_a_1551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: u64 = 0;
    let mut v___x_1556_: u64 = 0;
    let mut v___x_1557_: u64 = 0;
    let mut v___x_1558_: u64 = 0;
    let mut v_fold_1559_: u64 = 0;
    let mut v___x_1560_: u64 = 0;
    let mut v___x_1561_: u64 = 0;
    let mut v___x_1562_: u64 = 0;
    let mut v___x_1563_: usize = 0;
    let mut v___x_1564_: usize = 0;
    let mut v___x_1565_: usize = 0;
    let mut v___x_1566_: usize = 0;
    let mut v___x_1567_: usize = 0;
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1552_ = crate::leanh::lean_ctor_get(v_m_1550_, 1);
    v___x_1553_ = lean_array_get_size(v_buckets_1552_);
    crate::leanh::lean_inc(v_a_1551_);
    v___x_1554_ = crate::leanh::lean_apply_1(v_inst_1549_, v_a_1551_);
    v___x_1555_ = 32u64;
    v___x_1556_ = crate::leanh::lean_unbox_uint64(v___x_1554_);
    v___x_1557_ = lean_uint64_shift_right(v___x_1556_, v___x_1555_);
    v___x_1558_ = crate::leanh::lean_unbox_uint64(v___x_1554_);
    crate::leanh::lean_dec_ref(v___x_1554_);
    v_fold_1559_ = lean_uint64_xor(v___x_1558_, v___x_1557_);
    v___x_1560_ = 16u64;
    v___x_1561_ = lean_uint64_shift_right(v_fold_1559_, v___x_1560_);
    v___x_1562_ = lean_uint64_xor(v_fold_1559_, v___x_1561_);
    v___x_1563_ = lean_uint64_to_usize(v___x_1562_);
    v___x_1564_ = lean_usize_of_nat(v___x_1553_);
    v___x_1565_ = 1usize;
    v___x_1566_ = lean_usize_sub(v___x_1564_, v___x_1565_);
    v___x_1567_ = lean_usize_land(v___x_1563_, v___x_1566_);
    v___x_1568_ = lean_array_uget_borrowed(v_buckets_1552_, v___x_1567_);
    crate::leanh::lean_inc(v___x_1568_);
    v___x_1569_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(v_inst_1548_, v_a_1551_, v___x_1568_);
    return v___x_1569_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg___boxed(
    mut v_inst_1570_: *mut crate::leanh::LeanObject,
    mut v_inst_1571_: *mut crate::leanh::LeanObject,
    mut v_m_1572_: *mut crate::leanh::LeanObject,
    mut v_a_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_1570_, v_inst_1571_, v_m_1572_, v_a_1573_);
    crate::leanh::lean_dec_ref(v_m_1572_);
    return v_res_1574_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__1(
    mut v_00_u03b1_1575_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1576_: *mut crate::leanh::LeanObject,
    mut v_inst_1577_: *mut crate::leanh::LeanObject,
    mut v_inst_1578_: *mut crate::leanh::LeanObject,
    mut v_x_1579_: *mut crate::leanh::LeanObject,
    mut v___y_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_1577_, v_inst_1578_, v_x_1579_, v___y_1580_);
    return v___x_1581_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__1___boxed(
    mut v_00_u03b1_1582_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1583_: *mut crate::leanh::LeanObject,
    mut v_inst_1584_: *mut crate::leanh::LeanObject,
    mut v_inst_1585_: *mut crate::leanh::LeanObject,
    mut v_x_1586_: *mut crate::leanh::LeanObject,
    mut v___y_1587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1588_ = l_Lean_ShareCommon_objectFactory___elam__1(
        v_00_u03b1_1582_,
        v_00_u03b2_1583_,
        v_inst_1584_,
        v_inst_1585_,
        v_x_1586_,
        v___y_1587_,
    );
    crate::leanh::lean_dec_ref(v_x_1586_);
    return v_res_1588_;
}
pub unsafe fn _init_l_Lean_ShareCommon_objectFactory___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1602_ = l_Lean_ShareCommon_objectFactory___closed__6;
    v___x_1603_ = l_ShareCommon_StateFactory_mkImpl(v___x_1602_);
    return v___x_1603_;
}
pub unsafe fn _init_l_Lean_ShareCommon_objectFactory() -> *mut crate::leanh::LeanObject {
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1604_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_objectFactory___closed__7),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_objectFactory___closed__7_once),
        _init_l_Lean_ShareCommon_objectFactory___closed__7,
    );
    return v___x_1604_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__1___redArg(
    mut v_inst_1605_: *mut crate::leanh::LeanObject,
    mut v_inst_1606_: *mut crate::leanh::LeanObject,
    mut v_x_1607_: *mut crate::leanh::LeanObject,
    mut v___y_1608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1609_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_1605_, v_inst_1606_, v_x_1607_, v___y_1608_);
    return v___x_1609_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__1___redArg___boxed(
    mut v_inst_1610_: *mut crate::leanh::LeanObject,
    mut v_inst_1611_: *mut crate::leanh::LeanObject,
    mut v_x_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1614_ = l_Lean_ShareCommon_objectFactory___elam__1___redArg(
        v_inst_1610_,
        v_inst_1611_,
        v_x_1612_,
        v___y_1613_,
    );
    crate::leanh::lean_dec_ref(v_x_1612_);
    return v_res_1614_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__2___redArg(
    mut v_inst_1615_: *mut crate::leanh::LeanObject,
    mut v_inst_1616_: *mut crate::leanh::LeanObject,
    mut v_x_1617_: *mut crate::leanh::LeanObject,
    mut v___y_1618_: *mut crate::leanh::LeanObject,
    mut v___y_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1620_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_1615_, v_inst_1616_, v_x_1617_, v___y_1618_, v___y_1619_);
    return v___x_1620_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__4___redArg(
    mut v_inst_1621_: *mut crate::leanh::LeanObject,
    mut v_inst_1622_: *mut crate::leanh::LeanObject,
    mut v_x_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_1621_, v_inst_1622_, v_x_1623_, v___y_1624_);
    return v___x_1625_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__4___redArg___boxed(
    mut v_inst_1626_: *mut crate::leanh::LeanObject,
    mut v_inst_1627_: *mut crate::leanh::LeanObject,
    mut v_x_1628_: *mut crate::leanh::LeanObject,
    mut v___y_1629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1630_ = l_Lean_ShareCommon_objectFactory___elam__4___redArg(
        v_inst_1626_,
        v_inst_1627_,
        v_x_1628_,
        v___y_1629_,
    );
    crate::leanh::lean_dec_ref(v_x_1628_);
    return v_res_1630_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1(
    mut v_00_u03b1_1631_: *mut crate::leanh::LeanObject,
    mut v_inst_1632_: *mut crate::leanh::LeanObject,
    mut v_inst_1633_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1634_: *mut crate::leanh::LeanObject,
    mut v_m_1635_: *mut crate::leanh::LeanObject,
    mut v_a_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1637_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_1632_, v_inst_1633_, v_m_1635_, v_a_1636_);
    return v___x_1637_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___boxed(
    mut v_00_u03b1_1638_: *mut crate::leanh::LeanObject,
    mut v_inst_1639_: *mut crate::leanh::LeanObject,
    mut v_inst_1640_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1641_: *mut crate::leanh::LeanObject,
    mut v_m_1642_: *mut crate::leanh::LeanObject,
    mut v_a_1643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1644_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1(v_00_u03b1_1638_, v_inst_1639_, v_inst_1640_, v_00_u03b2_1641_, v_m_1642_, v_a_1643_);
    crate::leanh::lean_dec_ref(v_m_1642_);
    return v_res_1644_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3(
    mut v_00_u03b1_1645_: *mut crate::leanh::LeanObject,
    mut v_inst_1646_: *mut crate::leanh::LeanObject,
    mut v_inst_1647_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1648_: *mut crate::leanh::LeanObject,
    mut v_m_1649_: *mut crate::leanh::LeanObject,
    mut v_a_1650_: *mut crate::leanh::LeanObject,
    mut v_b_1651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1652_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_1646_, v_inst_1647_, v_m_1649_, v_a_1650_, v_b_1651_);
    return v___x_1652_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6(
    mut v_00_u03b1_1653_: *mut crate::leanh::LeanObject,
    mut v_inst_1654_: *mut crate::leanh::LeanObject,
    mut v_inst_1655_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1656_: *mut crate::leanh::LeanObject,
    mut v_m_1657_: *mut crate::leanh::LeanObject,
    mut v_a_1658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_1654_, v_inst_1655_, v_m_1657_, v_a_1658_);
    return v___x_1659_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___boxed(
    mut v_00_u03b1_1660_: *mut crate::leanh::LeanObject,
    mut v_inst_1661_: *mut crate::leanh::LeanObject,
    mut v_inst_1662_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1663_: *mut crate::leanh::LeanObject,
    mut v_m_1664_: *mut crate::leanh::LeanObject,
    mut v_a_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1666_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6(v_00_u03b1_1660_, v_inst_1661_, v_inst_1662_, v_00_u03b2_1663_, v_m_1664_, v_a_1665_);
    crate::leanh::lean_dec_ref(v_m_1664_);
    return v_res_1666_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8(
    mut v_00_u03b1_1667_: *mut crate::leanh::LeanObject,
    mut v_inst_1668_: *mut crate::leanh::LeanObject,
    mut v_inst_1669_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1670_: *mut crate::leanh::LeanObject,
    mut v_m_1671_: *mut crate::leanh::LeanObject,
    mut v_a_1672_: *mut crate::leanh::LeanObject,
    mut v_b_1673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(v_inst_1668_, v_inst_1669_, v_m_1671_, v_a_1672_, v_b_1673_);
    return v___x_1674_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3(
    mut v_00_u03b1_1675_: *mut crate::leanh::LeanObject,
    mut v_inst_1676_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1677_: *mut crate::leanh::LeanObject,
    mut v_a_1678_: *mut crate::leanh::LeanObject,
    mut v_x_1679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(v_inst_1676_, v_a_1678_, v_x_1679_);
    return v___x_1680_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(
    mut v_00_u03b1_1681_: *mut crate::leanh::LeanObject,
    mut v_inst_1682_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1683_: *mut crate::leanh::LeanObject,
    mut v_a_1684_: *mut crate::leanh::LeanObject,
    mut v_x_1685_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1686_: u8 = 0;
    v___x_1686_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_1682_, v_a_1684_, v_x_1685_);
    return v___x_1686_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___boxed(
    mut v_00_u03b1_1687_: *mut crate::leanh::LeanObject,
    mut v_inst_1688_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1689_: *mut crate::leanh::LeanObject,
    mut v_a_1690_: *mut crate::leanh::LeanObject,
    mut v_x_1691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1692_: u8 = 0;
    let mut v_r_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1692_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(v_00_u03b1_1687_, v_inst_1688_, v_00_u03b2_1689_, v_a_1690_, v_x_1691_);
    v_r_1693_ = crate::leanh::lean_box((v_res_1692_) as usize);
    return v_r_1693_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7(
    mut v_00_u03b1_1694_: *mut crate::leanh::LeanObject,
    mut v_inst_1695_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1696_: *mut crate::leanh::LeanObject,
    mut v_data_1697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1698_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_1695_, v_data_1697_);
    return v___x_1698_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8(
    mut v_00_u03b1_1699_: *mut crate::leanh::LeanObject,
    mut v_inst_1700_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1701_: *mut crate::leanh::LeanObject,
    mut v_a_1702_: *mut crate::leanh::LeanObject,
    mut v_b_1703_: *mut crate::leanh::LeanObject,
    mut v_x_1704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_1700_, v_a_1702_, v_b_1703_, v_x_1704_);
    return v___x_1705_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11(
    mut v_00_u03b1_1706_: *mut crate::leanh::LeanObject,
    mut v_inst_1707_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1708_: *mut crate::leanh::LeanObject,
    mut v_a_1709_: *mut crate::leanh::LeanObject,
    mut v_x_1710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(v_inst_1707_, v_a_1709_, v_x_1710_);
    return v___x_1711_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10(
    mut v_00_u03b1_1712_: *mut crate::leanh::LeanObject,
    mut v_inst_1713_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1714_: *mut crate::leanh::LeanObject,
    mut v_i_1715_: *mut crate::leanh::LeanObject,
    mut v_source_1716_: *mut crate::leanh::LeanObject,
    mut v_target_1717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1718_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10___redArg(v_inst_1713_, v_i_1715_, v_source_1716_, v_target_1717_);
    return v___x_1718_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13(
    mut v_00_u03b1_1719_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1720_: *mut crate::leanh::LeanObject,
    mut v_inst_1721_: *mut crate::leanh::LeanObject,
    mut v_x_1722_: *mut crate::leanh::LeanObject,
    mut v_x_1723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1724_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13___redArg(v_inst_1721_, v_x_1722_, v_x_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(
    mut v_inst_1725_: *mut crate::leanh::LeanObject,
    mut v_keys_1726_: *mut crate::leanh::LeanObject,
    mut v_vals_1727_: *mut crate::leanh::LeanObject,
    mut v_i_1728_: *mut crate::leanh::LeanObject,
    mut v_k_1729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: u8 = 0;
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: u8 = 0;
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1730_ = lean_array_get_size(v_keys_1726_);
                v___x_1731_ = lean_nat_dec_lt(v_i_1728_, v___x_1730_);
                if v___x_1731_ == 0 {
                    crate::leanh::lean_dec(v_k_1729_);
                    crate::leanh::lean_dec(v_i_1728_);
                    crate::leanh::lean_dec_ref(v_inst_1725_);
                    v___x_1732_ = crate::leanh::lean_box(0);
                    return v___x_1732_;
                } else {
                    v_k_x27_1733_ = lean_array_fget_borrowed(v_keys_1726_, v_i_1728_);
                    crate::leanh::lean_inc_ref(v_inst_1725_);
                    crate::leanh::lean_inc(v_k_x27_1733_);
                    crate::leanh::lean_inc(v_k_1729_);
                    v___x_1734_ =
                        crate::leanh::lean_apply_2(v_inst_1725_, v_k_1729_, v_k_x27_1733_);
                    v___x_1735_ = (crate::leanh::lean_unbox(v___x_1734_) as u8);
                    if v___x_1735_ == 0 {
                        v___x_1736_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1737_ = lean_nat_add(v_i_1728_, v___x_1736_);
                        crate::leanh::lean_dec(v_i_1728_);
                        v_i_1728_ = v___x_1737_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_k_1729_);
                        crate::leanh::lean_dec_ref(v_inst_1725_);
                        v___x_1739_ = lean_array_fget_borrowed(v_vals_1727_, v_i_1728_);
                        crate::leanh::lean_dec(v_i_1728_);
                        crate::leanh::lean_inc(v___x_1739_);
                        v___x_1740_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1740_, 0, v___x_1739_);
                        return v___x_1740_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg___boxed(
    mut v_inst_1741_: *mut crate::leanh::LeanObject,
    mut v_keys_1742_: *mut crate::leanh::LeanObject,
    mut v_vals_1743_: *mut crate::leanh::LeanObject,
    mut v_i_1744_: *mut crate::leanh::LeanObject,
    mut v_k_1745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1746_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_1741_, v_keys_1742_, v_vals_1743_, v_i_1744_, v_k_1745_);
    crate::leanh::lean_dec_ref(v_vals_1743_);
    crate::leanh::lean_dec_ref(v_keys_1742_);
    return v_res_1746_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_1747_: usize = 0;
    let mut v___x_1748_: usize = 0;
    let mut v___x_1749_: usize = 0;
    v___x_1747_ = 5usize;
    v___x_1748_ = 1usize;
    v___x_1749_ = lean_usize_shift_left(v___x_1748_, v___x_1747_);
    return v___x_1749_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_1750_: usize = 0;
    let mut v___x_1751_: usize = 0;
    let mut v___x_1752_: usize = 0;
    v___x_1750_ = 1usize;
    v___x_1751_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0);
    v___x_1752_ = lean_usize_sub(v___x_1751_, v___x_1750_);
    return v___x_1752_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(
    mut v_inst_1753_: *mut crate::leanh::LeanObject,
    mut v_x_1754_: *mut crate::leanh::LeanObject,
    mut v_x_1755_: usize,
    mut v_x_1756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: usize = 0;
    let mut v___x_1760_: usize = 0;
    let mut v___x_1761_: usize = 0;
    let mut v_j_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: u8 = 0;
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: usize = 0;
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1754_) == 0 {
                    v_es_1757_ = crate::leanh::lean_ctor_get(v_x_1754_, 0);
                    crate::leanh::lean_inc_ref(v_es_1757_);
                    crate::leanh::lean_dec_ref_known(v_x_1754_, 1);
                    v___x_1758_ = crate::leanh::lean_box(2);
                    v___x_1759_ = 5usize;
                    v___x_1760_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1);
                    v___x_1761_ = lean_usize_land(v_x_1755_, v___x_1760_);
                    v_j_1762_ = lean_usize_to_nat(v___x_1761_);
                    v___x_1763_ = lean_array_get(v___x_1758_, v_es_1757_, v_j_1762_);
                    crate::leanh::lean_dec(v_j_1762_);
                    crate::leanh::lean_dec_ref(v_es_1757_);
                    match crate::leanh::lean_obj_tag(v___x_1763_) {
                        0 => {
                            v_key_1764_ = crate::leanh::lean_ctor_get(v___x_1763_, 0);
                            crate::leanh::lean_inc(v_key_1764_);
                            v_val_1765_ = crate::leanh::lean_ctor_get(v___x_1763_, 1);
                            crate::leanh::lean_inc(v_val_1765_);
                            crate::leanh::lean_dec_ref_known(v___x_1763_, 2);
                            v___x_1766_ =
                                crate::leanh::lean_apply_2(v_inst_1753_, v_x_1756_, v_key_1764_);
                            v___x_1767_ = (crate::leanh::lean_unbox(v___x_1766_) as u8);
                            if v___x_1767_ == 0 {
                                crate::leanh::lean_dec(v_val_1765_);
                                v___x_1768_ = crate::leanh::lean_box(0);
                                return v___x_1768_;
                            } else {
                                v___x_1769_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1769_, 0, v_val_1765_);
                                return v___x_1769_;
                            }
                        }
                        1 => {
                            v_node_1770_ = crate::leanh::lean_ctor_get(v___x_1763_, 0);
                            crate::leanh::lean_inc(v_node_1770_);
                            crate::leanh::lean_dec_ref_known(v___x_1763_, 1);
                            v___x_1771_ = lean_usize_shift_right(v_x_1755_, v___x_1759_);
                            v_x_1754_ = v_node_1770_;
                            v_x_1755_ = v___x_1771_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_x_1756_);
                            crate::leanh::lean_dec_ref(v_inst_1753_);
                            v___x_1773_ = crate::leanh::lean_box(0);
                            return v___x_1773_;
                        }
                    }
                } else {
                    v_ks_1774_ = crate::leanh::lean_ctor_get(v_x_1754_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1774_);
                    v_vs_1775_ = crate::leanh::lean_ctor_get(v_x_1754_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1775_);
                    crate::leanh::lean_dec_ref_known(v_x_1754_, 2);
                    v___x_1776_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1777_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_1753_, v_ks_1774_, v_vs_1775_, v___x_1776_, v_x_1756_);
                    crate::leanh::lean_dec_ref(v_vs_1775_);
                    crate::leanh::lean_dec_ref(v_ks_1774_);
                    return v___x_1777_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___boxed(
    mut v_inst_1778_: *mut crate::leanh::LeanObject,
    mut v_x_1779_: *mut crate::leanh::LeanObject,
    mut v_x_1780_: *mut crate::leanh::LeanObject,
    mut v_x_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_710__boxed_1782_: usize = 0;
    let mut v_res_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_710__boxed_1782_ = crate::leanh::lean_unbox_usize(v_x_1780_);
    crate::leanh::lean_dec(v_x_1780_);
    v_res_1783_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_1778_, v_x_1779_, v_x_710__boxed_1782_, v_x_1781_);
    return v_res_1783_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(
    mut v_inst_1784_: *mut crate::leanh::LeanObject,
    mut v_inst_1785_: *mut crate::leanh::LeanObject,
    mut v_x_1786_: *mut crate::leanh::LeanObject,
    mut v_x_1787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u64 = 0;
    let mut v___x_1790_: usize = 0;
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_x_1787_);
    v___x_1788_ = crate::leanh::lean_apply_1(v_inst_1785_, v_x_1787_);
    v___x_1789_ = crate::leanh::lean_unbox_uint64(v___x_1788_);
    crate::leanh::lean_dec_ref(v___x_1788_);
    v___x_1790_ = lean_uint64_to_usize(v___x_1789_);
    crate::leanh::lean_inc_ref(v_x_1786_);
    v___x_1791_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_1784_, v_x_1786_, v___x_1790_, v_x_1787_);
    return v___x_1791_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg___boxed(
    mut v_inst_1792_: *mut crate::leanh::LeanObject,
    mut v_inst_1793_: *mut crate::leanh::LeanObject,
    mut v_x_1794_: *mut crate::leanh::LeanObject,
    mut v_x_1795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1796_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_1792_, v_inst_1793_, v_x_1794_, v_x_1795_);
    crate::leanh::lean_dec_ref(v_x_1794_);
    return v_res_1796_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__1(
    mut v_00_u03b1_1797_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1798_: *mut crate::leanh::LeanObject,
    mut v_inst_1799_: *mut crate::leanh::LeanObject,
    mut v_inst_1800_: *mut crate::leanh::LeanObject,
    mut v_x_1801_: *mut crate::leanh::LeanObject,
    mut v___y_1802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1803_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_1799_, v_inst_1800_, v_x_1801_, v___y_1802_);
    return v___x_1803_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__1___boxed(
    mut v_00_u03b1_1804_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1805_: *mut crate::leanh::LeanObject,
    mut v_inst_1806_: *mut crate::leanh::LeanObject,
    mut v_inst_1807_: *mut crate::leanh::LeanObject,
    mut v_x_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1810_ = l_Lean_ShareCommon_persistentObjectFactory___elam__1(
        v_00_u03b1_1804_,
        v_00_u03b2_1805_,
        v_inst_1806_,
        v_inst_1807_,
        v_x_1808_,
        v___y_1809_,
    );
    crate::leanh::lean_dec_ref(v_x_1808_);
    return v_res_1810_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(
    mut v_inst_1811_: *mut crate::leanh::LeanObject,
    mut v_keys_1812_: *mut crate::leanh::LeanObject,
    mut v_vals_1813_: *mut crate::leanh::LeanObject,
    mut v_i_1814_: *mut crate::leanh::LeanObject,
    mut v_k_1815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: u8 = 0;
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: u8 = 0;
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1816_ = lean_array_get_size(v_keys_1812_);
                v___x_1817_ = lean_nat_dec_lt(v_i_1814_, v___x_1816_);
                if v___x_1817_ == 0 {
                    crate::leanh::lean_dec(v_k_1815_);
                    crate::leanh::lean_dec(v_i_1814_);
                    crate::leanh::lean_dec_ref(v_inst_1811_);
                    v___x_1818_ = crate::leanh::lean_box(0);
                    return v___x_1818_;
                } else {
                    v_k_x27_1819_ = lean_array_fget_borrowed(v_keys_1812_, v_i_1814_);
                    crate::leanh::lean_inc_ref(v_inst_1811_);
                    crate::leanh::lean_inc(v_k_x27_1819_);
                    crate::leanh::lean_inc(v_k_1815_);
                    v___x_1820_ =
                        crate::leanh::lean_apply_2(v_inst_1811_, v_k_1815_, v_k_x27_1819_);
                    v___x_1821_ = (crate::leanh::lean_unbox(v___x_1820_) as u8);
                    if v___x_1821_ == 0 {
                        v___x_1822_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1823_ = lean_nat_add(v_i_1814_, v___x_1822_);
                        crate::leanh::lean_dec(v_i_1814_);
                        v_i_1814_ = v___x_1823_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_k_1815_);
                        crate::leanh::lean_dec_ref(v_inst_1811_);
                        v___x_1825_ = lean_array_fget_borrowed(v_vals_1813_, v_i_1814_);
                        crate::leanh::lean_dec(v_i_1814_);
                        crate::leanh::lean_inc(v___x_1825_);
                        crate::leanh::lean_inc(v_k_x27_1819_);
                        v___x_1826_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1826_, 0, v_k_x27_1819_);
                        crate::leanh::lean_ctor_set(v___x_1826_, 1, v___x_1825_);
                        v___x_1827_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_1826_);
                        return v___x_1827_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg___boxed(
    mut v_inst_1828_: *mut crate::leanh::LeanObject,
    mut v_keys_1829_: *mut crate::leanh::LeanObject,
    mut v_vals_1830_: *mut crate::leanh::LeanObject,
    mut v_i_1831_: *mut crate::leanh::LeanObject,
    mut v_k_1832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1833_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_1828_, v_keys_1829_, v_vals_1830_, v_i_1831_, v_k_1832_);
    crate::leanh::lean_dec_ref(v_vals_1830_);
    crate::leanh::lean_dec_ref(v_keys_1829_);
    return v_res_1833_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(
    mut v_inst_1834_: *mut crate::leanh::LeanObject,
    mut v_x_1835_: *mut crate::leanh::LeanObject,
    mut v_x_1836_: usize,
    mut v_x_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: usize = 0;
    let mut v___x_1841_: usize = 0;
    let mut v___x_1842_: usize = 0;
    let mut v_j_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: usize = 0;
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1835_) == 0 {
                    v_es_1838_ = crate::leanh::lean_ctor_get(v_x_1835_, 0);
                    crate::leanh::lean_inc_ref(v_es_1838_);
                    crate::leanh::lean_dec_ref_known(v_x_1835_, 1);
                    v___x_1839_ = crate::leanh::lean_box(2);
                    v___x_1840_ = 5usize;
                    v___x_1841_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1);
                    v___x_1842_ = lean_usize_land(v_x_1836_, v___x_1841_);
                    v_j_1843_ = lean_usize_to_nat(v___x_1842_);
                    v___x_1844_ = lean_array_get(v___x_1839_, v_es_1838_, v_j_1843_);
                    crate::leanh::lean_dec(v_j_1843_);
                    crate::leanh::lean_dec_ref(v_es_1838_);
                    match crate::leanh::lean_obj_tag(v___x_1844_) {
                        0 => {
                            v_key_1845_ = crate::leanh::lean_ctor_get(v___x_1844_, 0);
                            crate::leanh::lean_inc_n(v_key_1845_, 2);
                            v_val_1846_ = crate::leanh::lean_ctor_get(v___x_1844_, 1);
                            crate::leanh::lean_inc(v_val_1846_);
                            crate::leanh::lean_dec_ref_known(v___x_1844_, 2);
                            v___x_1847_ =
                                crate::leanh::lean_apply_2(v_inst_1834_, v_x_1837_, v_key_1845_);
                            v___x_1848_ = (crate::leanh::lean_unbox(v___x_1847_) as u8);
                            if v___x_1848_ == 0 {
                                crate::leanh::lean_dec(v_val_1846_);
                                crate::leanh::lean_dec(v_key_1845_);
                                v___x_1849_ = crate::leanh::lean_box(0);
                                return v___x_1849_;
                            } else {
                                v___x_1850_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1850_, 0, v_key_1845_);
                                crate::leanh::lean_ctor_set(v___x_1850_, 1, v_val_1846_);
                                v___x_1851_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1851_, 0, v___x_1850_);
                                return v___x_1851_;
                            }
                        }
                        1 => {
                            v_node_1852_ = crate::leanh::lean_ctor_get(v___x_1844_, 0);
                            crate::leanh::lean_inc(v_node_1852_);
                            crate::leanh::lean_dec_ref_known(v___x_1844_, 1);
                            v___x_1853_ = lean_usize_shift_right(v_x_1836_, v___x_1840_);
                            v_x_1835_ = v_node_1852_;
                            v_x_1836_ = v___x_1853_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_x_1837_);
                            crate::leanh::lean_dec_ref(v_inst_1834_);
                            v___x_1855_ = crate::leanh::lean_box(0);
                            return v___x_1855_;
                        }
                    }
                } else {
                    v_ks_1856_ = crate::leanh::lean_ctor_get(v_x_1835_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1856_);
                    v_vs_1857_ = crate::leanh::lean_ctor_get(v_x_1835_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1857_);
                    crate::leanh::lean_dec_ref_known(v_x_1835_, 2);
                    v___x_1858_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1859_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_1834_, v_ks_1856_, v_vs_1857_, v___x_1858_, v_x_1837_);
                    crate::leanh::lean_dec_ref(v_vs_1857_);
                    crate::leanh::lean_dec_ref(v_ks_1856_);
                    return v___x_1859_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg___boxed(
    mut v_inst_1860_: *mut crate::leanh::LeanObject,
    mut v_x_1861_: *mut crate::leanh::LeanObject,
    mut v_x_1862_: *mut crate::leanh::LeanObject,
    mut v_x_1863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_839__boxed_1864_: usize = 0;
    let mut v_res_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_839__boxed_1864_ = crate::leanh::lean_unbox_usize(v_x_1862_);
    crate::leanh::lean_dec(v_x_1862_);
    v_res_1865_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_1860_, v_x_1861_, v_x_839__boxed_1864_, v_x_1863_);
    return v_res_1865_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(
    mut v_inst_1866_: *mut crate::leanh::LeanObject,
    mut v_inst_1867_: *mut crate::leanh::LeanObject,
    mut v_x_1868_: *mut crate::leanh::LeanObject,
    mut v_x_1869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: u64 = 0;
    let mut v___x_1872_: usize = 0;
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_x_1869_);
    v___x_1870_ = crate::leanh::lean_apply_1(v_inst_1867_, v_x_1869_);
    v___x_1871_ = crate::leanh::lean_unbox_uint64(v___x_1870_);
    crate::leanh::lean_dec_ref(v___x_1870_);
    v___x_1872_ = lean_uint64_to_usize(v___x_1871_);
    crate::leanh::lean_inc_ref(v_x_1868_);
    v___x_1873_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_1866_, v_x_1868_, v___x_1872_, v_x_1869_);
    return v___x_1873_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg___boxed(
    mut v_inst_1874_: *mut crate::leanh::LeanObject,
    mut v_inst_1875_: *mut crate::leanh::LeanObject,
    mut v_x_1876_: *mut crate::leanh::LeanObject,
    mut v_x_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1878_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_1874_, v_inst_1875_, v_x_1876_, v_x_1877_);
    crate::leanh::lean_dec_ref(v_x_1876_);
    return v_res_1878_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(
    mut v_inst_1879_: *mut crate::leanh::LeanObject,
    mut v_inst_1880_: *mut crate::leanh::LeanObject,
    mut v_x_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1888_: u8 = 0;
    let mut v_fst_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1883_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_1879_, v_inst_1880_, v_x_1881_, v___y_1882_);
                if crate::leanh::lean_obj_tag(v___x_1883_) == 0 {
                    v___x_1884_ = crate::leanh::lean_box(0);
                    return v___x_1884_;
                } else {
                    v_val_1885_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                    v_isSharedCheck_1893_ = (!crate::leanh::lean_is_exclusive(v___x_1883_)) as u8;
                    if v_isSharedCheck_1893_ == 0 {
                        v___x_1887_ = v___x_1883_;
                        v_isShared_1888_ = v_isSharedCheck_1893_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1885_);
                        crate::leanh::lean_dec(v___x_1883_);
                        v___x_1887_ = crate::leanh::lean_box(0);
                        v_isShared_1888_ = v_isSharedCheck_1893_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1889_ = crate::leanh::lean_ctor_get(v_val_1885_, 0);
                crate::leanh::lean_inc(v_fst_1889_);
                crate::leanh::lean_dec(v_val_1885_);
                if v_isShared_1888_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1887_, 0, v_fst_1889_);
                    v___x_1891_ = v___x_1887_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1892_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_fst_1889_);
                    v___x_1891_ = v_reuseFailAlloc_1892_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg___boxed(
    mut v_inst_1894_: *mut crate::leanh::LeanObject,
    mut v_inst_1895_: *mut crate::leanh::LeanObject,
    mut v_x_1896_: *mut crate::leanh::LeanObject,
    mut v___y_1897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1898_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(
        v_inst_1894_,
        v_inst_1895_,
        v_x_1896_,
        v___y_1897_,
    );
    crate::leanh::lean_dec_ref(v_x_1896_);
    return v_res_1898_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__4(
    mut v_00_u03b1_1899_: *mut crate::leanh::LeanObject,
    mut v_inst_1900_: *mut crate::leanh::LeanObject,
    mut v_inst_1901_: *mut crate::leanh::LeanObject,
    mut v_x_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1904_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(
        v_inst_1900_,
        v_inst_1901_,
        v_x_1902_,
        v___y_1903_,
    );
    return v___x_1904_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__4___boxed(
    mut v_00_u03b1_1905_: *mut crate::leanh::LeanObject,
    mut v_inst_1906_: *mut crate::leanh::LeanObject,
    mut v_inst_1907_: *mut crate::leanh::LeanObject,
    mut v_x_1908_: *mut crate::leanh::LeanObject,
    mut v___y_1909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1910_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4(
        v_00_u03b1_1905_,
        v_inst_1906_,
        v_inst_1907_,
        v_x_1908_,
        v___y_1909_,
    );
    crate::leanh::lean_dec_ref(v_x_1908_);
    return v_res_1910_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1911_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1911_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1912_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0);
    v___x_1913_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1913_, 0, v___x_1912_);
    return v___x_1913_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(
    mut v_00_u03b1_1914_: *mut crate::leanh::LeanObject,
    mut v_inst_1915_: *mut crate::leanh::LeanObject,
    mut v_inst_1916_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1918_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1);
    return v___x_1918_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___boxed(
    mut v_00_u03b1_1919_: *mut crate::leanh::LeanObject,
    mut v_inst_1920_: *mut crate::leanh::LeanObject,
    mut v_inst_1921_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1923_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(v_00_u03b1_1919_, v_inst_1920_, v_inst_1921_, v_00_u03b2_1922_);
    crate::leanh::lean_dec_ref(v_inst_1921_);
    crate::leanh::lean_dec_ref(v_inst_1920_);
    return v_res_1923_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__0(
    mut v_00_u03b1_1924_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1925_: *mut crate::leanh::LeanObject,
    mut v_inst_1926_: *mut crate::leanh::LeanObject,
    mut v_inst_1927_: *mut crate::leanh::LeanObject,
    mut v_x_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1929_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(crate::leanh::lean_box(0), v_inst_1926_, v_inst_1927_, crate::leanh::lean_box(0));
    return v___x_1929_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__0___boxed(
    mut v_00_u03b1_1930_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1931_: *mut crate::leanh::LeanObject,
    mut v_inst_1932_: *mut crate::leanh::LeanObject,
    mut v_inst_1933_: *mut crate::leanh::LeanObject,
    mut v_x_1934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1935_ = l_Lean_ShareCommon_persistentObjectFactory___elam__0(
        v_00_u03b1_1930_,
        v_00_u03b2_1931_,
        v_inst_1932_,
        v_inst_1933_,
        v_x_1934_,
    );
    crate::leanh::lean_dec(v_x_1934_);
    crate::leanh::lean_dec_ref(v_inst_1933_);
    crate::leanh::lean_dec_ref(v_inst_1932_);
    return v_res_1935_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__3(
    mut v_00_u03b1_1936_: *mut crate::leanh::LeanObject,
    mut v_inst_1937_: *mut crate::leanh::LeanObject,
    mut v_inst_1938_: *mut crate::leanh::LeanObject,
    mut v_x_1939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1940_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(crate::leanh::lean_box(0), v_inst_1937_, v_inst_1938_, crate::leanh::lean_box(0));
    return v___x_1940_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__3___boxed(
    mut v_00_u03b1_1941_: *mut crate::leanh::LeanObject,
    mut v_inst_1942_: *mut crate::leanh::LeanObject,
    mut v_inst_1943_: *mut crate::leanh::LeanObject,
    mut v_x_1944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1945_ = l_Lean_ShareCommon_persistentObjectFactory___elam__3(
        v_00_u03b1_1941_,
        v_inst_1942_,
        v_inst_1943_,
        v_x_1944_,
    );
    crate::leanh::lean_dec(v_x_1944_);
    crate::leanh::lean_dec_ref(v_inst_1943_);
    crate::leanh::lean_dec_ref(v_inst_1942_);
    return v_res_1945_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(
    mut v_inst_1946_: *mut crate::leanh::LeanObject,
    mut v_x_1947_: *mut crate::leanh::LeanObject,
    mut v_x_1948_: *mut crate::leanh::LeanObject,
    mut v_x_1949_: *mut crate::leanh::LeanObject,
    mut v_x_1950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1955_: u8 = 0;
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1951_ = crate::leanh::lean_ctor_get(v_x_1947_, 0);
                v_vs_1952_ = crate::leanh::lean_ctor_get(v_x_1947_, 1);
                v_isSharedCheck_1977_ = (!crate::leanh::lean_is_exclusive(v_x_1947_)) as u8;
                if v_isSharedCheck_1977_ == 0 {
                    v___x_1954_ = v_x_1947_;
                    v_isShared_1955_ = v_isSharedCheck_1977_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1952_);
                    crate::leanh::lean_inc(v_ks_1951_);
                    crate::leanh::lean_dec(v_x_1947_);
                    v___x_1954_ = crate::leanh::lean_box(0);
                    v_isShared_1955_ = v_isSharedCheck_1977_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1956_ = lean_array_get_size(v_ks_1951_);
                v___x_1957_ = lean_nat_dec_lt(v_x_1948_, v___x_1956_);
                if v___x_1957_ == 0 {
                    crate::leanh::lean_dec(v_x_1948_);
                    crate::leanh::lean_dec_ref(v_inst_1946_);
                    v___x_1958_ = lean_array_push(v_ks_1951_, v_x_1949_);
                    v___x_1959_ = lean_array_push(v_vs_1952_, v_x_1950_);
                    if v_isShared_1955_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1954_, 1, v___x_1959_);
                        crate::leanh::lean_ctor_set(v___x_1954_, 0, v___x_1958_);
                        v___x_1961_ = v___x_1954_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1962_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1958_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 1, v___x_1959_);
                        v___x_1961_ = v_reuseFailAlloc_1962_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1963_ = lean_array_fget_borrowed(v_ks_1951_, v_x_1948_);
                    crate::leanh::lean_inc_ref(v_inst_1946_);
                    crate::leanh::lean_inc(v_k_x27_1963_);
                    crate::leanh::lean_inc(v_x_1949_);
                    v___x_1964_ =
                        crate::leanh::lean_apply_2(v_inst_1946_, v_x_1949_, v_k_x27_1963_);
                    v___x_1965_ = (crate::leanh::lean_unbox(v___x_1964_) as u8);
                    if v___x_1965_ == 0 {
                        if v_isShared_1955_ == 0 {
                            v___x_1967_ = v___x_1954_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1971_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_ks_1951_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_vs_1952_);
                            v___x_1967_ = v_reuseFailAlloc_1971_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_inst_1946_);
                        v___x_1972_ = lean_array_fset(v_ks_1951_, v_x_1948_, v_x_1949_);
                        v___x_1973_ = lean_array_fset(v_vs_1952_, v_x_1948_, v_x_1950_);
                        crate::leanh::lean_dec(v_x_1948_);
                        if v_isShared_1955_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1954_, 1, v___x_1973_);
                            crate::leanh::lean_ctor_set(v___x_1954_, 0, v___x_1972_);
                            v___x_1975_ = v___x_1954_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1976_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1972_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___x_1973_);
                            v___x_1975_ = v_reuseFailAlloc_1976_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1961_;
            }
            3 => {
                v___x_1968_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1969_ = lean_nat_add(v_x_1948_, v___x_1968_);
                crate::leanh::lean_dec(v_x_1948_);
                v_x_1947_ = v___x_1967_;
                v_x_1948_ = v___x_1969_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(
    mut v_inst_1978_: *mut crate::leanh::LeanObject,
    mut v_n_1979_: *mut crate::leanh::LeanObject,
    mut v_k_1980_: *mut crate::leanh::LeanObject,
    mut v_v_1981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1982_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1983_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(v_inst_1978_, v_n_1979_, v___x_1982_, v_k_1980_, v_v_1981_);
    return v___x_1983_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1984_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1984_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(
    mut v_inst_1985_: *mut crate::leanh::LeanObject,
    mut v_inst_1986_: *mut crate::leanh::LeanObject,
    mut v_x_1987_: *mut crate::leanh::LeanObject,
    mut v_x_1988_: usize,
    mut v_x_1989_: usize,
    mut v_x_1990_: *mut crate::leanh::LeanObject,
    mut v_x_1991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: usize = 0;
    let mut v___x_1994_: usize = 0;
    let mut v___x_1995_: usize = 0;
    let mut v___x_1996_: usize = 0;
    let mut v_j_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2002_: u8 = 0;
    let mut v_v_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2016_: u8 = 0;
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut v_node_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2029_: usize = 0;
    let mut v___x_2030_: usize = 0;
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2035_: u8 = 0;
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2037_: u8 = 0;
    let mut v_unused_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2043_: u8 = 0;
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2048_: u8 = 0;
    let mut v_ks_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: usize = 0;
    let mut v___x_2055_: u8 = 0;
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: u8 = 0;
    let mut v_reuseFailAlloc_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1987_) == 0 {
                    v_es_1992_ = crate::leanh::lean_ctor_get(v_x_1987_, 0);
                    v___x_1993_ = 5usize;
                    v___x_1994_ = 1usize;
                    v___x_1995_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1);
                    v___x_1996_ = lean_usize_land(v_x_1988_, v___x_1995_);
                    v_j_1997_ = lean_usize_to_nat(v___x_1996_);
                    v___x_1998_ = lean_array_get_size(v_es_1992_);
                    v___x_1999_ = lean_nat_dec_lt(v_j_1997_, v___x_1998_);
                    if v___x_1999_ == 0 {
                        crate::leanh::lean_dec(v_j_1997_);
                        crate::leanh::lean_dec(v_x_1991_);
                        crate::leanh::lean_dec(v_x_1990_);
                        crate::leanh::lean_dec_ref(v_inst_1986_);
                        crate::leanh::lean_dec_ref(v_inst_1985_);
                        return v_x_1987_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1992_);
                        v_isSharedCheck_2037_ = (!crate::leanh::lean_is_exclusive(v_x_1987_)) as u8;
                        if v_isSharedCheck_2037_ == 0 {
                            v_unused_2038_ = crate::leanh::lean_ctor_get(v_x_1987_, 0);
                            crate::leanh::lean_dec(v_unused_2038_);
                            v___x_2001_ = v_x_1987_;
                            v_isShared_2002_ = v_isSharedCheck_2037_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1987_);
                            v___x_2001_ = crate::leanh::lean_box(0);
                            v_isShared_2002_ = v_isSharedCheck_2037_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2039_ = crate::leanh::lean_ctor_get(v_x_1987_, 0);
                    v_vs_2040_ = crate::leanh::lean_ctor_get(v_x_1987_, 1);
                    v_isSharedCheck_2060_ = (!crate::leanh::lean_is_exclusive(v_x_1987_)) as u8;
                    if v_isSharedCheck_2060_ == 0 {
                        v___x_2042_ = v_x_1987_;
                        v_isShared_2043_ = v_isSharedCheck_2060_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2040_);
                        crate::leanh::lean_inc(v_ks_2039_);
                        crate::leanh::lean_dec(v_x_1987_);
                        v___x_2042_ = crate::leanh::lean_box(0);
                        v_isShared_2043_ = v_isSharedCheck_2060_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2003_ = lean_array_fget(v_es_1992_, v_j_1997_);
                v___x_2004_ = crate::leanh::lean_box(0);
                v_xs_x27_2005_ = lean_array_fset(v_es_1992_, v_j_1997_, v___x_2004_);
                match crate::leanh::lean_obj_tag(v_v_2003_) {
                    0 => {
                        crate::leanh::lean_dec_ref(v_inst_1986_);
                        v_key_2012_ = crate::leanh::lean_ctor_get(v_v_2003_, 0);
                        v_val_2013_ = crate::leanh::lean_ctor_get(v_v_2003_, 1);
                        v_isSharedCheck_2024_ = (!crate::leanh::lean_is_exclusive(v_v_2003_)) as u8;
                        if v_isSharedCheck_2024_ == 0 {
                            v___x_2015_ = v_v_2003_;
                            v_isShared_2016_ = v_isSharedCheck_2024_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2013_);
                            crate::leanh::lean_inc(v_key_2012_);
                            crate::leanh::lean_dec(v_v_2003_);
                            v___x_2015_ = crate::leanh::lean_box(0);
                            v_isShared_2016_ = v_isSharedCheck_2024_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2025_ = crate::leanh::lean_ctor_get(v_v_2003_, 0);
                        v_isSharedCheck_2035_ = (!crate::leanh::lean_is_exclusive(v_v_2003_)) as u8;
                        if v_isSharedCheck_2035_ == 0 {
                            v___x_2027_ = v_v_2003_;
                            v_isShared_2028_ = v_isSharedCheck_2035_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2025_);
                            crate::leanh::lean_dec(v_v_2003_);
                            v___x_2027_ = crate::leanh::lean_box(0);
                            v_isShared_2028_ = v_isSharedCheck_2035_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v_inst_1986_);
                        crate::leanh::lean_dec_ref(v_inst_1985_);
                        v___x_2036_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2036_, 0, v_x_1990_);
                        crate::leanh::lean_ctor_set(v___x_2036_, 1, v_x_1991_);
                        v___y_2007_ = v___x_2036_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2008_ = lean_array_fset(v_xs_x27_2005_, v_j_1997_, v___y_2007_);
                crate::leanh::lean_dec(v_j_1997_);
                if v_isShared_2002_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2001_, 0, v___x_2008_);
                    v___x_2010_ = v___x_2001_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2011_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
                    v___x_2010_ = v_reuseFailAlloc_2011_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2010_;
            }
            4 => {
                crate::leanh::lean_inc(v_key_2012_);
                crate::leanh::lean_inc(v_x_1990_);
                v___x_2017_ = crate::leanh::lean_apply_2(v_inst_1985_, v_x_1990_, v_key_2012_);
                v___x_2018_ = (crate::leanh::lean_unbox(v___x_2017_) as u8);
                if v___x_2018_ == 0 {
                    crate::leanh::lean_del_object(v___x_2015_);
                    v___x_2019_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2012_,
                        v_val_2013_,
                        v_x_1990_,
                        v_x_1991_,
                    );
                    v___x_2020_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2020_, 0, v___x_2019_);
                    v___y_2007_ = v___x_2020_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2013_);
                    crate::leanh::lean_dec(v_key_2012_);
                    if v_isShared_2016_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2015_, 1, v_x_1991_);
                        crate::leanh::lean_ctor_set(v___x_2015_, 0, v_x_1990_);
                        v___x_2022_ = v___x_2015_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2023_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_x_1990_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_x_1991_);
                        v___x_2022_ = v_reuseFailAlloc_2023_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2007_ = v___x_2022_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2029_ = lean_usize_shift_right(v_x_1988_, v___x_1993_);
                v___x_2030_ = lean_usize_add(v_x_1989_, v___x_1994_);
                v___x_2031_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_1985_, v_inst_1986_, v_node_2025_, v___x_2029_, v___x_2030_, v_x_1990_, v_x_1991_);
                if v_isShared_2028_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2027_, 0, v___x_2031_);
                    v___x_2033_ = v___x_2027_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2034_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
                    v___x_2033_ = v_reuseFailAlloc_2034_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2007_ = v___x_2033_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2043_ == 0 {
                    v___x_2045_ = v___x_2042_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2059_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_ks_2039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_vs_2040_);
                    v___x_2045_ = v_reuseFailAlloc_2059_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_inc_ref(v_inst_1985_);
                v_newNode_2046_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(v_inst_1985_, v___x_2045_, v_x_1990_, v_x_1991_);
                v___x_2054_ = 7usize;
                v___x_2055_ = lean_usize_dec_le(v___x_2054_, v_x_1989_);
                if v___x_2055_ == 0 {
                    v___x_2056_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2046_);
                    v___x_2057_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2058_ = lean_nat_dec_lt(v___x_2056_, v___x_2057_);
                    crate::leanh::lean_dec(v___x_2056_);
                    v___y_2048_ = v___x_2058_;
                    state = 10;
                    continue;
                } else {
                    v___y_2048_ = v___x_2055_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2048_ == 0 {
                    v_ks_2049_ = crate::leanh::lean_ctor_get(v_newNode_2046_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2049_);
                    v_vs_2050_ = crate::leanh::lean_ctor_get(v_newNode_2046_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2050_);
                    crate::leanh::lean_dec_ref(v_newNode_2046_);
                    v___x_2051_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2052_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0);
                    v___x_2053_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_1985_, v_inst_1986_, v_x_1989_, v_ks_2049_, v_vs_2050_, v___x_2051_, v___x_2052_);
                    crate::leanh::lean_dec_ref(v_vs_2050_);
                    crate::leanh::lean_dec_ref(v_ks_2049_);
                    return v___x_2053_;
                } else {
                    crate::leanh::lean_dec_ref(v_inst_1986_);
                    crate::leanh::lean_dec_ref(v_inst_1985_);
                    return v_newNode_2046_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(
    mut v_inst_2061_: *mut crate::leanh::LeanObject,
    mut v_inst_2062_: *mut crate::leanh::LeanObject,
    mut v_depth_2063_: usize,
    mut v_keys_2064_: *mut crate::leanh::LeanObject,
    mut v_vals_2065_: *mut crate::leanh::LeanObject,
    mut v_i_2066_: *mut crate::leanh::LeanObject,
    mut v_entries_2067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: u8 = 0;
    let mut v_k_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: u64 = 0;
    let mut v_h_2074_: usize = 0;
    let mut v___x_2075_: usize = 0;
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: usize = 0;
    let mut v___x_2078_: usize = 0;
    let mut v___x_2079_: usize = 0;
    let mut v_h_2080_: usize = 0;
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2068_ = lean_array_get_size(v_keys_2064_);
                v___x_2069_ = lean_nat_dec_lt(v_i_2066_, v___x_2068_);
                if v___x_2069_ == 0 {
                    crate::leanh::lean_dec(v_i_2066_);
                    crate::leanh::lean_dec_ref(v_inst_2062_);
                    crate::leanh::lean_dec_ref(v_inst_2061_);
                    return v_entries_2067_;
                } else {
                    v_k_2070_ = lean_array_fget_borrowed(v_keys_2064_, v_i_2066_);
                    v_v_2071_ = lean_array_fget_borrowed(v_vals_2065_, v_i_2066_);
                    crate::leanh::lean_inc_ref_n(v_inst_2062_, 2);
                    crate::leanh::lean_inc_n(v_k_2070_, 2);
                    v___x_2072_ = crate::leanh::lean_apply_1(v_inst_2062_, v_k_2070_);
                    v___x_2073_ = crate::leanh::lean_unbox_uint64(v___x_2072_);
                    crate::leanh::lean_dec_ref(v___x_2072_);
                    v_h_2074_ = lean_uint64_to_usize(v___x_2073_);
                    v___x_2075_ = 5usize;
                    v___x_2076_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2077_ = 1usize;
                    v___x_2078_ = lean_usize_sub(v_depth_2063_, v___x_2077_);
                    v___x_2079_ = lean_usize_mul(v___x_2075_, v___x_2078_);
                    v_h_2080_ = lean_usize_shift_right(v_h_2074_, v___x_2079_);
                    v___x_2081_ = lean_nat_add(v_i_2066_, v___x_2076_);
                    crate::leanh::lean_dec(v_i_2066_);
                    crate::leanh::lean_inc(v_v_2071_);
                    crate::leanh::lean_inc_ref(v_inst_2061_);
                    v___x_2082_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_2061_, v_inst_2062_, v_entries_2067_, v_h_2080_, v_depth_2063_, v_k_2070_, v_v_2071_);
                    v_i_2066_ = v___x_2081_;
                    v_entries_2067_ = v___x_2082_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg___boxed(
    mut v_inst_2084_: *mut crate::leanh::LeanObject,
    mut v_inst_2085_: *mut crate::leanh::LeanObject,
    mut v_depth_2086_: *mut crate::leanh::LeanObject,
    mut v_keys_2087_: *mut crate::leanh::LeanObject,
    mut v_vals_2088_: *mut crate::leanh::LeanObject,
    mut v_i_2089_: *mut crate::leanh::LeanObject,
    mut v_entries_2090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2091_: usize = 0;
    let mut v_res_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2091_ = crate::leanh::lean_unbox_usize(v_depth_2086_);
    crate::leanh::lean_dec(v_depth_2086_);
    v_res_2092_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_2084_, v_inst_2085_, v_depth_boxed_2091_, v_keys_2087_, v_vals_2088_, v_i_2089_, v_entries_2090_);
    crate::leanh::lean_dec_ref(v_vals_2088_);
    crate::leanh::lean_dec_ref(v_keys_2087_);
    return v_res_2092_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___boxed(
    mut v_inst_2093_: *mut crate::leanh::LeanObject,
    mut v_inst_2094_: *mut crate::leanh::LeanObject,
    mut v_x_2095_: *mut crate::leanh::LeanObject,
    mut v_x_2096_: *mut crate::leanh::LeanObject,
    mut v_x_2097_: *mut crate::leanh::LeanObject,
    mut v_x_2098_: *mut crate::leanh::LeanObject,
    mut v_x_2099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1109__boxed_2100_: usize = 0;
    let mut v_x_1110__boxed_2101_: usize = 0;
    let mut v_res_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1109__boxed_2100_ = crate::leanh::lean_unbox_usize(v_x_2096_);
    crate::leanh::lean_dec(v_x_2096_);
    v_x_1110__boxed_2101_ = crate::leanh::lean_unbox_usize(v_x_2097_);
    crate::leanh::lean_dec(v_x_2097_);
    v_res_2102_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_2093_, v_inst_2094_, v_x_2095_, v_x_1109__boxed_2100_, v_x_1110__boxed_2101_, v_x_2098_, v_x_2099_);
    return v_res_2102_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(
    mut v_inst_2103_: *mut crate::leanh::LeanObject,
    mut v_inst_2104_: *mut crate::leanh::LeanObject,
    mut v_x_2105_: *mut crate::leanh::LeanObject,
    mut v_x_2106_: *mut crate::leanh::LeanObject,
    mut v_x_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: u64 = 0;
    let mut v___x_2110_: usize = 0;
    let mut v___x_2111_: usize = 0;
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_2104_);
    crate::leanh::lean_inc(v_x_2106_);
    v___x_2108_ = crate::leanh::lean_apply_1(v_inst_2104_, v_x_2106_);
    v___x_2109_ = crate::leanh::lean_unbox_uint64(v___x_2108_);
    crate::leanh::lean_dec_ref(v___x_2108_);
    v___x_2110_ = lean_uint64_to_usize(v___x_2109_);
    v___x_2111_ = 1usize;
    v___x_2112_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_2103_, v_inst_2104_, v_x_2105_, v___x_2110_, v___x_2111_, v_x_2106_, v_x_2107_);
    return v___x_2112_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__2(
    mut v_00_u03b1_2113_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2114_: *mut crate::leanh::LeanObject,
    mut v_inst_2115_: *mut crate::leanh::LeanObject,
    mut v_inst_2116_: *mut crate::leanh::LeanObject,
    mut v_x_2117_: *mut crate::leanh::LeanObject,
    mut v___y_2118_: *mut crate::leanh::LeanObject,
    mut v___y_2119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2120_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_2115_, v_inst_2116_, v_x_2117_, v___y_2118_, v___y_2119_);
    return v___x_2120_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(
    mut v_inst_2121_: *mut crate::leanh::LeanObject,
    mut v_inst_2122_: *mut crate::leanh::LeanObject,
    mut v_x_2123_: *mut crate::leanh::LeanObject,
    mut v___y_2124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2125_ = crate::leanh::lean_box(0);
    v___x_2126_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_2121_, v_inst_2122_, v_x_2123_, v___y_2124_, v___x_2125_);
    return v___x_2126_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__5(
    mut v_00_u03b1_2127_: *mut crate::leanh::LeanObject,
    mut v_inst_2128_: *mut crate::leanh::LeanObject,
    mut v_inst_2129_: *mut crate::leanh::LeanObject,
    mut v_x_2130_: *mut crate::leanh::LeanObject,
    mut v___y_2131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2132_ = l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(
        v_inst_2128_,
        v_inst_2129_,
        v_x_2130_,
        v___y_2131_,
    );
    return v___x_2132_;
}
pub unsafe fn _init_l_Lean_ShareCommon_persistentObjectFactory___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ = l_Lean_ShareCommon_persistentObjectFactory___closed__6;
    v___x_2147_ = l_ShareCommon_StateFactory_mkImpl(v___x_2146_);
    return v___x_2147_;
}
pub unsafe fn _init_l_Lean_ShareCommon_persistentObjectFactory() -> *mut crate::leanh::LeanObject {
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2148_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_persistentObjectFactory___closed__7),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_persistentObjectFactory___closed__7_once),
        _init_l_Lean_ShareCommon_persistentObjectFactory___closed__7,
    );
    return v___x_2148_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(
    mut v_inst_2149_: *mut crate::leanh::LeanObject,
    mut v_inst_2150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2151_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(crate::leanh::lean_box(0), v_inst_2149_, v_inst_2150_, crate::leanh::lean_box(0));
    return v___x_2151_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg___boxed(
    mut v_inst_2152_: *mut crate::leanh::LeanObject,
    mut v_inst_2153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2154_ =
        l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(v_inst_2152_, v_inst_2153_);
    crate::leanh::lean_dec_ref(v_inst_2153_);
    crate::leanh::lean_dec_ref(v_inst_2152_);
    return v_res_2154_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg(
    mut v_inst_2155_: *mut crate::leanh::LeanObject,
    mut v_inst_2156_: *mut crate::leanh::LeanObject,
    mut v_x_2157_: *mut crate::leanh::LeanObject,
    mut v___y_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_2155_, v_inst_2156_, v_x_2157_, v___y_2158_);
    return v___x_2159_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg___boxed(
    mut v_inst_2160_: *mut crate::leanh::LeanObject,
    mut v_inst_2161_: *mut crate::leanh::LeanObject,
    mut v_x_2162_: *mut crate::leanh::LeanObject,
    mut v___y_2163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2164_ = l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg(
        v_inst_2160_,
        v_inst_2161_,
        v_x_2162_,
        v___y_2163_,
    );
    crate::leanh::lean_dec_ref(v_x_2162_);
    return v_res_2164_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__2___redArg(
    mut v_inst_2165_: *mut crate::leanh::LeanObject,
    mut v_inst_2166_: *mut crate::leanh::LeanObject,
    mut v_x_2167_: *mut crate::leanh::LeanObject,
    mut v___y_2168_: *mut crate::leanh::LeanObject,
    mut v___y_2169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2170_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_2165_, v_inst_2166_, v_x_2167_, v___y_2168_, v___y_2169_);
    return v___x_2170_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(
    mut v_inst_2171_: *mut crate::leanh::LeanObject,
    mut v_inst_2172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2173_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(crate::leanh::lean_box(0), v_inst_2171_, v_inst_2172_, crate::leanh::lean_box(0));
    return v___x_2173_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg___boxed(
    mut v_inst_2174_: *mut crate::leanh::LeanObject,
    mut v_inst_2175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2176_ =
        l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(v_inst_2174_, v_inst_2175_);
    crate::leanh::lean_dec_ref(v_inst_2175_);
    crate::leanh::lean_dec_ref(v_inst_2174_);
    return v_res_2176_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(
    mut v_00_u03b1_2177_: *mut crate::leanh::LeanObject,
    mut v_inst_2178_: *mut crate::leanh::LeanObject,
    mut v_inst_2179_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2180_: *mut crate::leanh::LeanObject,
    mut v_x_2181_: *mut crate::leanh::LeanObject,
    mut v_x_2182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2183_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_2178_, v_inst_2179_, v_x_2181_, v_x_2182_);
    return v___x_2183_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___boxed(
    mut v_00_u03b1_2184_: *mut crate::leanh::LeanObject,
    mut v_inst_2185_: *mut crate::leanh::LeanObject,
    mut v_inst_2186_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2187_: *mut crate::leanh::LeanObject,
    mut v_x_2188_: *mut crate::leanh::LeanObject,
    mut v_x_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2190_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(v_00_u03b1_2184_, v_inst_2185_, v_inst_2186_, v_00_u03b2_2187_, v_x_2188_, v_x_2189_);
    crate::leanh::lean_dec_ref(v_x_2188_);
    return v_res_2190_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4(
    mut v_00_u03b1_2191_: *mut crate::leanh::LeanObject,
    mut v_inst_2192_: *mut crate::leanh::LeanObject,
    mut v_inst_2193_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2194_: *mut crate::leanh::LeanObject,
    mut v_x_2195_: *mut crate::leanh::LeanObject,
    mut v_x_2196_: *mut crate::leanh::LeanObject,
    mut v_x_2197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2198_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_2192_, v_inst_2193_, v_x_2195_, v_x_2196_, v_x_2197_);
    return v___x_2198_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(
    mut v_00_u03b1_2199_: *mut crate::leanh::LeanObject,
    mut v_inst_2200_: *mut crate::leanh::LeanObject,
    mut v_inst_2201_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2202_: *mut crate::leanh::LeanObject,
    mut v_x_2203_: *mut crate::leanh::LeanObject,
    mut v_x_2204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2205_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_2200_, v_inst_2201_, v_x_2203_, v_x_2204_);
    return v___x_2205_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___boxed(
    mut v_00_u03b1_2206_: *mut crate::leanh::LeanObject,
    mut v_inst_2207_: *mut crate::leanh::LeanObject,
    mut v_inst_2208_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2209_: *mut crate::leanh::LeanObject,
    mut v_x_2210_: *mut crate::leanh::LeanObject,
    mut v_x_2211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2212_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(v_00_u03b1_2206_, v_inst_2207_, v_inst_2208_, v_00_u03b2_2209_, v_x_2210_, v_x_2211_);
    crate::leanh::lean_dec_ref(v_x_2210_);
    return v_res_2212_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(
    mut v_00_u03b1_2213_: *mut crate::leanh::LeanObject,
    mut v_inst_2214_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2215_: *mut crate::leanh::LeanObject,
    mut v_x_2216_: *mut crate::leanh::LeanObject,
    mut v_x_2217_: usize,
    mut v_x_2218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_x_2216_);
    v___x_2219_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_2214_, v_x_2216_, v_x_2217_, v_x_2218_);
    return v___x_2219_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___boxed(
    mut v_00_u03b1_2220_: *mut crate::leanh::LeanObject,
    mut v_inst_2221_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2222_: *mut crate::leanh::LeanObject,
    mut v_x_2223_: *mut crate::leanh::LeanObject,
    mut v_x_2224_: *mut crate::leanh::LeanObject,
    mut v_x_2225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1476__boxed_2226_: usize = 0;
    let mut v_res_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1476__boxed_2226_ = crate::leanh::lean_unbox_usize(v_x_2224_);
    crate::leanh::lean_dec(v_x_2224_);
    v_res_2227_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(v_00_u03b1_2220_, v_inst_2221_, v_00_u03b2_2222_, v_x_2223_, v_x_1476__boxed_2226_, v_x_2225_);
    crate::leanh::lean_dec_ref(v_x_2223_);
    return v_res_2227_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(
    mut v_00_u03b1_2228_: *mut crate::leanh::LeanObject,
    mut v_inst_2229_: *mut crate::leanh::LeanObject,
    mut v_inst_2230_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2231_: *mut crate::leanh::LeanObject,
    mut v_x_2232_: *mut crate::leanh::LeanObject,
    mut v_x_2233_: usize,
    mut v_x_2234_: usize,
    mut v_x_2235_: *mut crate::leanh::LeanObject,
    mut v_x_2236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2237_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_2229_, v_inst_2230_, v_x_2232_, v_x_2233_, v_x_2234_, v_x_2235_, v_x_2236_);
    return v___x_2237_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_2238_: *mut crate::leanh::LeanObject,
    mut v_inst_2239_: *mut crate::leanh::LeanObject,
    mut v_inst_2240_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2241_: *mut crate::leanh::LeanObject,
    mut v_x_2242_: *mut crate::leanh::LeanObject,
    mut v_x_2243_: *mut crate::leanh::LeanObject,
    mut v_x_2244_: *mut crate::leanh::LeanObject,
    mut v_x_2245_: *mut crate::leanh::LeanObject,
    mut v_x_2246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1494__boxed_2247_: usize = 0;
    let mut v_x_1495__boxed_2248_: usize = 0;
    let mut v_res_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1494__boxed_2247_ = crate::leanh::lean_unbox_usize(v_x_2243_);
    crate::leanh::lean_dec(v_x_2243_);
    v_x_1495__boxed_2248_ = crate::leanh::lean_unbox_usize(v_x_2244_);
    crate::leanh::lean_dec(v_x_2244_);
    v_res_2249_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(v_00_u03b1_2238_, v_inst_2239_, v_inst_2240_, v_00_u03b2_2241_, v_x_2242_, v_x_1494__boxed_2247_, v_x_1495__boxed_2248_, v_x_2245_, v_x_2246_);
    return v_res_2249_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(
    mut v_00_u03b1_2250_: *mut crate::leanh::LeanObject,
    mut v_inst_2251_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2252_: *mut crate::leanh::LeanObject,
    mut v_x_2253_: *mut crate::leanh::LeanObject,
    mut v_x_2254_: usize,
    mut v_x_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_x_2253_);
    v___x_2256_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_2251_, v_x_2253_, v_x_2254_, v_x_2255_);
    return v___x_2256_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___boxed(
    mut v_00_u03b1_2257_: *mut crate::leanh::LeanObject,
    mut v_inst_2258_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2259_: *mut crate::leanh::LeanObject,
    mut v_x_2260_: *mut crate::leanh::LeanObject,
    mut v_x_2261_: *mut crate::leanh::LeanObject,
    mut v_x_2262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1519__boxed_2263_: usize = 0;
    let mut v_res_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1519__boxed_2263_ = crate::leanh::lean_unbox_usize(v_x_2261_);
    crate::leanh::lean_dec(v_x_2261_);
    v_res_2264_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(v_00_u03b1_2257_, v_inst_2258_, v_00_u03b2_2259_, v_x_2260_, v_x_1519__boxed_2263_, v_x_2262_);
    crate::leanh::lean_dec_ref(v_x_2260_);
    return v_res_2264_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(
    mut v_00_u03b1_2265_: *mut crate::leanh::LeanObject,
    mut v_inst_2266_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2267_: *mut crate::leanh::LeanObject,
    mut v_keys_2268_: *mut crate::leanh::LeanObject,
    mut v_vals_2269_: *mut crate::leanh::LeanObject,
    mut v_heq_2270_: *mut crate::leanh::LeanObject,
    mut v_i_2271_: *mut crate::leanh::LeanObject,
    mut v_k_2272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2273_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_2266_, v_keys_2268_, v_vals_2269_, v_i_2271_, v_k_2272_);
    return v___x_2273_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___boxed(
    mut v_00_u03b1_2274_: *mut crate::leanh::LeanObject,
    mut v_inst_2275_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2276_: *mut crate::leanh::LeanObject,
    mut v_keys_2277_: *mut crate::leanh::LeanObject,
    mut v_vals_2278_: *mut crate::leanh::LeanObject,
    mut v_heq_2279_: *mut crate::leanh::LeanObject,
    mut v_i_2280_: *mut crate::leanh::LeanObject,
    mut v_k_2281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2282_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(v_00_u03b1_2274_, v_inst_2275_, v_00_u03b2_2276_, v_keys_2277_, v_vals_2278_, v_heq_2279_, v_i_2280_, v_k_2281_);
    crate::leanh::lean_dec_ref(v_vals_2278_);
    crate::leanh::lean_dec_ref(v_keys_2277_);
    return v_res_2282_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11(
    mut v_00_u03b1_2283_: *mut crate::leanh::LeanObject,
    mut v_inst_2284_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2285_: *mut crate::leanh::LeanObject,
    mut v_n_2286_: *mut crate::leanh::LeanObject,
    mut v_k_2287_: *mut crate::leanh::LeanObject,
    mut v_v_2288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2289_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(v_inst_2284_, v_n_2286_, v_k_2287_, v_v_2288_);
    return v___x_2289_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(
    mut v_00_u03b1_2290_: *mut crate::leanh::LeanObject,
    mut v_inst_2291_: *mut crate::leanh::LeanObject,
    mut v_inst_2292_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2293_: *mut crate::leanh::LeanObject,
    mut v_depth_2294_: usize,
    mut v_keys_2295_: *mut crate::leanh::LeanObject,
    mut v_vals_2296_: *mut crate::leanh::LeanObject,
    mut v_heq_2297_: *mut crate::leanh::LeanObject,
    mut v_i_2298_: *mut crate::leanh::LeanObject,
    mut v_entries_2299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2300_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_2291_, v_inst_2292_, v_depth_2294_, v_keys_2295_, v_vals_2296_, v_i_2298_, v_entries_2299_);
    return v___x_2300_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___boxed(
    mut v_00_u03b1_2301_: *mut crate::leanh::LeanObject,
    mut v_inst_2302_: *mut crate::leanh::LeanObject,
    mut v_inst_2303_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2304_: *mut crate::leanh::LeanObject,
    mut v_depth_2305_: *mut crate::leanh::LeanObject,
    mut v_keys_2306_: *mut crate::leanh::LeanObject,
    mut v_vals_2307_: *mut crate::leanh::LeanObject,
    mut v_heq_2308_: *mut crate::leanh::LeanObject,
    mut v_i_2309_: *mut crate::leanh::LeanObject,
    mut v_entries_2310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2311_: usize = 0;
    let mut v_res_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2311_ = crate::leanh::lean_unbox_usize(v_depth_2305_);
    crate::leanh::lean_dec(v_depth_2305_);
    v_res_2312_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(v_00_u03b1_2301_, v_inst_2302_, v_inst_2303_, v_00_u03b2_2304_, v_depth_boxed_2311_, v_keys_2306_, v_vals_2307_, v_heq_2308_, v_i_2309_, v_entries_2310_);
    crate::leanh::lean_dec_ref(v_vals_2307_);
    crate::leanh::lean_dec_ref(v_keys_2306_);
    return v_res_2312_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(
    mut v_00_u03b1_2313_: *mut crate::leanh::LeanObject,
    mut v_inst_2314_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2315_: *mut crate::leanh::LeanObject,
    mut v_keys_2316_: *mut crate::leanh::LeanObject,
    mut v_vals_2317_: *mut crate::leanh::LeanObject,
    mut v_heq_2318_: *mut crate::leanh::LeanObject,
    mut v_i_2319_: *mut crate::leanh::LeanObject,
    mut v_k_2320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2321_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_2314_, v_keys_2316_, v_vals_2317_, v_i_2319_, v_k_2320_);
    return v___x_2321_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___boxed(
    mut v_00_u03b1_2322_: *mut crate::leanh::LeanObject,
    mut v_inst_2323_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2324_: *mut crate::leanh::LeanObject,
    mut v_keys_2325_: *mut crate::leanh::LeanObject,
    mut v_vals_2326_: *mut crate::leanh::LeanObject,
    mut v_heq_2327_: *mut crate::leanh::LeanObject,
    mut v_i_2328_: *mut crate::leanh::LeanObject,
    mut v_k_2329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2330_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(v_00_u03b1_2322_, v_inst_2323_, v_00_u03b2_2324_, v_keys_2325_, v_vals_2326_, v_heq_2327_, v_i_2328_, v_k_2329_);
    crate::leanh::lean_dec_ref(v_vals_2326_);
    crate::leanh::lean_dec_ref(v_keys_2325_);
    return v_res_2330_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13(
    mut v_00_u03b1_2331_: *mut crate::leanh::LeanObject,
    mut v_inst_2332_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2333_: *mut crate::leanh::LeanObject,
    mut v_x_2334_: *mut crate::leanh::LeanObject,
    mut v_x_2335_: *mut crate::leanh::LeanObject,
    mut v_x_2336_: *mut crate::leanh::LeanObject,
    mut v_x_2337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2338_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(v_inst_2332_, v_x_2334_, v_x_2335_, v_x_2336_, v_x_2337_);
    return v___x_2338_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(
    mut v_inst_2339_: *mut crate::leanh::LeanObject,
    mut v_a_2340_: *mut crate::leanh::LeanObject,
    mut v_a_2341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2342_ = crate::leanh::lean_ctor_get(v_inst_2339_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2342_);
    crate::leanh::lean_dec_ref(v_inst_2339_);
    v_toPure_2343_ = crate::leanh::lean_ctor_get(v_toApplicative_2342_, 1);
    crate::leanh::lean_inc(v_toPure_2343_);
    crate::leanh::lean_dec_ref(v_toApplicative_2342_);
    v___x_2344_ = l_Lean_ShareCommon_objectFactory;
    v___x_2345_ = lean_state_sharecommon(v___x_2344_, v_a_2341_, v_a_2340_);
    v___x_2346_ =
        crate::leanh::lean_apply_2(v_toPure_2343_, crate::leanh::lean_box(0), v___x_2345_);
    return v___x_2346_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_withShareCommon(
    mut v_m_2347_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2348_: *mut crate::leanh::LeanObject,
    mut v_inst_2349_: *mut crate::leanh::LeanObject,
    mut v_a_2350_: *mut crate::leanh::LeanObject,
    mut v_a_2351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2352_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(
        v_inst_2349_,
        v_a_2350_,
        v_a_2351_,
    );
    return v___x_2352_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(
    mut v_inst_2353_: *mut crate::leanh::LeanObject,
    mut v_a_2354_: *mut crate::leanh::LeanObject,
    mut v_a_2355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2356_ = crate::leanh::lean_ctor_get(v_inst_2353_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2356_);
    crate::leanh::lean_dec_ref(v_inst_2353_);
    v_toPure_2357_ = crate::leanh::lean_ctor_get(v_toApplicative_2356_, 1);
    crate::leanh::lean_inc(v_toPure_2357_);
    crate::leanh::lean_dec_ref(v_toApplicative_2356_);
    v___x_2358_ = l_Lean_ShareCommon_persistentObjectFactory;
    v___x_2359_ = lean_state_sharecommon(v___x_2358_, v_a_2355_, v_a_2354_);
    v___x_2360_ =
        crate::leanh::lean_apply_2(v_toPure_2357_, crate::leanh::lean_box(0), v___x_2359_);
    return v___x_2360_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonT_withShareCommon(
    mut v_m_2361_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2362_: *mut crate::leanh::LeanObject,
    mut v_inst_2363_: *mut crate::leanh::LeanObject,
    mut v_a_2364_: *mut crate::leanh::LeanObject,
    mut v_a_2365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2366_ = l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(
        v_inst_2363_,
        v_a_2364_,
        v_a_2365_,
    );
    return v___x_2366_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0(
    mut v_inst_2367_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
    mut v___y_2370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2371_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(
        v_inst_2367_,
        v___y_2369_,
        v___y_2370_,
    );
    return v___x_2371_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg(
    mut v_inst_2372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2373_ = crate::leanh::lean_alloc_closure(
        l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2373_, 0, v_inst_2372_);
    return v___f_2373_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_monadShareCommon(
    mut v_m_2374_: *mut crate::leanh::LeanObject,
    mut v_inst_2375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2376_ = crate::leanh::lean_alloc_closure(
        l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2376_, 0, v_inst_2375_);
    return v___f_2376_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0(
    mut v_inst_2377_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2381_ = l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(
        v_inst_2377_,
        v___y_2379_,
        v___y_2380_,
    );
    return v___x_2381_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg(
    mut v_inst_2382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2383_ = crate::leanh::lean_alloc_closure(
        l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2383_, 0, v_inst_2382_);
    return v___f_2383_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonT_monadShareCommon(
    mut v_m_2384_: *mut crate::leanh::LeanObject,
    mut v_inst_2385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2386_ = crate::leanh::lean_alloc_closure(
        l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2386_, 0, v_inst_2385_);
    return v___f_2386_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(
    mut v_x_2387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2388_ = crate::leanh::lean_ctor_get(v_x_2387_, 0);
    crate::leanh::lean_inc(v_fst_2388_);
    return v_fst_2388_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0___boxed(
    mut v_x_2389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2390_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(v_x_2389_);
    crate::leanh::lean_dec_ref(v_x_2389_);
    return v_res_2390_;
}
pub unsafe fn _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2392_ = l_Lean_ShareCommon_objectFactory;
    v___x_2393_ = l_ShareCommon_mkStateImpl(v___x_2392_);
    return v___x_2393_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_run___redArg(
    mut v_inst_2394_: *mut crate::leanh::LeanObject,
    mut v_x_2395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2396_ = crate::leanh::lean_ctor_get(v_inst_2394_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2396_);
    crate::leanh::lean_dec_ref(v_inst_2394_);
    v_toFunctor_2397_ = crate::leanh::lean_ctor_get(v_toApplicative_2396_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_2397_);
    crate::leanh::lean_dec_ref(v_toApplicative_2396_);
    v_map_2398_ = crate::leanh::lean_ctor_get(v_toFunctor_2397_, 0);
    crate::leanh::lean_inc(v_map_2398_);
    crate::leanh::lean_dec_ref(v_toFunctor_2397_);
    v___f_2399_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0;
    v___x_2400_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once),
        _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1,
    );
    v___x_2401_ = crate::leanh::lean_apply_1(v_x_2395_, v___x_2400_);
    v___x_2402_ = crate::leanh::lean_apply_4(
        v_map_2398_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2399_,
        v___x_2401_,
    );
    return v___x_2402_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_run(
    mut v_m_2403_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2404_: *mut crate::leanh::LeanObject,
    mut v_inst_2405_: *mut crate::leanh::LeanObject,
    mut v_x_2406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2407_ = crate::leanh::lean_ctor_get(v_inst_2405_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2407_);
    crate::leanh::lean_dec_ref(v_inst_2405_);
    v_toFunctor_2408_ = crate::leanh::lean_ctor_get(v_toApplicative_2407_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_2408_);
    crate::leanh::lean_dec_ref(v_toApplicative_2407_);
    v_map_2409_ = crate::leanh::lean_ctor_get(v_toFunctor_2408_, 0);
    crate::leanh::lean_inc(v_map_2409_);
    crate::leanh::lean_dec_ref(v_toFunctor_2408_);
    v___f_2410_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0;
    v___x_2411_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once),
        _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1,
    );
    v___x_2412_ = crate::leanh::lean_apply_1(v_x_2406_, v___x_2411_);
    v___x_2413_ = crate::leanh::lean_apply_4(
        v_map_2409_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2410_,
        v___x_2412_,
    );
    return v___x_2413_;
}
pub unsafe fn _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2414_ = l_Lean_ShareCommon_persistentObjectFactory;
    v___x_2415_ = l_ShareCommon_mkStateImpl(v___x_2414_);
    return v___x_2415_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonT_run___redArg(
    mut v_inst_2416_: *mut crate::leanh::LeanObject,
    mut v_x_2417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2418_ = crate::leanh::lean_ctor_get(v_inst_2416_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2418_);
    crate::leanh::lean_dec_ref(v_inst_2416_);
    v_toFunctor_2419_ = crate::leanh::lean_ctor_get(v_toApplicative_2418_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_2419_);
    crate::leanh::lean_dec_ref(v_toApplicative_2418_);
    v_map_2420_ = crate::leanh::lean_ctor_get(v_toFunctor_2419_, 0);
    crate::leanh::lean_inc(v_map_2420_);
    crate::leanh::lean_dec_ref(v_toFunctor_2419_);
    v___f_2421_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0;
    v___x_2422_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once),
        _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0,
    );
    v___x_2423_ = crate::leanh::lean_apply_1(v_x_2417_, v___x_2422_);
    v___x_2424_ = crate::leanh::lean_apply_4(
        v_map_2420_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2421_,
        v___x_2423_,
    );
    return v___x_2424_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonT_run(
    mut v_m_2425_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2426_: *mut crate::leanh::LeanObject,
    mut v_inst_2427_: *mut crate::leanh::LeanObject,
    mut v_x_2428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2429_ = crate::leanh::lean_ctor_get(v_inst_2427_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2429_);
    crate::leanh::lean_dec_ref(v_inst_2427_);
    v_toFunctor_2430_ = crate::leanh::lean_ctor_get(v_toApplicative_2429_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_2430_);
    crate::leanh::lean_dec_ref(v_toApplicative_2429_);
    v_map_2431_ = crate::leanh::lean_ctor_get(v_toFunctor_2430_, 0);
    crate::leanh::lean_inc(v_map_2431_);
    crate::leanh::lean_dec_ref(v_toFunctor_2430_);
    v___f_2432_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0;
    v___x_2433_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once),
        _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0,
    );
    v___x_2434_ = crate::leanh::lean_apply_1(v_x_2428_, v___x_2433_);
    v___x_2435_ = crate::leanh::lean_apply_4(
        v_map_2431_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2432_,
        v___x_2434_,
    );
    return v___x_2435_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonM_run___redArg(
    mut v_a_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2437_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once),
        _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1,
    );
    v___x_2438_ = crate::leanh::lean_apply_1(v_a_2436_, v___x_2437_);
    v_fst_2439_ = crate::leanh::lean_ctor_get(v___x_2438_, 0);
    crate::leanh::lean_inc(v_fst_2439_);
    crate::leanh::lean_dec_ref(v___x_2438_);
    return v_fst_2439_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonM_run(
    mut v_00_u03b1_2440_: *mut crate::leanh::LeanObject,
    mut v_a_2441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2442_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once),
        _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1,
    );
    v___x_2443_ = crate::leanh::lean_apply_1(v_a_2441_, v___x_2442_);
    v_fst_2444_ = crate::leanh::lean_ctor_get(v___x_2443_, 0);
    crate::leanh::lean_inc(v_fst_2444_);
    crate::leanh::lean_dec_ref(v___x_2443_);
    return v_fst_2444_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonM_run___redArg(
    mut v_a_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once),
        _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0,
    );
    v___x_2447_ = crate::leanh::lean_apply_1(v_a_2445_, v___x_2446_);
    v_fst_2448_ = crate::leanh::lean_ctor_get(v___x_2447_, 0);
    crate::leanh::lean_inc(v_fst_2448_);
    crate::leanh::lean_dec_ref(v___x_2447_);
    return v_fst_2448_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonM_run(
    mut v_00_u03b1_2449_: *mut crate::leanh::LeanObject,
    mut v_a_2450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2451_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once),
        _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0,
    );
    v___x_2452_ = crate::leanh::lean_apply_1(v_a_2450_, v___x_2451_);
    v_fst_2453_ = crate::leanh::lean_ctor_get(v___x_2452_, 0);
    crate::leanh::lean_inc(v_fst_2453_);
    crate::leanh::lean_dec_ref(v___x_2452_);
    return v_fst_2453_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(
    mut v_a_2454_: *mut crate::leanh::LeanObject,
    mut v_a_2455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2456_ = l_Lean_ShareCommon_objectFactory;
    v___x_2457_ = lean_state_sharecommon(v___x_2456_, v_a_2455_, v_a_2454_);
    return v___x_2457_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0(
    mut v_00_u03b1_2458_: *mut crate::leanh::LeanObject,
    mut v_a_2459_: *mut crate::leanh::LeanObject,
    mut v_a_2460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2461_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(v_a_2459_, v_a_2460_);
    return v___x_2461_;
}
pub unsafe fn l_Lean_ShareCommon_shareCommon___redArg(
    mut v_a_2462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2463_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once),
        _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1,
    );
    v___x_2464_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(v_a_2462_, v___x_2463_);
    v_fst_2465_ = crate::leanh::lean_ctor_get(v___x_2464_, 0);
    crate::leanh::lean_inc(v_fst_2465_);
    crate::leanh::lean_dec_ref(v___x_2464_);
    return v_fst_2465_;
}
pub unsafe fn l_Lean_ShareCommon_shareCommon(
    mut v_00_u03b1_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2468_ = l_Lean_ShareCommon_shareCommon___redArg(v_a_2467_);
    return v___x_2468_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_ShareCommon(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_ShareCommon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentHashSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_ShareCommon_objectFactory = _init_l_Lean_ShareCommon_objectFactory();
    crate::leanh::lean_mark_persistent(l_Lean_ShareCommon_objectFactory);
    l_Lean_ShareCommon_persistentObjectFactory = _init_l_Lean_ShareCommon_persistentObjectFactory();
    crate::leanh::lean_mark_persistent(l_Lean_ShareCommon_persistentObjectFactory);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_ShareCommon(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_ShareCommon(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_ShareCommon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashSet_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_PersistentHashSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ShareCommon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_ShareCommon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_ShareCommon(builtin);
}
