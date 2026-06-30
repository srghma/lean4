// Lean compiler output
// Module: Lean.Util.ShareCommon
// Imports: Init.ShareCommon Std.Data.HashSet.Basic Lean.Data.PersistentHashSet
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_size, lean_array_push, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_state_sharecommon, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
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
pub static l_Lean_ShareCommon_objectFactory___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ShareCommon_objectFactory___elam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ShareCommon_objectFactory___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ShareCommon_objectFactory___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ShareCommon_objectFactory___elam__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ShareCommon_objectFactory___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ShareCommon_objectFactory___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ShareCommon_objectFactory___elam__2 as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ShareCommon_objectFactory___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ShareCommon_objectFactory___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ShareCommon_objectFactory___elam__3___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ShareCommon_objectFactory___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ShareCommon_objectFactory___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ShareCommon_objectFactory___elam__4___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ShareCommon_objectFactory___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ShareCommon_objectFactory___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ShareCommon_objectFactory___elam__5 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ShareCommon_objectFactory___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ShareCommon_objectFactory___closed__6_value: leanh::LeanCtorObject<6> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 6
                + 0) as u16,
            other: 6,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_ShareCommon_objectFactory___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_objectFactory___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_ShareCommon_objectFactory___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ShareCommon_objectFactory___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_ShareCommon_objectFactory: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ShareCommon_persistentObjectFactory___closed__0_value:
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
    m_fun: l_Lean_ShareCommon_persistentObjectFactory___elam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ShareCommon_persistentObjectFactory___closed__1_value:
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
    m_fun: l_Lean_ShareCommon_persistentObjectFactory___elam__1___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ShareCommon_persistentObjectFactory___closed__2_value:
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
    m_fun: l_Lean_ShareCommon_persistentObjectFactory___elam__2 as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ShareCommon_persistentObjectFactory___closed__3_value:
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
    m_fun: l_Lean_ShareCommon_persistentObjectFactory___elam__3___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ShareCommon_persistentObjectFactory___closed__4_value:
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
    m_fun: l_Lean_ShareCommon_persistentObjectFactory___elam__4___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ShareCommon_persistentObjectFactory___closed__5_value:
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
    m_fun: l_Lean_ShareCommon_persistentObjectFactory___elam__5 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ShareCommon_persistentObjectFactory___closed__6_value:
    leanh::LeanCtorObject<6> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 6
            + 0) as u16,
        other: 6,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_persistentObjectFactory___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ShareCommon_persistentObjectFactory___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_ShareCommon_persistentObjectFactory: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0_value:
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
    m_fun: l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__0___redArg(
    mut v_x_1235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1236_ = leanh::lean_unsigned_to_nat(0);
    v___x_1237_ = leanh::lean_unsigned_to_nat(4);
    v___x_1238_ = lean_nat_mul(v_x_1235_, v___x_1237_);
    v___x_1239_ = leanh::lean_unsigned_to_nat(3);
    v___x_1240_ = lean_nat_div(v___x_1238_, v___x_1239_);
    leanh::lean_dec(v___x_1238_);
    v___x_1241_ = l_Nat_nextPowerOfTwo(v___x_1240_);
    leanh::lean_dec(v___x_1240_);
    v___x_1242_ = leanh::lean_box(0);
    v___x_1243_ = lean_mk_array(v___x_1241_, v___x_1242_);
    v___x_1244_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1244_, 0, v___x_1236_);
    leanh::lean_ctor_set(v___x_1244_, 1, v___x_1243_);
    return v___x_1244_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__0___redArg___boxed(
    mut v_x_1245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1246_ = l_Lean_ShareCommon_objectFactory___elam__0___redArg(v_x_1245_);
    leanh::lean_dec(v_x_1245_);
    return v_res_1246_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__0(
    mut v_00_u03b1_1247_: *mut leanh::LeanObject,
    mut v_00_u03b2_1248_: *mut leanh::LeanObject,
    mut v_inst_1249_: *mut leanh::LeanObject,
    mut v_inst_1250_: *mut leanh::LeanObject,
    mut v_x_1251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = l_Lean_ShareCommon_objectFactory___elam__0___redArg(v_x_1251_);
    return v___x_1252_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__0___boxed(
    mut v_00_u03b1_1253_: *mut leanh::LeanObject,
    mut v_00_u03b2_1254_: *mut leanh::LeanObject,
    mut v_inst_1255_: *mut leanh::LeanObject,
    mut v_inst_1256_: *mut leanh::LeanObject,
    mut v_x_1257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Lean_ShareCommon_objectFactory___elam__0(
        v_00_u03b1_1253_,
        v_00_u03b2_1254_,
        v_inst_1255_,
        v_inst_1256_,
        v_x_1257_,
    );
    leanh::lean_dec(v_x_1257_);
    leanh::lean_dec_ref(v_inst_1256_);
    leanh::lean_dec_ref(v_inst_1255_);
    return v_res_1258_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__3___redArg(
    mut v_x_1259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1260_ = leanh::lean_unsigned_to_nat(0);
    v___x_1261_ = leanh::lean_unsigned_to_nat(4);
    v___x_1262_ = lean_nat_mul(v_x_1259_, v___x_1261_);
    v___x_1263_ = leanh::lean_unsigned_to_nat(3);
    v___x_1264_ = lean_nat_div(v___x_1262_, v___x_1263_);
    leanh::lean_dec(v___x_1262_);
    v___x_1265_ = l_Nat_nextPowerOfTwo(v___x_1264_);
    leanh::lean_dec(v___x_1264_);
    v___x_1266_ = leanh::lean_box(0);
    v___x_1267_ = lean_mk_array(v___x_1265_, v___x_1266_);
    v___x_1268_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1268_, 0, v___x_1260_);
    leanh::lean_ctor_set(v___x_1268_, 1, v___x_1267_);
    return v___x_1268_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__3___redArg___boxed(
    mut v_x_1269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1270_ = l_Lean_ShareCommon_objectFactory___elam__3___redArg(v_x_1269_);
    leanh::lean_dec(v_x_1269_);
    return v_res_1270_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__3(
    mut v_00_u03b1_1271_: *mut leanh::LeanObject,
    mut v_inst_1272_: *mut leanh::LeanObject,
    mut v_inst_1273_: *mut leanh::LeanObject,
    mut v_x_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_Lean_ShareCommon_objectFactory___elam__3___redArg(v_x_1274_);
    return v___x_1275_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__3___boxed(
    mut v_00_u03b1_1276_: *mut leanh::LeanObject,
    mut v_inst_1277_: *mut leanh::LeanObject,
    mut v_inst_1278_: *mut leanh::LeanObject,
    mut v_x_1279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1280_ = l_Lean_ShareCommon_objectFactory___elam__3(
        v_00_u03b1_1276_,
        v_inst_1277_,
        v_inst_1278_,
        v_x_1279_,
    );
    leanh::lean_dec(v_x_1279_);
    leanh::lean_dec_ref(v_inst_1278_);
    leanh::lean_dec_ref(v_inst_1277_);
    return v_res_1280_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(
    mut v_inst_1281_: *mut leanh::LeanObject,
    mut v_a_1282_: *mut leanh::LeanObject,
    mut v_x_1283_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1284_: u8 = 0;
    let mut v_key_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: u8 = 0;
    let mut v___x_1290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1283_) == 0 {
                    leanh::lean_dec(v_a_1282_);
                    leanh::lean_dec_ref(v_inst_1281_);
                    v___x_1284_ = 0;
                    return v___x_1284_;
                } else {
                    v_key_1285_ = leanh::lean_ctor_get(v_x_1283_, 0);
                    leanh::lean_inc(v_key_1285_);
                    v_tail_1286_ = leanh::lean_ctor_get(v_x_1283_, 2);
                    leanh::lean_inc(v_tail_1286_);
                    leanh::lean_dec_ref_known(v_x_1283_, 3);
                    leanh::lean_inc_ref(v_inst_1281_);
                    leanh::lean_inc(v_a_1282_);
                    v___x_1287_ = leanh::lean_apply_2(v_inst_1281_, v_key_1285_, v_a_1282_);
                    v___x_1288_ = (leanh::lean_unbox(v___x_1287_) as u8);
                    if v___x_1288_ == 0 {
                        v_x_1283_ = v_tail_1286_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1286_);
                        leanh::lean_dec(v_a_1282_);
                        leanh::lean_dec_ref(v_inst_1281_);
                        v___x_1290_ = (leanh::lean_unbox(v___x_1287_) as u8);
                        return v___x_1290_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg___boxed(
    mut v_inst_1291_: *mut leanh::LeanObject,
    mut v_a_1292_: *mut leanh::LeanObject,
    mut v_x_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1294_: u8 = 0;
    let mut v_r_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1294_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_1291_, v_a_1292_, v_x_1293_);
    v_r_1295_ = leanh::lean_box((v_res_1294_) as usize);
    return v_r_1295_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13___redArg(
    mut v_inst_1296_: *mut leanh::LeanObject,
    mut v_x_1297_: *mut leanh::LeanObject,
    mut v_x_1298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1304_: u8 = 0;
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1298_) == 0 {
                    leanh::lean_dec_ref(v_inst_1296_);
                    return v_x_1297_;
                } else {
                    v_key_1299_ = leanh::lean_ctor_get(v_x_1298_, 0);
                    v_value_1300_ = leanh::lean_ctor_get(v_x_1298_, 1);
                    v_tail_1301_ = leanh::lean_ctor_get(v_x_1298_, 2);
                    v_isSharedCheck_1326_ = (!leanh::lean_is_exclusive(v_x_1298_)) as u8;
                    if v_isSharedCheck_1326_ == 0 {
                        v___x_1303_ = v_x_1298_;
                        v_isShared_1304_ = v_isSharedCheck_1326_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1301_);
                        leanh::lean_inc(v_value_1300_);
                        leanh::lean_inc(v_key_1299_);
                        leanh::lean_dec(v_x_1298_);
                        v___x_1303_ = leanh::lean_box(0);
                        v_isShared_1304_ = v_isSharedCheck_1326_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1305_ = lean_array_get_size(v_x_1297_);
                leanh::lean_inc_ref(v_inst_1296_);
                leanh::lean_inc(v_key_1299_);
                v___x_1306_ = leanh::lean_apply_1(v_inst_1296_, v_key_1299_);
                v___x_1307_ = 32u64;
                v___x_1308_ = leanh::lean_unbox_uint64(v___x_1306_);
                v___x_1309_ = lean_uint64_shift_right(v___x_1308_, v___x_1307_);
                v___x_1310_ = leanh::lean_unbox_uint64(v___x_1306_);
                leanh::lean_dec_ref(v___x_1306_);
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
                leanh::lean_inc(v___x_1320_);
                if v_isShared_1304_ == 0 {
                    leanh::lean_ctor_set(v___x_1303_, 2, v___x_1320_);
                    v___x_1322_ = v___x_1303_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1325_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_key_1299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_value_1300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1325_, 2, v___x_1320_);
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
    mut v_inst_1327_: *mut leanh::LeanObject,
    mut v_i_1328_: *mut leanh::LeanObject,
    mut v_source_1329_: *mut leanh::LeanObject,
    mut v_target_1330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    let mut v_es_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1331_ = lean_array_get_size(v_source_1329_);
                v___x_1332_ = lean_nat_dec_lt(v_i_1328_, v___x_1331_);
                if v___x_1332_ == 0 {
                    leanh::lean_dec_ref(v_source_1329_);
                    leanh::lean_dec(v_i_1328_);
                    leanh::lean_dec_ref(v_inst_1327_);
                    return v_target_1330_;
                } else {
                    v_es_1333_ = lean_array_fget(v_source_1329_, v_i_1328_);
                    v___x_1334_ = leanh::lean_box(0);
                    v_source_1335_ = lean_array_fset(v_source_1329_, v_i_1328_, v___x_1334_);
                    leanh::lean_inc_ref(v_inst_1327_);
                    v_target_1336_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13___redArg(v_inst_1327_, v_target_1330_, v_es_1333_);
                    v___x_1337_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1338_ = lean_nat_add(v_i_1328_, v___x_1337_);
                    leanh::lean_dec(v_i_1328_);
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
    mut v_inst_1340_: *mut leanh::LeanObject,
    mut v_data_1341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1342_ = lean_array_get_size(v_data_1341_);
    v___x_1343_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1344_ = lean_nat_mul(v___x_1342_, v___x_1343_);
    v___x_1345_ = leanh::lean_unsigned_to_nat(0);
    v___x_1346_ = leanh::lean_box(0);
    v___x_1347_ = lean_mk_array(v_nbuckets_1344_, v___x_1346_);
    v___x_1348_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10___redArg(v_inst_1340_, v___x_1345_, v_data_1341_, v___x_1347_);
    return v___x_1348_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(
    mut v_inst_1349_: *mut leanh::LeanObject,
    mut v_inst_1350_: *mut leanh::LeanObject,
    mut v_m_1351_: *mut leanh::LeanObject,
    mut v_a_1352_: *mut leanh::LeanObject,
    mut v_b_1353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: u8 = 0;
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1375_: u8 = 0;
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: u8 = 0;
    let mut v_val_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1393_: u8 = 0;
    let mut v_unused_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1354_ = leanh::lean_ctor_get(v_m_1351_, 0);
                v_buckets_1355_ = leanh::lean_ctor_get(v_m_1351_, 1);
                v___x_1356_ = lean_array_get_size(v_buckets_1355_);
                leanh::lean_inc_ref(v_inst_1350_);
                leanh::lean_inc_n(v_a_1352_, 2);
                v___x_1357_ = leanh::lean_apply_1(v_inst_1350_, v_a_1352_);
                v___x_1358_ = 32u64;
                v___x_1359_ = leanh::lean_unbox_uint64(v___x_1357_);
                v___x_1360_ = lean_uint64_shift_right(v___x_1359_, v___x_1358_);
                v___x_1361_ = leanh::lean_unbox_uint64(v___x_1357_);
                leanh::lean_dec_ref(v___x_1357_);
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
                leanh::lean_inc(v_bkt_1371_);
                v___x_1372_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_1349_, v_a_1352_, v_bkt_1371_);
                if v___x_1372_ == 0 {
                    leanh::lean_inc_ref(v_buckets_1355_);
                    leanh::lean_inc(v_size_1354_);
                    v_isSharedCheck_1393_ = (!leanh::lean_is_exclusive(v_m_1351_)) as u8;
                    if v_isSharedCheck_1393_ == 0 {
                        v_unused_1394_ = leanh::lean_ctor_get(v_m_1351_, 1);
                        leanh::lean_dec(v_unused_1394_);
                        v_unused_1395_ = leanh::lean_ctor_get(v_m_1351_, 0);
                        leanh::lean_dec(v_unused_1395_);
                        v___x_1374_ = v_m_1351_;
                        v_isShared_1375_ = v_isSharedCheck_1393_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_1351_);
                        v___x_1374_ = leanh::lean_box(0);
                        v_isShared_1375_ = v_isSharedCheck_1393_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_1353_);
                    leanh::lean_dec(v_a_1352_);
                    leanh::lean_dec_ref(v_inst_1350_);
                    return v_m_1351_;
                }
            }
            1 => {
                v___x_1376_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_1377_ = lean_nat_add(v_size_1354_, v___x_1376_);
                leanh::lean_dec(v_size_1354_);
                leanh::lean_inc(v_bkt_1371_);
                v___x_1378_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1378_, 0, v_a_1352_);
                leanh::lean_ctor_set(v___x_1378_, 1, v_b_1353_);
                leanh::lean_ctor_set(v___x_1378_, 2, v_bkt_1371_);
                v_buckets_x27_1379_ = lean_array_uset(v_buckets_1355_, v___x_1370_, v___x_1378_);
                v___x_1380_ = leanh::lean_unsigned_to_nat(4);
                v___x_1381_ = lean_nat_mul(v_size_x27_1377_, v___x_1380_);
                v___x_1382_ = leanh::lean_unsigned_to_nat(3);
                v___x_1383_ = lean_nat_div(v___x_1381_, v___x_1382_);
                leanh::lean_dec(v___x_1381_);
                v___x_1384_ = lean_array_get_size(v_buckets_x27_1379_);
                v___x_1385_ = lean_nat_dec_le(v___x_1383_, v___x_1384_);
                leanh::lean_dec(v___x_1383_);
                if v___x_1385_ == 0 {
                    v_val_1386_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_1350_, v_buckets_x27_1379_);
                    if v_isShared_1375_ == 0 {
                        leanh::lean_ctor_set(v___x_1374_, 1, v_val_1386_);
                        leanh::lean_ctor_set(v___x_1374_, 0, v_size_x27_1377_);
                        v___x_1388_ = v___x_1374_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1389_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_size_x27_1377_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_val_1386_);
                        v___x_1388_ = v_reuseFailAlloc_1389_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_1350_);
                    if v_isShared_1375_ == 0 {
                        leanh::lean_ctor_set(v___x_1374_, 1, v_buckets_x27_1379_);
                        leanh::lean_ctor_set(v___x_1374_, 0, v_size_x27_1377_);
                        v___x_1391_ = v___x_1374_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1392_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_size_x27_1377_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_buckets_x27_1379_);
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
    mut v_inst_1396_: *mut leanh::LeanObject,
    mut v_inst_1397_: *mut leanh::LeanObject,
    mut v_x_1398_: *mut leanh::LeanObject,
    mut v___y_1399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ = leanh::lean_box(0);
    v___x_1401_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(v_inst_1396_, v_inst_1397_, v_x_1398_, v___y_1399_, v___x_1400_);
    return v___x_1401_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__5(
    mut v_00_u03b1_1402_: *mut leanh::LeanObject,
    mut v_inst_1403_: *mut leanh::LeanObject,
    mut v_inst_1404_: *mut leanh::LeanObject,
    mut v_x_1405_: *mut leanh::LeanObject,
    mut v___y_1406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ = l_Lean_ShareCommon_objectFactory___elam__5___redArg(
        v_inst_1403_,
        v_inst_1404_,
        v_x_1405_,
        v___y_1406_,
    );
    return v___x_1407_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(
    mut v_inst_1408_: *mut leanh::LeanObject,
    mut v_a_1409_: *mut leanh::LeanObject,
    mut v_b_1410_: *mut leanh::LeanObject,
    mut v_x_1411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1417_: u8 = 0;
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: u8 = 0;
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1411_) == 0 {
                    leanh::lean_dec(v_b_1410_);
                    leanh::lean_dec(v_a_1409_);
                    leanh::lean_dec_ref(v_inst_1408_);
                    return v_x_1411_;
                } else {
                    v_key_1412_ = leanh::lean_ctor_get(v_x_1411_, 0);
                    v_value_1413_ = leanh::lean_ctor_get(v_x_1411_, 1);
                    v_tail_1414_ = leanh::lean_ctor_get(v_x_1411_, 2);
                    v_isSharedCheck_1427_ = (!leanh::lean_is_exclusive(v_x_1411_)) as u8;
                    if v_isSharedCheck_1427_ == 0 {
                        v___x_1416_ = v_x_1411_;
                        v_isShared_1417_ = v_isSharedCheck_1427_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1414_);
                        leanh::lean_inc(v_value_1413_);
                        leanh::lean_inc(v_key_1412_);
                        leanh::lean_dec(v_x_1411_);
                        v___x_1416_ = leanh::lean_box(0);
                        v_isShared_1417_ = v_isSharedCheck_1427_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_1408_);
                leanh::lean_inc(v_a_1409_);
                leanh::lean_inc(v_key_1412_);
                v___x_1418_ = leanh::lean_apply_2(v_inst_1408_, v_key_1412_, v_a_1409_);
                v___x_1419_ = (leanh::lean_unbox(v___x_1418_) as u8);
                if v___x_1419_ == 0 {
                    v___x_1420_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_1408_, v_a_1409_, v_b_1410_, v_tail_1414_);
                    if v_isShared_1417_ == 0 {
                        leanh::lean_ctor_set(v___x_1416_, 2, v___x_1420_);
                        v___x_1422_ = v___x_1416_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1423_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_key_1412_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_value_1413_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 2, v___x_1420_);
                        v___x_1422_ = v_reuseFailAlloc_1423_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_1413_);
                    leanh::lean_dec(v_key_1412_);
                    leanh::lean_dec_ref(v_inst_1408_);
                    if v_isShared_1417_ == 0 {
                        leanh::lean_ctor_set(v___x_1416_, 1, v_b_1410_);
                        leanh::lean_ctor_set(v___x_1416_, 0, v_a_1409_);
                        v___x_1425_ = v___x_1416_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1426_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1409_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_b_1410_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_tail_1414_);
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
    mut v_inst_1428_: *mut leanh::LeanObject,
    mut v_inst_1429_: *mut leanh::LeanObject,
    mut v_m_1430_: *mut leanh::LeanObject,
    mut v_a_1431_: *mut leanh::LeanObject,
    mut v_b_1432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1437_: u8 = 0;
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: u8 = 0;
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u8 = 0;
    let mut v_val_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1433_ = leanh::lean_ctor_get(v_m_1430_, 0);
                v_buckets_1434_ = leanh::lean_ctor_get(v_m_1430_, 1);
                v_isSharedCheck_1479_ = (!leanh::lean_is_exclusive(v_m_1430_)) as u8;
                if v_isSharedCheck_1479_ == 0 {
                    v___x_1436_ = v_m_1430_;
                    v_isShared_1437_ = v_isSharedCheck_1479_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1434_);
                    leanh::lean_inc(v_size_1433_);
                    leanh::lean_dec(v_m_1430_);
                    v___x_1436_ = leanh::lean_box(0);
                    v_isShared_1437_ = v_isSharedCheck_1479_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1438_ = lean_array_get_size(v_buckets_1434_);
                leanh::lean_inc_ref(v_inst_1429_);
                leanh::lean_inc_n(v_a_1431_, 2);
                v___x_1439_ = leanh::lean_apply_1(v_inst_1429_, v_a_1431_);
                v___x_1440_ = 32u64;
                v___x_1441_ = leanh::lean_unbox_uint64(v___x_1439_);
                v___x_1442_ = lean_uint64_shift_right(v___x_1441_, v___x_1440_);
                v___x_1443_ = leanh::lean_unbox_uint64(v___x_1439_);
                leanh::lean_dec_ref(v___x_1439_);
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
                leanh::lean_inc(v_bkt_1453_);
                leanh::lean_inc_ref(v_inst_1428_);
                v___x_1454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_1428_, v_a_1431_, v_bkt_1453_);
                if v___x_1454_ == 0 {
                    leanh::lean_dec_ref(v_inst_1428_);
                    v___x_1455_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1456_ = lean_nat_add(v_size_1433_, v___x_1455_);
                    leanh::lean_dec(v_size_1433_);
                    leanh::lean_inc(v_bkt_1453_);
                    v___x_1457_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1457_, 0, v_a_1431_);
                    leanh::lean_ctor_set(v___x_1457_, 1, v_b_1432_);
                    leanh::lean_ctor_set(v___x_1457_, 2, v_bkt_1453_);
                    v_buckets_x27_1458_ =
                        lean_array_uset(v_buckets_1434_, v___x_1452_, v___x_1457_);
                    v___x_1459_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1460_ = lean_nat_mul(v_size_x27_1456_, v___x_1459_);
                    v___x_1461_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1462_ = lean_nat_div(v___x_1460_, v___x_1461_);
                    leanh::lean_dec(v___x_1460_);
                    v___x_1463_ = lean_array_get_size(v_buckets_x27_1458_);
                    v___x_1464_ = lean_nat_dec_le(v___x_1462_, v___x_1463_);
                    leanh::lean_dec(v___x_1462_);
                    if v___x_1464_ == 0 {
                        v_val_1465_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_1429_, v_buckets_x27_1458_);
                        if v_isShared_1437_ == 0 {
                            leanh::lean_ctor_set(v___x_1436_, 1, v_val_1465_);
                            leanh::lean_ctor_set(v___x_1436_, 0, v_size_x27_1456_);
                            v___x_1467_ = v___x_1436_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1468_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1468_,
                                0,
                                v_size_x27_1456_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_val_1465_);
                            v___x_1467_ = v_reuseFailAlloc_1468_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_inst_1429_);
                        if v_isShared_1437_ == 0 {
                            leanh::lean_ctor_set(v___x_1436_, 1, v_buckets_x27_1458_);
                            leanh::lean_ctor_set(v___x_1436_, 0, v_size_x27_1456_);
                            v___x_1470_ = v___x_1436_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1471_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1471_,
                                0,
                                v_size_x27_1456_,
                            );
                            leanh::lean_ctor_set(
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
                    leanh::lean_inc(v_bkt_1453_);
                    leanh::lean_dec_ref(v_inst_1429_);
                    v___x_1472_ = leanh::lean_box(0);
                    v_buckets_x27_1473_ =
                        lean_array_uset(v_buckets_1434_, v___x_1452_, v___x_1472_);
                    v___x_1474_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_1428_, v_a_1431_, v_b_1432_, v_bkt_1453_);
                    v___x_1475_ = lean_array_uset(v_buckets_x27_1473_, v___x_1452_, v___x_1474_);
                    if v_isShared_1437_ == 0 {
                        leanh::lean_ctor_set(v___x_1436_, 1, v___x_1475_);
                        v___x_1477_ = v___x_1436_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1478_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_size_1433_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 1, v___x_1475_);
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
    mut v_00_u03b1_1480_: *mut leanh::LeanObject,
    mut v_00_u03b2_1481_: *mut leanh::LeanObject,
    mut v_inst_1482_: *mut leanh::LeanObject,
    mut v_inst_1483_: *mut leanh::LeanObject,
    mut v_x_1484_: *mut leanh::LeanObject,
    mut v___y_1485_: *mut leanh::LeanObject,
    mut v___y_1486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1487_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_1482_, v_inst_1483_, v_x_1484_, v___y_1485_, v___y_1486_);
    return v___x_1487_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(
    mut v_inst_1488_: *mut leanh::LeanObject,
    mut v_a_1489_: *mut leanh::LeanObject,
    mut v_x_1490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: u8 = 0;
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1490_) == 0 {
                    leanh::lean_dec(v_a_1489_);
                    leanh::lean_dec_ref(v_inst_1488_);
                    v___x_1491_ = leanh::lean_box(0);
                    return v___x_1491_;
                } else {
                    v_key_1492_ = leanh::lean_ctor_get(v_x_1490_, 0);
                    leanh::lean_inc_n(v_key_1492_, 2);
                    v_tail_1493_ = leanh::lean_ctor_get(v_x_1490_, 2);
                    leanh::lean_inc(v_tail_1493_);
                    leanh::lean_dec_ref_known(v_x_1490_, 3);
                    leanh::lean_inc_ref(v_inst_1488_);
                    leanh::lean_inc(v_a_1489_);
                    v___x_1494_ = leanh::lean_apply_2(v_inst_1488_, v_key_1492_, v_a_1489_);
                    v___x_1495_ = (leanh::lean_unbox(v___x_1494_) as u8);
                    if v___x_1495_ == 0 {
                        leanh::lean_dec(v_key_1492_);
                        v_x_1490_ = v_tail_1493_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1493_);
                        leanh::lean_dec(v_a_1489_);
                        leanh::lean_dec_ref(v_inst_1488_);
                        v___x_1497_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1497_, 0, v_key_1492_);
                        return v___x_1497_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(
    mut v_inst_1498_: *mut leanh::LeanObject,
    mut v_inst_1499_: *mut leanh::LeanObject,
    mut v_m_1500_: *mut leanh::LeanObject,
    mut v_a_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1502_ = leanh::lean_ctor_get(v_m_1500_, 1);
    v___x_1503_ = lean_array_get_size(v_buckets_1502_);
    leanh::lean_inc(v_a_1501_);
    v___x_1504_ = leanh::lean_apply_1(v_inst_1499_, v_a_1501_);
    v___x_1505_ = 32u64;
    v___x_1506_ = leanh::lean_unbox_uint64(v___x_1504_);
    v___x_1507_ = lean_uint64_shift_right(v___x_1506_, v___x_1505_);
    v___x_1508_ = leanh::lean_unbox_uint64(v___x_1504_);
    leanh::lean_dec_ref(v___x_1504_);
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
    leanh::lean_inc(v___x_1518_);
    v___x_1519_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(v_inst_1498_, v_a_1501_, v___x_1518_);
    return v___x_1519_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg___boxed(
    mut v_inst_1520_: *mut leanh::LeanObject,
    mut v_inst_1521_: *mut leanh::LeanObject,
    mut v_m_1522_: *mut leanh::LeanObject,
    mut v_a_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_1520_, v_inst_1521_, v_m_1522_, v_a_1523_);
    leanh::lean_dec_ref(v_m_1522_);
    return v_res_1524_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__4(
    mut v_00_u03b1_1525_: *mut leanh::LeanObject,
    mut v_inst_1526_: *mut leanh::LeanObject,
    mut v_inst_1527_: *mut leanh::LeanObject,
    mut v_x_1528_: *mut leanh::LeanObject,
    mut v___y_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1530_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_1526_, v_inst_1527_, v_x_1528_, v___y_1529_);
    return v___x_1530_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__4___boxed(
    mut v_00_u03b1_1531_: *mut leanh::LeanObject,
    mut v_inst_1532_: *mut leanh::LeanObject,
    mut v_inst_1533_: *mut leanh::LeanObject,
    mut v_x_1534_: *mut leanh::LeanObject,
    mut v___y_1535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1536_ = l_Lean_ShareCommon_objectFactory___elam__4(
        v_00_u03b1_1531_,
        v_inst_1532_,
        v_inst_1533_,
        v_x_1534_,
        v___y_1535_,
    );
    leanh::lean_dec_ref(v_x_1534_);
    return v_res_1536_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(
    mut v_inst_1537_: *mut leanh::LeanObject,
    mut v_a_1538_: *mut leanh::LeanObject,
    mut v_x_1539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: u8 = 0;
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1539_) == 0 {
                    leanh::lean_dec(v_a_1538_);
                    leanh::lean_dec_ref(v_inst_1537_);
                    v___x_1540_ = leanh::lean_box(0);
                    return v___x_1540_;
                } else {
                    v_key_1541_ = leanh::lean_ctor_get(v_x_1539_, 0);
                    leanh::lean_inc(v_key_1541_);
                    v_value_1542_ = leanh::lean_ctor_get(v_x_1539_, 1);
                    leanh::lean_inc(v_value_1542_);
                    v_tail_1543_ = leanh::lean_ctor_get(v_x_1539_, 2);
                    leanh::lean_inc(v_tail_1543_);
                    leanh::lean_dec_ref_known(v_x_1539_, 3);
                    leanh::lean_inc_ref(v_inst_1537_);
                    leanh::lean_inc(v_a_1538_);
                    v___x_1544_ = leanh::lean_apply_2(v_inst_1537_, v_key_1541_, v_a_1538_);
                    v___x_1545_ = (leanh::lean_unbox(v___x_1544_) as u8);
                    if v___x_1545_ == 0 {
                        leanh::lean_dec(v_value_1542_);
                        v_x_1539_ = v_tail_1543_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1543_);
                        leanh::lean_dec(v_a_1538_);
                        leanh::lean_dec_ref(v_inst_1537_);
                        v___x_1547_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1547_, 0, v_value_1542_);
                        return v___x_1547_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(
    mut v_inst_1548_: *mut leanh::LeanObject,
    mut v_inst_1549_: *mut leanh::LeanObject,
    mut v_m_1550_: *mut leanh::LeanObject,
    mut v_a_1551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1552_ = leanh::lean_ctor_get(v_m_1550_, 1);
    v___x_1553_ = lean_array_get_size(v_buckets_1552_);
    leanh::lean_inc(v_a_1551_);
    v___x_1554_ = leanh::lean_apply_1(v_inst_1549_, v_a_1551_);
    v___x_1555_ = 32u64;
    v___x_1556_ = leanh::lean_unbox_uint64(v___x_1554_);
    v___x_1557_ = lean_uint64_shift_right(v___x_1556_, v___x_1555_);
    v___x_1558_ = leanh::lean_unbox_uint64(v___x_1554_);
    leanh::lean_dec_ref(v___x_1554_);
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
    leanh::lean_inc(v___x_1568_);
    v___x_1569_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(v_inst_1548_, v_a_1551_, v___x_1568_);
    return v___x_1569_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg___boxed(
    mut v_inst_1570_: *mut leanh::LeanObject,
    mut v_inst_1571_: *mut leanh::LeanObject,
    mut v_m_1572_: *mut leanh::LeanObject,
    mut v_a_1573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_1570_, v_inst_1571_, v_m_1572_, v_a_1573_);
    leanh::lean_dec_ref(v_m_1572_);
    return v_res_1574_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__1(
    mut v_00_u03b1_1575_: *mut leanh::LeanObject,
    mut v_00_u03b2_1576_: *mut leanh::LeanObject,
    mut v_inst_1577_: *mut leanh::LeanObject,
    mut v_inst_1578_: *mut leanh::LeanObject,
    mut v_x_1579_: *mut leanh::LeanObject,
    mut v___y_1580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_1577_, v_inst_1578_, v_x_1579_, v___y_1580_);
    return v___x_1581_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__1___boxed(
    mut v_00_u03b1_1582_: *mut leanh::LeanObject,
    mut v_00_u03b2_1583_: *mut leanh::LeanObject,
    mut v_inst_1584_: *mut leanh::LeanObject,
    mut v_inst_1585_: *mut leanh::LeanObject,
    mut v_x_1586_: *mut leanh::LeanObject,
    mut v___y_1587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1588_ = l_Lean_ShareCommon_objectFactory___elam__1(
        v_00_u03b1_1582_,
        v_00_u03b2_1583_,
        v_inst_1584_,
        v_inst_1585_,
        v_x_1586_,
        v___y_1587_,
    );
    leanh::lean_dec_ref(v_x_1586_);
    return v_res_1588_;
}
pub unsafe fn _init_l_Lean_ShareCommon_objectFactory___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1602_ = l_Lean_ShareCommon_objectFactory___closed__6;
    v___x_1603_ = l_ShareCommon_StateFactory_mkImpl(v___x_1602_);
    return v___x_1603_;
}
pub unsafe fn _init_l_Lean_ShareCommon_objectFactory() -> *mut leanh::LeanObject {
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1604_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_objectFactory___closed__7),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_objectFactory___closed__7_once),
        _init_l_Lean_ShareCommon_objectFactory___closed__7,
    );
    return v___x_1604_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__1___redArg(
    mut v_inst_1605_: *mut leanh::LeanObject,
    mut v_inst_1606_: *mut leanh::LeanObject,
    mut v_x_1607_: *mut leanh::LeanObject,
    mut v___y_1608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1609_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_1605_, v_inst_1606_, v_x_1607_, v___y_1608_);
    return v___x_1609_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__1___redArg___boxed(
    mut v_inst_1610_: *mut leanh::LeanObject,
    mut v_inst_1611_: *mut leanh::LeanObject,
    mut v_x_1612_: *mut leanh::LeanObject,
    mut v___y_1613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1614_ = l_Lean_ShareCommon_objectFactory___elam__1___redArg(
        v_inst_1610_,
        v_inst_1611_,
        v_x_1612_,
        v___y_1613_,
    );
    leanh::lean_dec_ref(v_x_1612_);
    return v_res_1614_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__2___redArg(
    mut v_inst_1615_: *mut leanh::LeanObject,
    mut v_inst_1616_: *mut leanh::LeanObject,
    mut v_x_1617_: *mut leanh::LeanObject,
    mut v___y_1618_: *mut leanh::LeanObject,
    mut v___y_1619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1620_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_1615_, v_inst_1616_, v_x_1617_, v___y_1618_, v___y_1619_);
    return v___x_1620_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__4___redArg(
    mut v_inst_1621_: *mut leanh::LeanObject,
    mut v_inst_1622_: *mut leanh::LeanObject,
    mut v_x_1623_: *mut leanh::LeanObject,
    mut v___y_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_1621_, v_inst_1622_, v_x_1623_, v___y_1624_);
    return v___x_1625_;
}
pub unsafe fn l_Lean_ShareCommon_objectFactory___elam__4___redArg___boxed(
    mut v_inst_1626_: *mut leanh::LeanObject,
    mut v_inst_1627_: *mut leanh::LeanObject,
    mut v_x_1628_: *mut leanh::LeanObject,
    mut v___y_1629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1630_ = l_Lean_ShareCommon_objectFactory___elam__4___redArg(
        v_inst_1626_,
        v_inst_1627_,
        v_x_1628_,
        v___y_1629_,
    );
    leanh::lean_dec_ref(v_x_1628_);
    return v_res_1630_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1(
    mut v_00_u03b1_1631_: *mut leanh::LeanObject,
    mut v_inst_1632_: *mut leanh::LeanObject,
    mut v_inst_1633_: *mut leanh::LeanObject,
    mut v_00_u03b2_1634_: *mut leanh::LeanObject,
    mut v_m_1635_: *mut leanh::LeanObject,
    mut v_a_1636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1637_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___redArg(v_inst_1632_, v_inst_1633_, v_m_1635_, v_a_1636_);
    return v___x_1637_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1___boxed(
    mut v_00_u03b1_1638_: *mut leanh::LeanObject,
    mut v_inst_1639_: *mut leanh::LeanObject,
    mut v_inst_1640_: *mut leanh::LeanObject,
    mut v_00_u03b2_1641_: *mut leanh::LeanObject,
    mut v_m_1642_: *mut leanh::LeanObject,
    mut v_a_1643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1644_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1(v_00_u03b1_1638_, v_inst_1639_, v_inst_1640_, v_00_u03b2_1641_, v_m_1642_, v_a_1643_);
    leanh::lean_dec_ref(v_m_1642_);
    return v_res_1644_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3(
    mut v_00_u03b1_1645_: *mut leanh::LeanObject,
    mut v_inst_1646_: *mut leanh::LeanObject,
    mut v_inst_1647_: *mut leanh::LeanObject,
    mut v_00_u03b2_1648_: *mut leanh::LeanObject,
    mut v_m_1649_: *mut leanh::LeanObject,
    mut v_a_1650_: *mut leanh::LeanObject,
    mut v_b_1651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1652_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3___redArg(v_inst_1646_, v_inst_1647_, v_m_1649_, v_a_1650_, v_b_1651_);
    return v___x_1652_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6(
    mut v_00_u03b1_1653_: *mut leanh::LeanObject,
    mut v_inst_1654_: *mut leanh::LeanObject,
    mut v_inst_1655_: *mut leanh::LeanObject,
    mut v_00_u03b2_1656_: *mut leanh::LeanObject,
    mut v_m_1657_: *mut leanh::LeanObject,
    mut v_a_1658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___redArg(v_inst_1654_, v_inst_1655_, v_m_1657_, v_a_1658_);
    return v___x_1659_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6___boxed(
    mut v_00_u03b1_1660_: *mut leanh::LeanObject,
    mut v_inst_1661_: *mut leanh::LeanObject,
    mut v_inst_1662_: *mut leanh::LeanObject,
    mut v_00_u03b2_1663_: *mut leanh::LeanObject,
    mut v_m_1664_: *mut leanh::LeanObject,
    mut v_a_1665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1666_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6(v_00_u03b1_1660_, v_inst_1661_, v_inst_1662_, v_00_u03b2_1663_, v_m_1664_, v_a_1665_);
    leanh::lean_dec_ref(v_m_1664_);
    return v_res_1666_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8(
    mut v_00_u03b1_1667_: *mut leanh::LeanObject,
    mut v_inst_1668_: *mut leanh::LeanObject,
    mut v_inst_1669_: *mut leanh::LeanObject,
    mut v_00_u03b2_1670_: *mut leanh::LeanObject,
    mut v_m_1671_: *mut leanh::LeanObject,
    mut v_a_1672_: *mut leanh::LeanObject,
    mut v_b_1673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ShareCommon_objectFactory___elam__5_spec__8___redArg(v_inst_1668_, v_inst_1669_, v_m_1671_, v_a_1672_, v_b_1673_);
    return v___x_1674_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3(
    mut v_00_u03b1_1675_: *mut leanh::LeanObject,
    mut v_inst_1676_: *mut leanh::LeanObject,
    mut v_00_u03b2_1677_: *mut leanh::LeanObject,
    mut v_a_1678_: *mut leanh::LeanObject,
    mut v_x_1679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ShareCommon_objectFactory___elam__1_spec__1_spec__3___redArg(v_inst_1676_, v_a_1678_, v_x_1679_);
    return v___x_1680_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(
    mut v_00_u03b1_1681_: *mut leanh::LeanObject,
    mut v_inst_1682_: *mut leanh::LeanObject,
    mut v_00_u03b2_1683_: *mut leanh::LeanObject,
    mut v_a_1684_: *mut leanh::LeanObject,
    mut v_x_1685_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1686_: u8 = 0;
    v___x_1686_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___redArg(v_inst_1682_, v_a_1684_, v_x_1685_);
    return v___x_1686_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6___boxed(
    mut v_00_u03b1_1687_: *mut leanh::LeanObject,
    mut v_inst_1688_: *mut leanh::LeanObject,
    mut v_00_u03b2_1689_: *mut leanh::LeanObject,
    mut v_a_1690_: *mut leanh::LeanObject,
    mut v_x_1691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1692_: u8 = 0;
    let mut v_r_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1692_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__6(v_00_u03b1_1687_, v_inst_1688_, v_00_u03b2_1689_, v_a_1690_, v_x_1691_);
    v_r_1693_ = leanh::lean_box((v_res_1692_) as usize);
    return v_r_1693_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7(
    mut v_00_u03b1_1694_: *mut leanh::LeanObject,
    mut v_inst_1695_: *mut leanh::LeanObject,
    mut v_00_u03b2_1696_: *mut leanh::LeanObject,
    mut v_data_1697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1698_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7___redArg(v_inst_1695_, v_data_1697_);
    return v___x_1698_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8(
    mut v_00_u03b1_1699_: *mut leanh::LeanObject,
    mut v_inst_1700_: *mut leanh::LeanObject,
    mut v_00_u03b2_1701_: *mut leanh::LeanObject,
    mut v_a_1702_: *mut leanh::LeanObject,
    mut v_b_1703_: *mut leanh::LeanObject,
    mut v_x_1704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__8___redArg(v_inst_1700_, v_a_1702_, v_b_1703_, v_x_1704_);
    return v___x_1705_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11(
    mut v_00_u03b1_1706_: *mut leanh::LeanObject,
    mut v_inst_1707_: *mut leanh::LeanObject,
    mut v_00_u03b2_1708_: *mut leanh::LeanObject,
    mut v_a_1709_: *mut leanh::LeanObject,
    mut v_x_1710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___at___00Std_DHashMap_Internal_Raw_u2080_getKey_x3f___at___00Lean_ShareCommon_objectFactory___elam__4_spec__6_spec__11___redArg(v_inst_1707_, v_a_1709_, v_x_1710_);
    return v___x_1711_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10(
    mut v_00_u03b1_1712_: *mut leanh::LeanObject,
    mut v_inst_1713_: *mut leanh::LeanObject,
    mut v_00_u03b2_1714_: *mut leanh::LeanObject,
    mut v_i_1715_: *mut leanh::LeanObject,
    mut v_source_1716_: *mut leanh::LeanObject,
    mut v_target_1717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1718_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10___redArg(v_inst_1713_, v_i_1715_, v_source_1716_, v_target_1717_);
    return v___x_1718_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13(
    mut v_00_u03b1_1719_: *mut leanh::LeanObject,
    mut v_00_u03b2_1720_: *mut leanh::LeanObject,
    mut v_inst_1721_: *mut leanh::LeanObject,
    mut v_x_1722_: *mut leanh::LeanObject,
    mut v_x_1723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1724_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ShareCommon_objectFactory___elam__2_spec__3_spec__7_spec__10_spec__13___redArg(v_inst_1721_, v_x_1722_, v_x_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(
    mut v_inst_1725_: *mut leanh::LeanObject,
    mut v_keys_1726_: *mut leanh::LeanObject,
    mut v_vals_1727_: *mut leanh::LeanObject,
    mut v_i_1728_: *mut leanh::LeanObject,
    mut v_k_1729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: u8 = 0;
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: u8 = 0;
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1730_ = lean_array_get_size(v_keys_1726_);
                v___x_1731_ = lean_nat_dec_lt(v_i_1728_, v___x_1730_);
                if v___x_1731_ == 0 {
                    leanh::lean_dec(v_k_1729_);
                    leanh::lean_dec(v_i_1728_);
                    leanh::lean_dec_ref(v_inst_1725_);
                    v___x_1732_ = leanh::lean_box(0);
                    return v___x_1732_;
                } else {
                    v_k_x27_1733_ = lean_array_fget_borrowed(v_keys_1726_, v_i_1728_);
                    leanh::lean_inc_ref(v_inst_1725_);
                    leanh::lean_inc(v_k_x27_1733_);
                    leanh::lean_inc(v_k_1729_);
                    v___x_1734_ =
                        leanh::lean_apply_2(v_inst_1725_, v_k_1729_, v_k_x27_1733_);
                    v___x_1735_ = (leanh::lean_unbox(v___x_1734_) as u8);
                    if v___x_1735_ == 0 {
                        v___x_1736_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1737_ = lean_nat_add(v_i_1728_, v___x_1736_);
                        leanh::lean_dec(v_i_1728_);
                        v_i_1728_ = v___x_1737_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_k_1729_);
                        leanh::lean_dec_ref(v_inst_1725_);
                        v___x_1739_ = lean_array_fget_borrowed(v_vals_1727_, v_i_1728_);
                        leanh::lean_dec(v_i_1728_);
                        leanh::lean_inc(v___x_1739_);
                        v___x_1740_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1740_, 0, v___x_1739_);
                        return v___x_1740_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg___boxed(
    mut v_inst_1741_: *mut leanh::LeanObject,
    mut v_keys_1742_: *mut leanh::LeanObject,
    mut v_vals_1743_: *mut leanh::LeanObject,
    mut v_i_1744_: *mut leanh::LeanObject,
    mut v_k_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1746_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_1741_, v_keys_1742_, v_vals_1743_, v_i_1744_, v_k_1745_);
    leanh::lean_dec_ref(v_vals_1743_);
    leanh::lean_dec_ref(v_keys_1742_);
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
    v___x_1751_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__0);
    v___x_1752_ = lean_usize_sub(v___x_1751_, v___x_1750_);
    return v___x_1752_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(
    mut v_inst_1753_: *mut leanh::LeanObject,
    mut v_x_1754_: *mut leanh::LeanObject,
    mut v_x_1755_: usize,
    mut v_x_1756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: usize = 0;
    let mut v___x_1760_: usize = 0;
    let mut v___x_1761_: usize = 0;
    let mut v_j_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: u8 = 0;
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: usize = 0;
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1754_) == 0 {
                    v_es_1757_ = leanh::lean_ctor_get(v_x_1754_, 0);
                    leanh::lean_inc_ref(v_es_1757_);
                    leanh::lean_dec_ref_known(v_x_1754_, 1);
                    v___x_1758_ = leanh::lean_box(2);
                    v___x_1759_ = 5usize;
                    v___x_1760_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1);
                    v___x_1761_ = lean_usize_land(v_x_1755_, v___x_1760_);
                    v_j_1762_ = lean_usize_to_nat(v___x_1761_);
                    v___x_1763_ = lean_array_get(v___x_1758_, v_es_1757_, v_j_1762_);
                    leanh::lean_dec(v_j_1762_);
                    leanh::lean_dec_ref(v_es_1757_);
                    match leanh::lean_obj_tag(v___x_1763_) {
                        0 => {
                            v_key_1764_ = leanh::lean_ctor_get(v___x_1763_, 0);
                            leanh::lean_inc(v_key_1764_);
                            v_val_1765_ = leanh::lean_ctor_get(v___x_1763_, 1);
                            leanh::lean_inc(v_val_1765_);
                            leanh::lean_dec_ref_known(v___x_1763_, 2);
                            v___x_1766_ =
                                leanh::lean_apply_2(v_inst_1753_, v_x_1756_, v_key_1764_);
                            v___x_1767_ = (leanh::lean_unbox(v___x_1766_) as u8);
                            if v___x_1767_ == 0 {
                                leanh::lean_dec(v_val_1765_);
                                v___x_1768_ = leanh::lean_box(0);
                                return v___x_1768_;
                            } else {
                                v___x_1769_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1769_, 0, v_val_1765_);
                                return v___x_1769_;
                            }
                        }
                        1 => {
                            v_node_1770_ = leanh::lean_ctor_get(v___x_1763_, 0);
                            leanh::lean_inc(v_node_1770_);
                            leanh::lean_dec_ref_known(v___x_1763_, 1);
                            v___x_1771_ = lean_usize_shift_right(v_x_1755_, v___x_1759_);
                            v_x_1754_ = v_node_1770_;
                            v_x_1755_ = v___x_1771_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec(v_x_1756_);
                            leanh::lean_dec_ref(v_inst_1753_);
                            v___x_1773_ = leanh::lean_box(0);
                            return v___x_1773_;
                        }
                    }
                } else {
                    v_ks_1774_ = leanh::lean_ctor_get(v_x_1754_, 0);
                    leanh::lean_inc_ref(v_ks_1774_);
                    v_vs_1775_ = leanh::lean_ctor_get(v_x_1754_, 1);
                    leanh::lean_inc_ref(v_vs_1775_);
                    leanh::lean_dec_ref_known(v_x_1754_, 2);
                    v___x_1776_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1777_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_1753_, v_ks_1774_, v_vs_1775_, v___x_1776_, v_x_1756_);
                    leanh::lean_dec_ref(v_vs_1775_);
                    leanh::lean_dec_ref(v_ks_1774_);
                    return v___x_1777_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___boxed(
    mut v_inst_1778_: *mut leanh::LeanObject,
    mut v_x_1779_: *mut leanh::LeanObject,
    mut v_x_1780_: *mut leanh::LeanObject,
    mut v_x_1781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_710__boxed_1782_: usize = 0;
    let mut v_res_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_710__boxed_1782_ = leanh::lean_unbox_usize(v_x_1780_);
    leanh::lean_dec(v_x_1780_);
    v_res_1783_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_1778_, v_x_1779_, v_x_710__boxed_1782_, v_x_1781_);
    return v_res_1783_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(
    mut v_inst_1784_: *mut leanh::LeanObject,
    mut v_inst_1785_: *mut leanh::LeanObject,
    mut v_x_1786_: *mut leanh::LeanObject,
    mut v_x_1787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u64 = 0;
    let mut v___x_1790_: usize = 0;
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_x_1787_);
    v___x_1788_ = leanh::lean_apply_1(v_inst_1785_, v_x_1787_);
    v___x_1789_ = leanh::lean_unbox_uint64(v___x_1788_);
    leanh::lean_dec_ref(v___x_1788_);
    v___x_1790_ = lean_uint64_to_usize(v___x_1789_);
    leanh::lean_inc_ref(v_x_1786_);
    v___x_1791_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_1784_, v_x_1786_, v___x_1790_, v_x_1787_);
    return v___x_1791_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg___boxed(
    mut v_inst_1792_: *mut leanh::LeanObject,
    mut v_inst_1793_: *mut leanh::LeanObject,
    mut v_x_1794_: *mut leanh::LeanObject,
    mut v_x_1795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1796_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_1792_, v_inst_1793_, v_x_1794_, v_x_1795_);
    leanh::lean_dec_ref(v_x_1794_);
    return v_res_1796_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__1(
    mut v_00_u03b1_1797_: *mut leanh::LeanObject,
    mut v_00_u03b2_1798_: *mut leanh::LeanObject,
    mut v_inst_1799_: *mut leanh::LeanObject,
    mut v_inst_1800_: *mut leanh::LeanObject,
    mut v_x_1801_: *mut leanh::LeanObject,
    mut v___y_1802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1803_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_1799_, v_inst_1800_, v_x_1801_, v___y_1802_);
    return v___x_1803_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__1___boxed(
    mut v_00_u03b1_1804_: *mut leanh::LeanObject,
    mut v_00_u03b2_1805_: *mut leanh::LeanObject,
    mut v_inst_1806_: *mut leanh::LeanObject,
    mut v_inst_1807_: *mut leanh::LeanObject,
    mut v_x_1808_: *mut leanh::LeanObject,
    mut v___y_1809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1810_ = l_Lean_ShareCommon_persistentObjectFactory___elam__1(
        v_00_u03b1_1804_,
        v_00_u03b2_1805_,
        v_inst_1806_,
        v_inst_1807_,
        v_x_1808_,
        v___y_1809_,
    );
    leanh::lean_dec_ref(v_x_1808_);
    return v_res_1810_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(
    mut v_inst_1811_: *mut leanh::LeanObject,
    mut v_keys_1812_: *mut leanh::LeanObject,
    mut v_vals_1813_: *mut leanh::LeanObject,
    mut v_i_1814_: *mut leanh::LeanObject,
    mut v_k_1815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: u8 = 0;
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: u8 = 0;
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1816_ = lean_array_get_size(v_keys_1812_);
                v___x_1817_ = lean_nat_dec_lt(v_i_1814_, v___x_1816_);
                if v___x_1817_ == 0 {
                    leanh::lean_dec(v_k_1815_);
                    leanh::lean_dec(v_i_1814_);
                    leanh::lean_dec_ref(v_inst_1811_);
                    v___x_1818_ = leanh::lean_box(0);
                    return v___x_1818_;
                } else {
                    v_k_x27_1819_ = lean_array_fget_borrowed(v_keys_1812_, v_i_1814_);
                    leanh::lean_inc_ref(v_inst_1811_);
                    leanh::lean_inc(v_k_x27_1819_);
                    leanh::lean_inc(v_k_1815_);
                    v___x_1820_ =
                        leanh::lean_apply_2(v_inst_1811_, v_k_1815_, v_k_x27_1819_);
                    v___x_1821_ = (leanh::lean_unbox(v___x_1820_) as u8);
                    if v___x_1821_ == 0 {
                        v___x_1822_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1823_ = lean_nat_add(v_i_1814_, v___x_1822_);
                        leanh::lean_dec(v_i_1814_);
                        v_i_1814_ = v___x_1823_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_k_1815_);
                        leanh::lean_dec_ref(v_inst_1811_);
                        v___x_1825_ = lean_array_fget_borrowed(v_vals_1813_, v_i_1814_);
                        leanh::lean_dec(v_i_1814_);
                        leanh::lean_inc(v___x_1825_);
                        leanh::lean_inc(v_k_x27_1819_);
                        v___x_1826_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1826_, 0, v_k_x27_1819_);
                        leanh::lean_ctor_set(v___x_1826_, 1, v___x_1825_);
                        v___x_1827_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1827_, 0, v___x_1826_);
                        return v___x_1827_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg___boxed(
    mut v_inst_1828_: *mut leanh::LeanObject,
    mut v_keys_1829_: *mut leanh::LeanObject,
    mut v_vals_1830_: *mut leanh::LeanObject,
    mut v_i_1831_: *mut leanh::LeanObject,
    mut v_k_1832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1833_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_1828_, v_keys_1829_, v_vals_1830_, v_i_1831_, v_k_1832_);
    leanh::lean_dec_ref(v_vals_1830_);
    leanh::lean_dec_ref(v_keys_1829_);
    return v_res_1833_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(
    mut v_inst_1834_: *mut leanh::LeanObject,
    mut v_x_1835_: *mut leanh::LeanObject,
    mut v_x_1836_: usize,
    mut v_x_1837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: usize = 0;
    let mut v___x_1841_: usize = 0;
    let mut v___x_1842_: usize = 0;
    let mut v_j_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: usize = 0;
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1835_) == 0 {
                    v_es_1838_ = leanh::lean_ctor_get(v_x_1835_, 0);
                    leanh::lean_inc_ref(v_es_1838_);
                    leanh::lean_dec_ref_known(v_x_1835_, 1);
                    v___x_1839_ = leanh::lean_box(2);
                    v___x_1840_ = 5usize;
                    v___x_1841_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1);
                    v___x_1842_ = lean_usize_land(v_x_1836_, v___x_1841_);
                    v_j_1843_ = lean_usize_to_nat(v___x_1842_);
                    v___x_1844_ = lean_array_get(v___x_1839_, v_es_1838_, v_j_1843_);
                    leanh::lean_dec(v_j_1843_);
                    leanh::lean_dec_ref(v_es_1838_);
                    match leanh::lean_obj_tag(v___x_1844_) {
                        0 => {
                            v_key_1845_ = leanh::lean_ctor_get(v___x_1844_, 0);
                            leanh::lean_inc_n(v_key_1845_, 2);
                            v_val_1846_ = leanh::lean_ctor_get(v___x_1844_, 1);
                            leanh::lean_inc(v_val_1846_);
                            leanh::lean_dec_ref_known(v___x_1844_, 2);
                            v___x_1847_ =
                                leanh::lean_apply_2(v_inst_1834_, v_x_1837_, v_key_1845_);
                            v___x_1848_ = (leanh::lean_unbox(v___x_1847_) as u8);
                            if v___x_1848_ == 0 {
                                leanh::lean_dec(v_val_1846_);
                                leanh::lean_dec(v_key_1845_);
                                v___x_1849_ = leanh::lean_box(0);
                                return v___x_1849_;
                            } else {
                                v___x_1850_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1850_, 0, v_key_1845_);
                                leanh::lean_ctor_set(v___x_1850_, 1, v_val_1846_);
                                v___x_1851_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1851_, 0, v___x_1850_);
                                return v___x_1851_;
                            }
                        }
                        1 => {
                            v_node_1852_ = leanh::lean_ctor_get(v___x_1844_, 0);
                            leanh::lean_inc(v_node_1852_);
                            leanh::lean_dec_ref_known(v___x_1844_, 1);
                            v___x_1853_ = lean_usize_shift_right(v_x_1836_, v___x_1840_);
                            v_x_1835_ = v_node_1852_;
                            v_x_1836_ = v___x_1853_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec(v_x_1837_);
                            leanh::lean_dec_ref(v_inst_1834_);
                            v___x_1855_ = leanh::lean_box(0);
                            return v___x_1855_;
                        }
                    }
                } else {
                    v_ks_1856_ = leanh::lean_ctor_get(v_x_1835_, 0);
                    leanh::lean_inc_ref(v_ks_1856_);
                    v_vs_1857_ = leanh::lean_ctor_get(v_x_1835_, 1);
                    leanh::lean_inc_ref(v_vs_1857_);
                    leanh::lean_dec_ref_known(v_x_1835_, 2);
                    v___x_1858_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1859_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_1834_, v_ks_1856_, v_vs_1857_, v___x_1858_, v_x_1837_);
                    leanh::lean_dec_ref(v_vs_1857_);
                    leanh::lean_dec_ref(v_ks_1856_);
                    return v___x_1859_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg___boxed(
    mut v_inst_1860_: *mut leanh::LeanObject,
    mut v_x_1861_: *mut leanh::LeanObject,
    mut v_x_1862_: *mut leanh::LeanObject,
    mut v_x_1863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_839__boxed_1864_: usize = 0;
    let mut v_res_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_839__boxed_1864_ = leanh::lean_unbox_usize(v_x_1862_);
    leanh::lean_dec(v_x_1862_);
    v_res_1865_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_1860_, v_x_1861_, v_x_839__boxed_1864_, v_x_1863_);
    return v_res_1865_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(
    mut v_inst_1866_: *mut leanh::LeanObject,
    mut v_inst_1867_: *mut leanh::LeanObject,
    mut v_x_1868_: *mut leanh::LeanObject,
    mut v_x_1869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: u64 = 0;
    let mut v___x_1872_: usize = 0;
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_x_1869_);
    v___x_1870_ = leanh::lean_apply_1(v_inst_1867_, v_x_1869_);
    v___x_1871_ = leanh::lean_unbox_uint64(v___x_1870_);
    leanh::lean_dec_ref(v___x_1870_);
    v___x_1872_ = lean_uint64_to_usize(v___x_1871_);
    leanh::lean_inc_ref(v_x_1868_);
    v___x_1873_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_1866_, v_x_1868_, v___x_1872_, v_x_1869_);
    return v___x_1873_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg___boxed(
    mut v_inst_1874_: *mut leanh::LeanObject,
    mut v_inst_1875_: *mut leanh::LeanObject,
    mut v_x_1876_: *mut leanh::LeanObject,
    mut v_x_1877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1878_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_1874_, v_inst_1875_, v_x_1876_, v_x_1877_);
    leanh::lean_dec_ref(v_x_1876_);
    return v_res_1878_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(
    mut v_inst_1879_: *mut leanh::LeanObject,
    mut v_inst_1880_: *mut leanh::LeanObject,
    mut v_x_1881_: *mut leanh::LeanObject,
    mut v___y_1882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1888_: u8 = 0;
    let mut v_fst_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1883_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_1879_, v_inst_1880_, v_x_1881_, v___y_1882_);
                if leanh::lean_obj_tag(v___x_1883_) == 0 {
                    v___x_1884_ = leanh::lean_box(0);
                    return v___x_1884_;
                } else {
                    v_val_1885_ = leanh::lean_ctor_get(v___x_1883_, 0);
                    v_isSharedCheck_1893_ = (!leanh::lean_is_exclusive(v___x_1883_)) as u8;
                    if v_isSharedCheck_1893_ == 0 {
                        v___x_1887_ = v___x_1883_;
                        v_isShared_1888_ = v_isSharedCheck_1893_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1885_);
                        leanh::lean_dec(v___x_1883_);
                        v___x_1887_ = leanh::lean_box(0);
                        v_isShared_1888_ = v_isSharedCheck_1893_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1889_ = leanh::lean_ctor_get(v_val_1885_, 0);
                leanh::lean_inc(v_fst_1889_);
                leanh::lean_dec(v_val_1885_);
                if v_isShared_1888_ == 0 {
                    leanh::lean_ctor_set(v___x_1887_, 0, v_fst_1889_);
                    v___x_1891_ = v___x_1887_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1892_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_fst_1889_);
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
    mut v_inst_1894_: *mut leanh::LeanObject,
    mut v_inst_1895_: *mut leanh::LeanObject,
    mut v_x_1896_: *mut leanh::LeanObject,
    mut v___y_1897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1898_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(
        v_inst_1894_,
        v_inst_1895_,
        v_x_1896_,
        v___y_1897_,
    );
    leanh::lean_dec_ref(v_x_1896_);
    return v_res_1898_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__4(
    mut v_00_u03b1_1899_: *mut leanh::LeanObject,
    mut v_inst_1900_: *mut leanh::LeanObject,
    mut v_inst_1901_: *mut leanh::LeanObject,
    mut v_x_1902_: *mut leanh::LeanObject,
    mut v___y_1903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1904_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4___redArg(
        v_inst_1900_,
        v_inst_1901_,
        v_x_1902_,
        v___y_1903_,
    );
    return v___x_1904_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__4___boxed(
    mut v_00_u03b1_1905_: *mut leanh::LeanObject,
    mut v_inst_1906_: *mut leanh::LeanObject,
    mut v_inst_1907_: *mut leanh::LeanObject,
    mut v_x_1908_: *mut leanh::LeanObject,
    mut v___y_1909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1910_ = l_Lean_ShareCommon_persistentObjectFactory___elam__4(
        v_00_u03b1_1905_,
        v_inst_1906_,
        v_inst_1907_,
        v_x_1908_,
        v___y_1909_,
    );
    leanh::lean_dec_ref(v_x_1908_);
    return v_res_1910_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1911_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1911_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1912_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__0);
    v___x_1913_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1913_, 0, v___x_1912_);
    return v___x_1913_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(
    mut v_00_u03b1_1914_: *mut leanh::LeanObject,
    mut v_inst_1915_: *mut leanh::LeanObject,
    mut v_inst_1916_: *mut leanh::LeanObject,
    mut v_00_u03b2_1917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1918_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___closed__1);
    return v___x_1918_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0___boxed(
    mut v_00_u03b1_1919_: *mut leanh::LeanObject,
    mut v_inst_1920_: *mut leanh::LeanObject,
    mut v_inst_1921_: *mut leanh::LeanObject,
    mut v_00_u03b2_1922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1923_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(v_00_u03b1_1919_, v_inst_1920_, v_inst_1921_, v_00_u03b2_1922_);
    leanh::lean_dec_ref(v_inst_1921_);
    leanh::lean_dec_ref(v_inst_1920_);
    return v_res_1923_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__0(
    mut v_00_u03b1_1924_: *mut leanh::LeanObject,
    mut v_00_u03b2_1925_: *mut leanh::LeanObject,
    mut v_inst_1926_: *mut leanh::LeanObject,
    mut v_inst_1927_: *mut leanh::LeanObject,
    mut v_x_1928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1929_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(leanh::lean_box(0), v_inst_1926_, v_inst_1927_, leanh::lean_box(0));
    return v___x_1929_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__0___boxed(
    mut v_00_u03b1_1930_: *mut leanh::LeanObject,
    mut v_00_u03b2_1931_: *mut leanh::LeanObject,
    mut v_inst_1932_: *mut leanh::LeanObject,
    mut v_inst_1933_: *mut leanh::LeanObject,
    mut v_x_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1935_ = l_Lean_ShareCommon_persistentObjectFactory___elam__0(
        v_00_u03b1_1930_,
        v_00_u03b2_1931_,
        v_inst_1932_,
        v_inst_1933_,
        v_x_1934_,
    );
    leanh::lean_dec(v_x_1934_);
    leanh::lean_dec_ref(v_inst_1933_);
    leanh::lean_dec_ref(v_inst_1932_);
    return v_res_1935_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__3(
    mut v_00_u03b1_1936_: *mut leanh::LeanObject,
    mut v_inst_1937_: *mut leanh::LeanObject,
    mut v_inst_1938_: *mut leanh::LeanObject,
    mut v_x_1939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1940_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(leanh::lean_box(0), v_inst_1937_, v_inst_1938_, leanh::lean_box(0));
    return v___x_1940_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__3___boxed(
    mut v_00_u03b1_1941_: *mut leanh::LeanObject,
    mut v_inst_1942_: *mut leanh::LeanObject,
    mut v_inst_1943_: *mut leanh::LeanObject,
    mut v_x_1944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1945_ = l_Lean_ShareCommon_persistentObjectFactory___elam__3(
        v_00_u03b1_1941_,
        v_inst_1942_,
        v_inst_1943_,
        v_x_1944_,
    );
    leanh::lean_dec(v_x_1944_);
    leanh::lean_dec_ref(v_inst_1943_);
    leanh::lean_dec_ref(v_inst_1942_);
    return v_res_1945_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(
    mut v_inst_1946_: *mut leanh::LeanObject,
    mut v_x_1947_: *mut leanh::LeanObject,
    mut v_x_1948_: *mut leanh::LeanObject,
    mut v_x_1949_: *mut leanh::LeanObject,
    mut v_x_1950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1955_: u8 = 0;
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1951_ = leanh::lean_ctor_get(v_x_1947_, 0);
                v_vs_1952_ = leanh::lean_ctor_get(v_x_1947_, 1);
                v_isSharedCheck_1977_ = (!leanh::lean_is_exclusive(v_x_1947_)) as u8;
                if v_isSharedCheck_1977_ == 0 {
                    v___x_1954_ = v_x_1947_;
                    v_isShared_1955_ = v_isSharedCheck_1977_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_1952_);
                    leanh::lean_inc(v_ks_1951_);
                    leanh::lean_dec(v_x_1947_);
                    v___x_1954_ = leanh::lean_box(0);
                    v_isShared_1955_ = v_isSharedCheck_1977_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1956_ = lean_array_get_size(v_ks_1951_);
                v___x_1957_ = lean_nat_dec_lt(v_x_1948_, v___x_1956_);
                if v___x_1957_ == 0 {
                    leanh::lean_dec(v_x_1948_);
                    leanh::lean_dec_ref(v_inst_1946_);
                    v___x_1958_ = lean_array_push(v_ks_1951_, v_x_1949_);
                    v___x_1959_ = lean_array_push(v_vs_1952_, v_x_1950_);
                    if v_isShared_1955_ == 0 {
                        leanh::lean_ctor_set(v___x_1954_, 1, v___x_1959_);
                        leanh::lean_ctor_set(v___x_1954_, 0, v___x_1958_);
                        v___x_1961_ = v___x_1954_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1962_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1958_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 1, v___x_1959_);
                        v___x_1961_ = v_reuseFailAlloc_1962_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1963_ = lean_array_fget_borrowed(v_ks_1951_, v_x_1948_);
                    leanh::lean_inc_ref(v_inst_1946_);
                    leanh::lean_inc(v_k_x27_1963_);
                    leanh::lean_inc(v_x_1949_);
                    v___x_1964_ =
                        leanh::lean_apply_2(v_inst_1946_, v_x_1949_, v_k_x27_1963_);
                    v___x_1965_ = (leanh::lean_unbox(v___x_1964_) as u8);
                    if v___x_1965_ == 0 {
                        if v_isShared_1955_ == 0 {
                            v___x_1967_ = v___x_1954_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1971_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_ks_1951_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_vs_1952_);
                            v___x_1967_ = v_reuseFailAlloc_1971_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_inst_1946_);
                        v___x_1972_ = lean_array_fset(v_ks_1951_, v_x_1948_, v_x_1949_);
                        v___x_1973_ = lean_array_fset(v_vs_1952_, v_x_1948_, v_x_1950_);
                        leanh::lean_dec(v_x_1948_);
                        if v_isShared_1955_ == 0 {
                            leanh::lean_ctor_set(v___x_1954_, 1, v___x_1973_);
                            leanh::lean_ctor_set(v___x_1954_, 0, v___x_1972_);
                            v___x_1975_ = v___x_1954_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1976_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1972_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___x_1973_);
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
                v___x_1968_ = leanh::lean_unsigned_to_nat(1);
                v___x_1969_ = lean_nat_add(v_x_1948_, v___x_1968_);
                leanh::lean_dec(v_x_1948_);
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
    mut v_inst_1978_: *mut leanh::LeanObject,
    mut v_n_1979_: *mut leanh::LeanObject,
    mut v_k_1980_: *mut leanh::LeanObject,
    mut v_v_1981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1982_ = leanh::lean_unsigned_to_nat(0);
    v___x_1983_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(v_inst_1978_, v_n_1979_, v___x_1982_, v_k_1980_, v_v_1981_);
    return v___x_1983_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1984_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1984_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(
    mut v_inst_1985_: *mut leanh::LeanObject,
    mut v_inst_1986_: *mut leanh::LeanObject,
    mut v_x_1987_: *mut leanh::LeanObject,
    mut v_x_1988_: usize,
    mut v_x_1989_: usize,
    mut v_x_1990_: *mut leanh::LeanObject,
    mut v_x_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: usize = 0;
    let mut v___x_1994_: usize = 0;
    let mut v___x_1995_: usize = 0;
    let mut v___x_1996_: usize = 0;
    let mut v_j_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2002_: u8 = 0;
    let mut v_v_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2016_: u8 = 0;
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut v_node_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2029_: usize = 0;
    let mut v___x_2030_: usize = 0;
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2035_: u8 = 0;
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2037_: u8 = 0;
    let mut v_unused_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2043_: u8 = 0;
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2048_: u8 = 0;
    let mut v_ks_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: usize = 0;
    let mut v___x_2055_: u8 = 0;
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: u8 = 0;
    let mut v_reuseFailAlloc_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1987_) == 0 {
                    v_es_1992_ = leanh::lean_ctor_get(v_x_1987_, 0);
                    v___x_1993_ = 5usize;
                    v___x_1994_ = 1usize;
                    v___x_1995_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg___closed__1);
                    v___x_1996_ = lean_usize_land(v_x_1988_, v___x_1995_);
                    v_j_1997_ = lean_usize_to_nat(v___x_1996_);
                    v___x_1998_ = lean_array_get_size(v_es_1992_);
                    v___x_1999_ = lean_nat_dec_lt(v_j_1997_, v___x_1998_);
                    if v___x_1999_ == 0 {
                        leanh::lean_dec(v_j_1997_);
                        leanh::lean_dec(v_x_1991_);
                        leanh::lean_dec(v_x_1990_);
                        leanh::lean_dec_ref(v_inst_1986_);
                        leanh::lean_dec_ref(v_inst_1985_);
                        return v_x_1987_;
                    } else {
                        leanh::lean_inc_ref(v_es_1992_);
                        v_isSharedCheck_2037_ = (!leanh::lean_is_exclusive(v_x_1987_)) as u8;
                        if v_isSharedCheck_2037_ == 0 {
                            v_unused_2038_ = leanh::lean_ctor_get(v_x_1987_, 0);
                            leanh::lean_dec(v_unused_2038_);
                            v___x_2001_ = v_x_1987_;
                            v_isShared_2002_ = v_isSharedCheck_2037_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_1987_);
                            v___x_2001_ = leanh::lean_box(0);
                            v_isShared_2002_ = v_isSharedCheck_2037_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2039_ = leanh::lean_ctor_get(v_x_1987_, 0);
                    v_vs_2040_ = leanh::lean_ctor_get(v_x_1987_, 1);
                    v_isSharedCheck_2060_ = (!leanh::lean_is_exclusive(v_x_1987_)) as u8;
                    if v_isSharedCheck_2060_ == 0 {
                        v___x_2042_ = v_x_1987_;
                        v_isShared_2043_ = v_isSharedCheck_2060_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2040_);
                        leanh::lean_inc(v_ks_2039_);
                        leanh::lean_dec(v_x_1987_);
                        v___x_2042_ = leanh::lean_box(0);
                        v_isShared_2043_ = v_isSharedCheck_2060_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2003_ = lean_array_fget(v_es_1992_, v_j_1997_);
                v___x_2004_ = leanh::lean_box(0);
                v_xs_x27_2005_ = lean_array_fset(v_es_1992_, v_j_1997_, v___x_2004_);
                match leanh::lean_obj_tag(v_v_2003_) {
                    0 => {
                        leanh::lean_dec_ref(v_inst_1986_);
                        v_key_2012_ = leanh::lean_ctor_get(v_v_2003_, 0);
                        v_val_2013_ = leanh::lean_ctor_get(v_v_2003_, 1);
                        v_isSharedCheck_2024_ = (!leanh::lean_is_exclusive(v_v_2003_)) as u8;
                        if v_isSharedCheck_2024_ == 0 {
                            v___x_2015_ = v_v_2003_;
                            v_isShared_2016_ = v_isSharedCheck_2024_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2013_);
                            leanh::lean_inc(v_key_2012_);
                            leanh::lean_dec(v_v_2003_);
                            v___x_2015_ = leanh::lean_box(0);
                            v_isShared_2016_ = v_isSharedCheck_2024_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2025_ = leanh::lean_ctor_get(v_v_2003_, 0);
                        v_isSharedCheck_2035_ = (!leanh::lean_is_exclusive(v_v_2003_)) as u8;
                        if v_isSharedCheck_2035_ == 0 {
                            v___x_2027_ = v_v_2003_;
                            v_isShared_2028_ = v_isSharedCheck_2035_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2025_);
                            leanh::lean_dec(v_v_2003_);
                            v___x_2027_ = leanh::lean_box(0);
                            v_isShared_2028_ = v_isSharedCheck_2035_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec_ref(v_inst_1986_);
                        leanh::lean_dec_ref(v_inst_1985_);
                        v___x_2036_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2036_, 0, v_x_1990_);
                        leanh::lean_ctor_set(v___x_2036_, 1, v_x_1991_);
                        v___y_2007_ = v___x_2036_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2008_ = lean_array_fset(v_xs_x27_2005_, v_j_1997_, v___y_2007_);
                leanh::lean_dec(v_j_1997_);
                if v_isShared_2002_ == 0 {
                    leanh::lean_ctor_set(v___x_2001_, 0, v___x_2008_);
                    v___x_2010_ = v___x_2001_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2011_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
                    v___x_2010_ = v_reuseFailAlloc_2011_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2010_;
            }
            4 => {
                leanh::lean_inc(v_key_2012_);
                leanh::lean_inc(v_x_1990_);
                v___x_2017_ = leanh::lean_apply_2(v_inst_1985_, v_x_1990_, v_key_2012_);
                v___x_2018_ = (leanh::lean_unbox(v___x_2017_) as u8);
                if v___x_2018_ == 0 {
                    leanh::lean_del_object(v___x_2015_);
                    v___x_2019_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2012_,
                        v_val_2013_,
                        v_x_1990_,
                        v_x_1991_,
                    );
                    v___x_2020_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2020_, 0, v___x_2019_);
                    v___y_2007_ = v___x_2020_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2013_);
                    leanh::lean_dec(v_key_2012_);
                    if v_isShared_2016_ == 0 {
                        leanh::lean_ctor_set(v___x_2015_, 1, v_x_1991_);
                        leanh::lean_ctor_set(v___x_2015_, 0, v_x_1990_);
                        v___x_2022_ = v___x_2015_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2023_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_x_1990_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_x_1991_);
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
                    leanh::lean_ctor_set(v___x_2027_, 0, v___x_2031_);
                    v___x_2033_ = v___x_2027_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2034_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
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
                    v_reuseFailAlloc_2059_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_ks_2039_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_vs_2040_);
                    v___x_2045_ = v_reuseFailAlloc_2059_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                leanh::lean_inc_ref(v_inst_1985_);
                v_newNode_2046_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(v_inst_1985_, v___x_2045_, v_x_1990_, v_x_1991_);
                v___x_2054_ = 7usize;
                v___x_2055_ = lean_usize_dec_le(v___x_2054_, v_x_1989_);
                if v___x_2055_ == 0 {
                    v___x_2056_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2046_);
                    v___x_2057_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2058_ = lean_nat_dec_lt(v___x_2056_, v___x_2057_);
                    leanh::lean_dec(v___x_2056_);
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
                    v_ks_2049_ = leanh::lean_ctor_get(v_newNode_2046_, 0);
                    leanh::lean_inc_ref(v_ks_2049_);
                    v_vs_2050_ = leanh::lean_ctor_get(v_newNode_2046_, 1);
                    leanh::lean_inc_ref(v_vs_2050_);
                    leanh::lean_dec_ref(v_newNode_2046_);
                    v___x_2051_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2052_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___closed__0);
                    v___x_2053_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_1985_, v_inst_1986_, v_x_1989_, v_ks_2049_, v_vs_2050_, v___x_2051_, v___x_2052_);
                    leanh::lean_dec_ref(v_vs_2050_);
                    leanh::lean_dec_ref(v_ks_2049_);
                    return v___x_2053_;
                } else {
                    leanh::lean_dec_ref(v_inst_1986_);
                    leanh::lean_dec_ref(v_inst_1985_);
                    return v_newNode_2046_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(
    mut v_inst_2061_: *mut leanh::LeanObject,
    mut v_inst_2062_: *mut leanh::LeanObject,
    mut v_depth_2063_: usize,
    mut v_keys_2064_: *mut leanh::LeanObject,
    mut v_vals_2065_: *mut leanh::LeanObject,
    mut v_i_2066_: *mut leanh::LeanObject,
    mut v_entries_2067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: u8 = 0;
    let mut v_k_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: u64 = 0;
    let mut v_h_2074_: usize = 0;
    let mut v___x_2075_: usize = 0;
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: usize = 0;
    let mut v___x_2078_: usize = 0;
    let mut v___x_2079_: usize = 0;
    let mut v_h_2080_: usize = 0;
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2068_ = lean_array_get_size(v_keys_2064_);
                v___x_2069_ = lean_nat_dec_lt(v_i_2066_, v___x_2068_);
                if v___x_2069_ == 0 {
                    leanh::lean_dec(v_i_2066_);
                    leanh::lean_dec_ref(v_inst_2062_);
                    leanh::lean_dec_ref(v_inst_2061_);
                    return v_entries_2067_;
                } else {
                    v_k_2070_ = lean_array_fget_borrowed(v_keys_2064_, v_i_2066_);
                    v_v_2071_ = lean_array_fget_borrowed(v_vals_2065_, v_i_2066_);
                    leanh::lean_inc_ref_n(v_inst_2062_, 2);
                    leanh::lean_inc_n(v_k_2070_, 2);
                    v___x_2072_ = leanh::lean_apply_1(v_inst_2062_, v_k_2070_);
                    v___x_2073_ = leanh::lean_unbox_uint64(v___x_2072_);
                    leanh::lean_dec_ref(v___x_2072_);
                    v_h_2074_ = lean_uint64_to_usize(v___x_2073_);
                    v___x_2075_ = 5usize;
                    v___x_2076_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2077_ = 1usize;
                    v___x_2078_ = lean_usize_sub(v_depth_2063_, v___x_2077_);
                    v___x_2079_ = lean_usize_mul(v___x_2075_, v___x_2078_);
                    v_h_2080_ = lean_usize_shift_right(v_h_2074_, v___x_2079_);
                    v___x_2081_ = lean_nat_add(v_i_2066_, v___x_2076_);
                    leanh::lean_dec(v_i_2066_);
                    leanh::lean_inc(v_v_2071_);
                    leanh::lean_inc_ref(v_inst_2061_);
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
    mut v_inst_2084_: *mut leanh::LeanObject,
    mut v_inst_2085_: *mut leanh::LeanObject,
    mut v_depth_2086_: *mut leanh::LeanObject,
    mut v_keys_2087_: *mut leanh::LeanObject,
    mut v_vals_2088_: *mut leanh::LeanObject,
    mut v_i_2089_: *mut leanh::LeanObject,
    mut v_entries_2090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2091_: usize = 0;
    let mut v_res_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2091_ = leanh::lean_unbox_usize(v_depth_2086_);
    leanh::lean_dec(v_depth_2086_);
    v_res_2092_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_2084_, v_inst_2085_, v_depth_boxed_2091_, v_keys_2087_, v_vals_2088_, v_i_2089_, v_entries_2090_);
    leanh::lean_dec_ref(v_vals_2088_);
    leanh::lean_dec_ref(v_keys_2087_);
    return v_res_2092_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg___boxed(
    mut v_inst_2093_: *mut leanh::LeanObject,
    mut v_inst_2094_: *mut leanh::LeanObject,
    mut v_x_2095_: *mut leanh::LeanObject,
    mut v_x_2096_: *mut leanh::LeanObject,
    mut v_x_2097_: *mut leanh::LeanObject,
    mut v_x_2098_: *mut leanh::LeanObject,
    mut v_x_2099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1109__boxed_2100_: usize = 0;
    let mut v_x_1110__boxed_2101_: usize = 0;
    let mut v_res_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1109__boxed_2100_ = leanh::lean_unbox_usize(v_x_2096_);
    leanh::lean_dec(v_x_2096_);
    v_x_1110__boxed_2101_ = leanh::lean_unbox_usize(v_x_2097_);
    leanh::lean_dec(v_x_2097_);
    v_res_2102_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_2093_, v_inst_2094_, v_x_2095_, v_x_1109__boxed_2100_, v_x_1110__boxed_2101_, v_x_2098_, v_x_2099_);
    return v_res_2102_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(
    mut v_inst_2103_: *mut leanh::LeanObject,
    mut v_inst_2104_: *mut leanh::LeanObject,
    mut v_x_2105_: *mut leanh::LeanObject,
    mut v_x_2106_: *mut leanh::LeanObject,
    mut v_x_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: u64 = 0;
    let mut v___x_2110_: usize = 0;
    let mut v___x_2111_: usize = 0;
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_2104_);
    leanh::lean_inc(v_x_2106_);
    v___x_2108_ = leanh::lean_apply_1(v_inst_2104_, v_x_2106_);
    v___x_2109_ = leanh::lean_unbox_uint64(v___x_2108_);
    leanh::lean_dec_ref(v___x_2108_);
    v___x_2110_ = lean_uint64_to_usize(v___x_2109_);
    v___x_2111_ = 1usize;
    v___x_2112_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_2103_, v_inst_2104_, v_x_2105_, v___x_2110_, v___x_2111_, v_x_2106_, v_x_2107_);
    return v___x_2112_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__2(
    mut v_00_u03b1_2113_: *mut leanh::LeanObject,
    mut v_00_u03b2_2114_: *mut leanh::LeanObject,
    mut v_inst_2115_: *mut leanh::LeanObject,
    mut v_inst_2116_: *mut leanh::LeanObject,
    mut v_x_2117_: *mut leanh::LeanObject,
    mut v___y_2118_: *mut leanh::LeanObject,
    mut v___y_2119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2120_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_2115_, v_inst_2116_, v_x_2117_, v___y_2118_, v___y_2119_);
    return v___x_2120_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(
    mut v_inst_2121_: *mut leanh::LeanObject,
    mut v_inst_2122_: *mut leanh::LeanObject,
    mut v_x_2123_: *mut leanh::LeanObject,
    mut v___y_2124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2125_ = leanh::lean_box(0);
    v___x_2126_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_2121_, v_inst_2122_, v_x_2123_, v___y_2124_, v___x_2125_);
    return v___x_2126_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__5(
    mut v_00_u03b1_2127_: *mut leanh::LeanObject,
    mut v_inst_2128_: *mut leanh::LeanObject,
    mut v_inst_2129_: *mut leanh::LeanObject,
    mut v_x_2130_: *mut leanh::LeanObject,
    mut v___y_2131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2132_ = l_Lean_ShareCommon_persistentObjectFactory___elam__5___redArg(
        v_inst_2128_,
        v_inst_2129_,
        v_x_2130_,
        v___y_2131_,
    );
    return v___x_2132_;
}
pub unsafe fn _init_l_Lean_ShareCommon_persistentObjectFactory___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ = l_Lean_ShareCommon_persistentObjectFactory___closed__6;
    v___x_2147_ = l_ShareCommon_StateFactory_mkImpl(v___x_2146_);
    return v___x_2147_;
}
pub unsafe fn _init_l_Lean_ShareCommon_persistentObjectFactory() -> *mut leanh::LeanObject {
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2148_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_persistentObjectFactory___closed__7),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_persistentObjectFactory___closed__7_once),
        _init_l_Lean_ShareCommon_persistentObjectFactory___closed__7,
    );
    return v___x_2148_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(
    mut v_inst_2149_: *mut leanh::LeanObject,
    mut v_inst_2150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2151_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(leanh::lean_box(0), v_inst_2149_, v_inst_2150_, leanh::lean_box(0));
    return v___x_2151_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg___boxed(
    mut v_inst_2152_: *mut leanh::LeanObject,
    mut v_inst_2153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2154_ =
        l_Lean_ShareCommon_persistentObjectFactory___elam__0___redArg(v_inst_2152_, v_inst_2153_);
    leanh::lean_dec_ref(v_inst_2153_);
    leanh::lean_dec_ref(v_inst_2152_);
    return v_res_2154_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg(
    mut v_inst_2155_: *mut leanh::LeanObject,
    mut v_inst_2156_: *mut leanh::LeanObject,
    mut v_x_2157_: *mut leanh::LeanObject,
    mut v___y_2158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_2155_, v_inst_2156_, v_x_2157_, v___y_2158_);
    return v___x_2159_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg___boxed(
    mut v_inst_2160_: *mut leanh::LeanObject,
    mut v_inst_2161_: *mut leanh::LeanObject,
    mut v_x_2162_: *mut leanh::LeanObject,
    mut v___y_2163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2164_ = l_Lean_ShareCommon_persistentObjectFactory___elam__1___redArg(
        v_inst_2160_,
        v_inst_2161_,
        v_x_2162_,
        v___y_2163_,
    );
    leanh::lean_dec_ref(v_x_2162_);
    return v_res_2164_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__2___redArg(
    mut v_inst_2165_: *mut leanh::LeanObject,
    mut v_inst_2166_: *mut leanh::LeanObject,
    mut v_x_2167_: *mut leanh::LeanObject,
    mut v___y_2168_: *mut leanh::LeanObject,
    mut v___y_2169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2170_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_2165_, v_inst_2166_, v_x_2167_, v___y_2168_, v___y_2169_);
    return v___x_2170_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(
    mut v_inst_2171_: *mut leanh::LeanObject,
    mut v_inst_2172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2173_ = l_Lean_PersistentHashMap_empty___at___00Lean_ShareCommon_persistentObjectFactory___elam__0_spec__0(leanh::lean_box(0), v_inst_2171_, v_inst_2172_, leanh::lean_box(0));
    return v___x_2173_;
}
pub unsafe fn l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg___boxed(
    mut v_inst_2174_: *mut leanh::LeanObject,
    mut v_inst_2175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2176_ =
        l_Lean_ShareCommon_persistentObjectFactory___elam__3___redArg(v_inst_2174_, v_inst_2175_);
    leanh::lean_dec_ref(v_inst_2175_);
    leanh::lean_dec_ref(v_inst_2174_);
    return v_res_2176_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(
    mut v_00_u03b1_2177_: *mut leanh::LeanObject,
    mut v_inst_2178_: *mut leanh::LeanObject,
    mut v_inst_2179_: *mut leanh::LeanObject,
    mut v_00_u03b2_2180_: *mut leanh::LeanObject,
    mut v_x_2181_: *mut leanh::LeanObject,
    mut v_x_2182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2183_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___redArg(v_inst_2178_, v_inst_2179_, v_x_2181_, v_x_2182_);
    return v___x_2183_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2___boxed(
    mut v_00_u03b1_2184_: *mut leanh::LeanObject,
    mut v_inst_2185_: *mut leanh::LeanObject,
    mut v_inst_2186_: *mut leanh::LeanObject,
    mut v_00_u03b2_2187_: *mut leanh::LeanObject,
    mut v_x_2188_: *mut leanh::LeanObject,
    mut v_x_2189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2190_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2(v_00_u03b1_2184_, v_inst_2185_, v_inst_2186_, v_00_u03b2_2187_, v_x_2188_, v_x_2189_);
    leanh::lean_dec_ref(v_x_2188_);
    return v_res_2190_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4(
    mut v_00_u03b1_2191_: *mut leanh::LeanObject,
    mut v_inst_2192_: *mut leanh::LeanObject,
    mut v_inst_2193_: *mut leanh::LeanObject,
    mut v_00_u03b2_2194_: *mut leanh::LeanObject,
    mut v_x_2195_: *mut leanh::LeanObject,
    mut v_x_2196_: *mut leanh::LeanObject,
    mut v_x_2197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2198_ = l_Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4___redArg(v_inst_2192_, v_inst_2193_, v_x_2195_, v_x_2196_, v_x_2197_);
    return v___x_2198_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(
    mut v_00_u03b1_2199_: *mut leanh::LeanObject,
    mut v_inst_2200_: *mut leanh::LeanObject,
    mut v_inst_2201_: *mut leanh::LeanObject,
    mut v_00_u03b2_2202_: *mut leanh::LeanObject,
    mut v_x_2203_: *mut leanh::LeanObject,
    mut v_x_2204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2205_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___redArg(v_inst_2200_, v_inst_2201_, v_x_2203_, v_x_2204_);
    return v___x_2205_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7___boxed(
    mut v_00_u03b1_2206_: *mut leanh::LeanObject,
    mut v_inst_2207_: *mut leanh::LeanObject,
    mut v_inst_2208_: *mut leanh::LeanObject,
    mut v_00_u03b2_2209_: *mut leanh::LeanObject,
    mut v_x_2210_: *mut leanh::LeanObject,
    mut v_x_2211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2212_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7(v_00_u03b1_2206_, v_inst_2207_, v_inst_2208_, v_00_u03b2_2209_, v_x_2210_, v_x_2211_);
    leanh::lean_dec_ref(v_x_2210_);
    return v_res_2212_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(
    mut v_00_u03b1_2213_: *mut leanh::LeanObject,
    mut v_inst_2214_: *mut leanh::LeanObject,
    mut v_00_u03b2_2215_: *mut leanh::LeanObject,
    mut v_x_2216_: *mut leanh::LeanObject,
    mut v_x_2217_: usize,
    mut v_x_2218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_x_2216_);
    v___x_2219_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___redArg(v_inst_2214_, v_x_2216_, v_x_2217_, v_x_2218_);
    return v___x_2219_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3___boxed(
    mut v_00_u03b1_2220_: *mut leanh::LeanObject,
    mut v_inst_2221_: *mut leanh::LeanObject,
    mut v_00_u03b2_2222_: *mut leanh::LeanObject,
    mut v_x_2223_: *mut leanh::LeanObject,
    mut v_x_2224_: *mut leanh::LeanObject,
    mut v_x_2225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1476__boxed_2226_: usize = 0;
    let mut v_res_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1476__boxed_2226_ = leanh::lean_unbox_usize(v_x_2224_);
    leanh::lean_dec(v_x_2224_);
    v_res_2227_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3(v_00_u03b1_2220_, v_inst_2221_, v_00_u03b2_2222_, v_x_2223_, v_x_1476__boxed_2226_, v_x_2225_);
    leanh::lean_dec_ref(v_x_2223_);
    return v_res_2227_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(
    mut v_00_u03b1_2228_: *mut leanh::LeanObject,
    mut v_inst_2229_: *mut leanh::LeanObject,
    mut v_inst_2230_: *mut leanh::LeanObject,
    mut v_00_u03b2_2231_: *mut leanh::LeanObject,
    mut v_x_2232_: *mut leanh::LeanObject,
    mut v_x_2233_: usize,
    mut v_x_2234_: usize,
    mut v_x_2235_: *mut leanh::LeanObject,
    mut v_x_2236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2237_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___redArg(v_inst_2229_, v_inst_2230_, v_x_2232_, v_x_2233_, v_x_2234_, v_x_2235_, v_x_2236_);
    return v___x_2237_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_2238_: *mut leanh::LeanObject,
    mut v_inst_2239_: *mut leanh::LeanObject,
    mut v_inst_2240_: *mut leanh::LeanObject,
    mut v_00_u03b2_2241_: *mut leanh::LeanObject,
    mut v_x_2242_: *mut leanh::LeanObject,
    mut v_x_2243_: *mut leanh::LeanObject,
    mut v_x_2244_: *mut leanh::LeanObject,
    mut v_x_2245_: *mut leanh::LeanObject,
    mut v_x_2246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1494__boxed_2247_: usize = 0;
    let mut v_x_1495__boxed_2248_: usize = 0;
    let mut v_res_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1494__boxed_2247_ = leanh::lean_unbox_usize(v_x_2243_);
    leanh::lean_dec(v_x_2243_);
    v_x_1495__boxed_2248_ = leanh::lean_unbox_usize(v_x_2244_);
    leanh::lean_dec(v_x_2244_);
    v_res_2249_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6(v_00_u03b1_2238_, v_inst_2239_, v_inst_2240_, v_00_u03b2_2241_, v_x_2242_, v_x_1494__boxed_2247_, v_x_1495__boxed_2248_, v_x_2245_, v_x_2246_);
    return v_res_2249_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(
    mut v_00_u03b1_2250_: *mut leanh::LeanObject,
    mut v_inst_2251_: *mut leanh::LeanObject,
    mut v_00_u03b2_2252_: *mut leanh::LeanObject,
    mut v_x_2253_: *mut leanh::LeanObject,
    mut v_x_2254_: usize,
    mut v_x_2255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_x_2253_);
    v___x_2256_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___redArg(v_inst_2251_, v_x_2253_, v_x_2254_, v_x_2255_);
    return v___x_2256_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10___boxed(
    mut v_00_u03b1_2257_: *mut leanh::LeanObject,
    mut v_inst_2258_: *mut leanh::LeanObject,
    mut v_00_u03b2_2259_: *mut leanh::LeanObject,
    mut v_x_2260_: *mut leanh::LeanObject,
    mut v_x_2261_: *mut leanh::LeanObject,
    mut v_x_2262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1519__boxed_2263_: usize = 0;
    let mut v_res_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1519__boxed_2263_ = leanh::lean_unbox_usize(v_x_2261_);
    leanh::lean_dec(v_x_2261_);
    v_res_2264_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10(v_00_u03b1_2257_, v_inst_2258_, v_00_u03b2_2259_, v_x_2260_, v_x_1519__boxed_2263_, v_x_2262_);
    leanh::lean_dec_ref(v_x_2260_);
    return v_res_2264_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(
    mut v_00_u03b1_2265_: *mut leanh::LeanObject,
    mut v_inst_2266_: *mut leanh::LeanObject,
    mut v_00_u03b2_2267_: *mut leanh::LeanObject,
    mut v_keys_2268_: *mut leanh::LeanObject,
    mut v_vals_2269_: *mut leanh::LeanObject,
    mut v_heq_2270_: *mut leanh::LeanObject,
    mut v_i_2271_: *mut leanh::LeanObject,
    mut v_k_2272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2273_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___redArg(v_inst_2266_, v_keys_2268_, v_vals_2269_, v_i_2271_, v_k_2272_);
    return v___x_2273_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8___boxed(
    mut v_00_u03b1_2274_: *mut leanh::LeanObject,
    mut v_inst_2275_: *mut leanh::LeanObject,
    mut v_00_u03b2_2276_: *mut leanh::LeanObject,
    mut v_keys_2277_: *mut leanh::LeanObject,
    mut v_vals_2278_: *mut leanh::LeanObject,
    mut v_heq_2279_: *mut leanh::LeanObject,
    mut v_i_2280_: *mut leanh::LeanObject,
    mut v_k_2281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2282_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__1_spec__2_spec__3_spec__8(v_00_u03b1_2274_, v_inst_2275_, v_00_u03b2_2276_, v_keys_2277_, v_vals_2278_, v_heq_2279_, v_i_2280_, v_k_2281_);
    leanh::lean_dec_ref(v_vals_2278_);
    leanh::lean_dec_ref(v_keys_2277_);
    return v_res_2282_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11(
    mut v_00_u03b1_2283_: *mut leanh::LeanObject,
    mut v_inst_2284_: *mut leanh::LeanObject,
    mut v_00_u03b2_2285_: *mut leanh::LeanObject,
    mut v_n_2286_: *mut leanh::LeanObject,
    mut v_k_2287_: *mut leanh::LeanObject,
    mut v_v_2288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2289_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11___redArg(v_inst_2284_, v_n_2286_, v_k_2287_, v_v_2288_);
    return v___x_2289_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(
    mut v_00_u03b1_2290_: *mut leanh::LeanObject,
    mut v_inst_2291_: *mut leanh::LeanObject,
    mut v_inst_2292_: *mut leanh::LeanObject,
    mut v_00_u03b2_2293_: *mut leanh::LeanObject,
    mut v_depth_2294_: usize,
    mut v_keys_2295_: *mut leanh::LeanObject,
    mut v_vals_2296_: *mut leanh::LeanObject,
    mut v_heq_2297_: *mut leanh::LeanObject,
    mut v_i_2298_: *mut leanh::LeanObject,
    mut v_entries_2299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2300_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___redArg(v_inst_2291_, v_inst_2292_, v_depth_2294_, v_keys_2295_, v_vals_2296_, v_i_2298_, v_entries_2299_);
    return v___x_2300_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12___boxed(
    mut v_00_u03b1_2301_: *mut leanh::LeanObject,
    mut v_inst_2302_: *mut leanh::LeanObject,
    mut v_inst_2303_: *mut leanh::LeanObject,
    mut v_00_u03b2_2304_: *mut leanh::LeanObject,
    mut v_depth_2305_: *mut leanh::LeanObject,
    mut v_keys_2306_: *mut leanh::LeanObject,
    mut v_vals_2307_: *mut leanh::LeanObject,
    mut v_heq_2308_: *mut leanh::LeanObject,
    mut v_i_2309_: *mut leanh::LeanObject,
    mut v_entries_2310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2311_: usize = 0;
    let mut v_res_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2311_ = leanh::lean_unbox_usize(v_depth_2305_);
    leanh::lean_dec(v_depth_2305_);
    v_res_2312_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__12(v_00_u03b1_2301_, v_inst_2302_, v_inst_2303_, v_00_u03b2_2304_, v_depth_boxed_2311_, v_keys_2306_, v_vals_2307_, v_heq_2308_, v_i_2309_, v_entries_2310_);
    leanh::lean_dec_ref(v_vals_2307_);
    leanh::lean_dec_ref(v_keys_2306_);
    return v_res_2312_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(
    mut v_00_u03b1_2313_: *mut leanh::LeanObject,
    mut v_inst_2314_: *mut leanh::LeanObject,
    mut v_00_u03b2_2315_: *mut leanh::LeanObject,
    mut v_keys_2316_: *mut leanh::LeanObject,
    mut v_vals_2317_: *mut leanh::LeanObject,
    mut v_heq_2318_: *mut leanh::LeanObject,
    mut v_i_2319_: *mut leanh::LeanObject,
    mut v_k_2320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2321_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___redArg(v_inst_2314_, v_keys_2316_, v_vals_2317_, v_i_2319_, v_k_2320_);
    return v___x_2321_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15___boxed(
    mut v_00_u03b1_2322_: *mut leanh::LeanObject,
    mut v_inst_2323_: *mut leanh::LeanObject,
    mut v_00_u03b2_2324_: *mut leanh::LeanObject,
    mut v_keys_2325_: *mut leanh::LeanObject,
    mut v_vals_2326_: *mut leanh::LeanObject,
    mut v_heq_2327_: *mut leanh::LeanObject,
    mut v_i_2328_: *mut leanh::LeanObject,
    mut v_k_2329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2330_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_ShareCommon_persistentObjectFactory___elam__4_spec__7_spec__10_spec__15(v_00_u03b1_2322_, v_inst_2323_, v_00_u03b2_2324_, v_keys_2325_, v_vals_2326_, v_heq_2327_, v_i_2328_, v_k_2329_);
    leanh::lean_dec_ref(v_vals_2326_);
    leanh::lean_dec_ref(v_keys_2325_);
    return v_res_2330_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13(
    mut v_00_u03b1_2331_: *mut leanh::LeanObject,
    mut v_inst_2332_: *mut leanh::LeanObject,
    mut v_00_u03b2_2333_: *mut leanh::LeanObject,
    mut v_x_2334_: *mut leanh::LeanObject,
    mut v_x_2335_: *mut leanh::LeanObject,
    mut v_x_2336_: *mut leanh::LeanObject,
    mut v_x_2337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2338_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ShareCommon_persistentObjectFactory___elam__2_spec__4_spec__6_spec__11_spec__13___redArg(v_inst_2332_, v_x_2334_, v_x_2335_, v_x_2336_, v_x_2337_);
    return v___x_2338_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(
    mut v_inst_2339_: *mut leanh::LeanObject,
    mut v_a_2340_: *mut leanh::LeanObject,
    mut v_a_2341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2342_ = leanh::lean_ctor_get(v_inst_2339_, 0);
    leanh::lean_inc_ref(v_toApplicative_2342_);
    leanh::lean_dec_ref(v_inst_2339_);
    v_toPure_2343_ = leanh::lean_ctor_get(v_toApplicative_2342_, 1);
    leanh::lean_inc(v_toPure_2343_);
    leanh::lean_dec_ref(v_toApplicative_2342_);
    v___x_2344_ = l_Lean_ShareCommon_objectFactory;
    v___x_2345_ = lean_state_sharecommon(v___x_2344_, v_a_2341_, v_a_2340_);
    v___x_2346_ =
        leanh::lean_apply_2(v_toPure_2343_, leanh::lean_box(0), v___x_2345_);
    return v___x_2346_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_withShareCommon(
    mut v_m_2347_: *mut leanh::LeanObject,
    mut v_00_u03b1_2348_: *mut leanh::LeanObject,
    mut v_inst_2349_: *mut leanh::LeanObject,
    mut v_a_2350_: *mut leanh::LeanObject,
    mut v_a_2351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2352_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(
        v_inst_2349_,
        v_a_2350_,
        v_a_2351_,
    );
    return v___x_2352_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(
    mut v_inst_2353_: *mut leanh::LeanObject,
    mut v_a_2354_: *mut leanh::LeanObject,
    mut v_a_2355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2356_ = leanh::lean_ctor_get(v_inst_2353_, 0);
    leanh::lean_inc_ref(v_toApplicative_2356_);
    leanh::lean_dec_ref(v_inst_2353_);
    v_toPure_2357_ = leanh::lean_ctor_get(v_toApplicative_2356_, 1);
    leanh::lean_inc(v_toPure_2357_);
    leanh::lean_dec_ref(v_toApplicative_2356_);
    v___x_2358_ = l_Lean_ShareCommon_persistentObjectFactory;
    v___x_2359_ = lean_state_sharecommon(v___x_2358_, v_a_2355_, v_a_2354_);
    v___x_2360_ =
        leanh::lean_apply_2(v_toPure_2357_, leanh::lean_box(0), v___x_2359_);
    return v___x_2360_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonT_withShareCommon(
    mut v_m_2361_: *mut leanh::LeanObject,
    mut v_00_u03b1_2362_: *mut leanh::LeanObject,
    mut v_inst_2363_: *mut leanh::LeanObject,
    mut v_a_2364_: *mut leanh::LeanObject,
    mut v_a_2365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2366_ = l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(
        v_inst_2363_,
        v_a_2364_,
        v_a_2365_,
    );
    return v___x_2366_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0(
    mut v_inst_2367_: *mut leanh::LeanObject,
    mut v_00_u03b1_2368_: *mut leanh::LeanObject,
    mut v___y_2369_: *mut leanh::LeanObject,
    mut v___y_2370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2371_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___redArg(
        v_inst_2367_,
        v___y_2369_,
        v___y_2370_,
    );
    return v___x_2371_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg(
    mut v_inst_2372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2373_ = leanh::lean_alloc_closure(
        l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2373_, 0, v_inst_2372_);
    return v___f_2373_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_monadShareCommon(
    mut v_m_2374_: *mut leanh::LeanObject,
    mut v_inst_2375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2376_ = leanh::lean_alloc_closure(
        l_Lean_ShareCommon_ShareCommonT_monadShareCommon___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2376_, 0, v_inst_2375_);
    return v___f_2376_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0(
    mut v_inst_2377_: *mut leanh::LeanObject,
    mut v_00_u03b1_2378_: *mut leanh::LeanObject,
    mut v___y_2379_: *mut leanh::LeanObject,
    mut v___y_2380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2381_ = l_Lean_ShareCommon_PShareCommonT_withShareCommon___redArg(
        v_inst_2377_,
        v___y_2379_,
        v___y_2380_,
    );
    return v___x_2381_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg(
    mut v_inst_2382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2383_ = leanh::lean_alloc_closure(
        l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2383_, 0, v_inst_2382_);
    return v___f_2383_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonT_monadShareCommon(
    mut v_m_2384_: *mut leanh::LeanObject,
    mut v_inst_2385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2386_ = leanh::lean_alloc_closure(
        l_Lean_ShareCommon_PShareCommonT_monadShareCommon___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2386_, 0, v_inst_2385_);
    return v___f_2386_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(
    mut v_x_2387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2388_ = leanh::lean_ctor_get(v_x_2387_, 0);
    leanh::lean_inc(v_fst_2388_);
    return v_fst_2388_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0___boxed(
    mut v_x_2389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2390_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___lam__0(v_x_2389_);
    leanh::lean_dec_ref(v_x_2389_);
    return v_res_2390_;
}
pub unsafe fn _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2392_ = l_Lean_ShareCommon_objectFactory;
    v___x_2393_ = l_ShareCommon_mkStateImpl(v___x_2392_);
    return v___x_2393_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_run___redArg(
    mut v_inst_2394_: *mut leanh::LeanObject,
    mut v_x_2395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2396_ = leanh::lean_ctor_get(v_inst_2394_, 0);
    leanh::lean_inc_ref(v_toApplicative_2396_);
    leanh::lean_dec_ref(v_inst_2394_);
    v_toFunctor_2397_ = leanh::lean_ctor_get(v_toApplicative_2396_, 0);
    leanh::lean_inc_ref(v_toFunctor_2397_);
    leanh::lean_dec_ref(v_toApplicative_2396_);
    v_map_2398_ = leanh::lean_ctor_get(v_toFunctor_2397_, 0);
    leanh::lean_inc(v_map_2398_);
    leanh::lean_dec_ref(v_toFunctor_2397_);
    v___f_2399_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0;
    v___x_2400_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once),
        _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1,
    );
    v___x_2401_ = leanh::lean_apply_1(v_x_2395_, v___x_2400_);
    v___x_2402_ = leanh::lean_apply_4(
        v_map_2398_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_2399_,
        v___x_2401_,
    );
    return v___x_2402_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_run(
    mut v_m_2403_: *mut leanh::LeanObject,
    mut v_00_u03b1_2404_: *mut leanh::LeanObject,
    mut v_inst_2405_: *mut leanh::LeanObject,
    mut v_x_2406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2407_ = leanh::lean_ctor_get(v_inst_2405_, 0);
    leanh::lean_inc_ref(v_toApplicative_2407_);
    leanh::lean_dec_ref(v_inst_2405_);
    v_toFunctor_2408_ = leanh::lean_ctor_get(v_toApplicative_2407_, 0);
    leanh::lean_inc_ref(v_toFunctor_2408_);
    leanh::lean_dec_ref(v_toApplicative_2407_);
    v_map_2409_ = leanh::lean_ctor_get(v_toFunctor_2408_, 0);
    leanh::lean_inc(v_map_2409_);
    leanh::lean_dec_ref(v_toFunctor_2408_);
    v___f_2410_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0;
    v___x_2411_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once),
        _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1,
    );
    v___x_2412_ = leanh::lean_apply_1(v_x_2406_, v___x_2411_);
    v___x_2413_ = leanh::lean_apply_4(
        v_map_2409_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_2410_,
        v___x_2412_,
    );
    return v___x_2413_;
}
pub unsafe fn _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2414_ = l_Lean_ShareCommon_persistentObjectFactory;
    v___x_2415_ = l_ShareCommon_mkStateImpl(v___x_2414_);
    return v___x_2415_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonT_run___redArg(
    mut v_inst_2416_: *mut leanh::LeanObject,
    mut v_x_2417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2418_ = leanh::lean_ctor_get(v_inst_2416_, 0);
    leanh::lean_inc_ref(v_toApplicative_2418_);
    leanh::lean_dec_ref(v_inst_2416_);
    v_toFunctor_2419_ = leanh::lean_ctor_get(v_toApplicative_2418_, 0);
    leanh::lean_inc_ref(v_toFunctor_2419_);
    leanh::lean_dec_ref(v_toApplicative_2418_);
    v_map_2420_ = leanh::lean_ctor_get(v_toFunctor_2419_, 0);
    leanh::lean_inc(v_map_2420_);
    leanh::lean_dec_ref(v_toFunctor_2419_);
    v___f_2421_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0;
    v___x_2422_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once),
        _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0,
    );
    v___x_2423_ = leanh::lean_apply_1(v_x_2417_, v___x_2422_);
    v___x_2424_ = leanh::lean_apply_4(
        v_map_2420_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_2421_,
        v___x_2423_,
    );
    return v___x_2424_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonT_run(
    mut v_m_2425_: *mut leanh::LeanObject,
    mut v_00_u03b1_2426_: *mut leanh::LeanObject,
    mut v_inst_2427_: *mut leanh::LeanObject,
    mut v_x_2428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2429_ = leanh::lean_ctor_get(v_inst_2427_, 0);
    leanh::lean_inc_ref(v_toApplicative_2429_);
    leanh::lean_dec_ref(v_inst_2427_);
    v_toFunctor_2430_ = leanh::lean_ctor_get(v_toApplicative_2429_, 0);
    leanh::lean_inc_ref(v_toFunctor_2430_);
    leanh::lean_dec_ref(v_toApplicative_2429_);
    v_map_2431_ = leanh::lean_ctor_get(v_toFunctor_2430_, 0);
    leanh::lean_inc(v_map_2431_);
    leanh::lean_dec_ref(v_toFunctor_2430_);
    v___f_2432_ = l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__0;
    v___x_2433_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once),
        _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0,
    );
    v___x_2434_ = leanh::lean_apply_1(v_x_2428_, v___x_2433_);
    v___x_2435_ = leanh::lean_apply_4(
        v_map_2431_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_2432_,
        v___x_2434_,
    );
    return v___x_2435_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonM_run___redArg(
    mut v_a_2436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2437_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once),
        _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1,
    );
    v___x_2438_ = leanh::lean_apply_1(v_a_2436_, v___x_2437_);
    v_fst_2439_ = leanh::lean_ctor_get(v___x_2438_, 0);
    leanh::lean_inc(v_fst_2439_);
    leanh::lean_dec_ref(v___x_2438_);
    return v_fst_2439_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonM_run(
    mut v_00_u03b1_2440_: *mut leanh::LeanObject,
    mut v_a_2441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2442_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once),
        _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1,
    );
    v___x_2443_ = leanh::lean_apply_1(v_a_2441_, v___x_2442_);
    v_fst_2444_ = leanh::lean_ctor_get(v___x_2443_, 0);
    leanh::lean_inc(v_fst_2444_);
    leanh::lean_dec_ref(v___x_2443_);
    return v_fst_2444_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonM_run___redArg(
    mut v_a_2445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once),
        _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0,
    );
    v___x_2447_ = leanh::lean_apply_1(v_a_2445_, v___x_2446_);
    v_fst_2448_ = leanh::lean_ctor_get(v___x_2447_, 0);
    leanh::lean_inc(v_fst_2448_);
    leanh::lean_dec_ref(v___x_2447_);
    return v_fst_2448_;
}
pub unsafe fn l_Lean_ShareCommon_PShareCommonM_run(
    mut v_00_u03b1_2449_: *mut leanh::LeanObject,
    mut v_a_2450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2451_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0_once),
        _init_l_Lean_ShareCommon_PShareCommonT_run___redArg___closed__0,
    );
    v___x_2452_ = leanh::lean_apply_1(v_a_2450_, v___x_2451_);
    v_fst_2453_ = leanh::lean_ctor_get(v___x_2452_, 0);
    leanh::lean_inc(v_fst_2453_);
    leanh::lean_dec_ref(v___x_2452_);
    return v_fst_2453_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(
    mut v_a_2454_: *mut leanh::LeanObject,
    mut v_a_2455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2456_ = l_Lean_ShareCommon_objectFactory;
    v___x_2457_ = lean_state_sharecommon(v___x_2456_, v_a_2455_, v_a_2454_);
    return v___x_2457_;
}
pub unsafe fn l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0(
    mut v_00_u03b1_2458_: *mut leanh::LeanObject,
    mut v_a_2459_: *mut leanh::LeanObject,
    mut v_a_2460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2461_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(v_a_2459_, v_a_2460_);
    return v___x_2461_;
}
pub unsafe fn l_Lean_ShareCommon_shareCommon___redArg(
    mut v_a_2462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2463_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1_once),
        _init_l_Lean_ShareCommon_ShareCommonT_run___redArg___closed__1,
    );
    v___x_2464_ = l_Lean_ShareCommon_ShareCommonT_withShareCommon___at___00Lean_ShareCommon_shareCommon_spec__0___redArg(v_a_2462_, v___x_2463_);
    v_fst_2465_ = leanh::lean_ctor_get(v___x_2464_, 0);
    leanh::lean_inc(v_fst_2465_);
    leanh::lean_dec_ref(v___x_2464_);
    return v_fst_2465_;
}
pub unsafe fn l_Lean_ShareCommon_shareCommon(
    mut v_00_u03b1_2466_: *mut leanh::LeanObject,
    mut v_a_2467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2468_ = l_Lean_ShareCommon_shareCommon___redArg(v_a_2467_);
    return v___x_2468_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_ShareCommon(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_ShareCommon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentHashSet(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_ShareCommon_objectFactory = _init_l_Lean_ShareCommon_objectFactory();
    leanh::lean_mark_persistent(l_Lean_ShareCommon_objectFactory);
    l_Lean_ShareCommon_persistentObjectFactory = _init_l_Lean_ShareCommon_persistentObjectFactory();
    leanh::lean_mark_persistent(l_Lean_ShareCommon_persistentObjectFactory);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_ShareCommon(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_ShareCommon(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_ShareCommon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_PersistentHashSet(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ShareCommon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_ShareCommon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_ShareCommon(builtin);
}